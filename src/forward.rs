use prusti_rustc_interface::middle::{mir, ty};
use mir::{BasicBlock, StatementKind, TerminatorKind};
use std::fmt;
use std::{fmt::Debug, collections::HashMap, collections::HashSet};
use prusti_rustc_interface::dataflow::{
    Analysis, AnalysisDomain, CallReturnPlaces, 
    Engine, JoinSemiLattice, fmt::DebugWithContext
};
use crate::expr::*;
use crate::ssa::*;

struct PureForwardAnalysis(SsaAnalysis);

impl PureForwardAnalysis {

    fn get_ssa_version(&self, location: mir::Location, local: mir::Local) -> usize {
        self.0.version.get(&(location, local)).unwrap().clone()
    }

    fn apply_first(&self, state: &mut State, location: mir::Location) {
        if location.statement_index == 0 {
            assert!(state.block.is_none());
            state.block = Some(location.block);
            for (block, other) in state.incoming_data.iter() {
                if !state.imaginary_edges.contains(&(*block, location.block)) {
                    eprintln!("Merge {:?} into {:?}", block, location.block);
                    state.path_conditions.merge(&other.path_conditions);
                    state.bindings.merge(&other.bindings);
                }
            }
            for phi in self.0.phi.get(&location.block).unwrap_or(&vec![]).iter() {
                eprintln!("PHI: {phi:?}");
                let new_var = BindVar(phi.local, phi.new_version);
                if(state.bindings.contains(new_var)){
                    continue;
                }
                let mut phi_parts = vec![];
                for (block, version) in phi.sources.iter() {
                    let incoming_path_conditions = state.incoming_data.get(block).unwrap().path_conditions.clone();
                    phi_parts.push((
                        incoming_path_conditions,
                        MirExpr::BoundVar(BindVar(phi.local, *version))
                    ));
                }
                state.bindings.insert((new_var, MirExpr::Phi(phi_parts)));
            }
            match state.branch_cond_to.get(&location.block) {
                Some(cond) => {
                    // eprintln!("Inheriting branch condition: {:?}", cond);
                    state.insert_branch_condition(cond.clone());
                },
                None => {}
            }
        }
    }

}
impl<'tcx> fmt::Display for MirExpr<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MirExpr::Fail => write!(f, "fail"),
            MirExpr::BoundVar(l) => write!(f, "{:?}", l),
            MirExpr::Rvalue(r) => write!(f, "{:?}", r),
            MirExpr::Let(l, a, b) => write!(f, "let {:?} = {} in\n{}", l, a, b),
            MirExpr::Ite(c, t, e) => write!(f, "if {} then {} else {}", c, t, e),
            MirExpr::Eq(a, b) => write!(f, "{} == {}", a, b),
            MirExpr::NotEq(a, b) => write!(f, "{} != {}", a, b),
            MirExpr::And(a, b) => write!(f, "{} && {}", a, b),
            MirExpr::Or(a, b) => write!(f, "{} || {}", a, b),
            MirExpr::Phi(pos) => { write!(f, "phi(\n ")?;
                for (cond, expr) in pos {
                    write!(f, "{:?} => {},\n ", cond, expr)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Eq for MirExpr<'_> {

}

type Binding<'tcx> = (BindVar, MirExpr<'tcx>);

#[derive(Clone, PartialEq, Eq, Debug)]
struct Bindings<'tcx>(Vec<Binding<'tcx>>);


impl <'tcx> Bindings<'tcx> {
    fn new() -> Self {
        Bindings(vec![])
    }

    // TODO
    // fn subst_expr(&self, expr: MirExpr<'tcx>) -> MirExpr<'tcx> {
    //     match expr {
    //         MirExpr::Phi(vec) => {
    //             let mut expr = MirExpr::Fail;
    //             for (cond, rhs) in vec.iter() {
    //                 let cond_expr = cond.expr();
    //                 expr = MirExpr::Ite(
    //                     box self.subst_expr(cond_expr), 
    //                     box self.subst_expr(rhs.clone()), 
    //                     box expr
    //                 );
    //             }
    //             expr
    //         },
    //         MirExpr::Eq(a, b) => MirExpr::Eq(
    //             box self.subst_expr(*a), 
    //             box self.subst_expr(*b)
    //         ),
    //         MirExpr::Operand(o) => {
    //             match o {
    //                 Operand::Place()
    //             }
    //         }
    //         _ => unimplemented!()
    //     }
    // }

    fn lookup(&self, var: BindVar) -> Option<MirExpr<'tcx>> {
        self.0.iter().find(|b| b.0 == var).map(|b| b.1.clone())
    }
    fn contains(&self, var: BindVar) -> bool {
        self.lookup(var).is_some()
    }

    fn insert(&mut self, binding: Binding<'tcx>) {
        assert!(
            self.lookup(binding.0).is_none(),
            "Cannot insert {:?}: Binding already exists: {:?}",
            binding,
            self.lookup(binding.0).unwrap(),
        );
        self.0.push(binding);
    }


    fn merge(&mut self, 
        other_bindings: &Bindings<'tcx>,
    ) {
        for binding in other_bindings.0.iter() {
            if self.lookup(binding.0).is_none() {
                self.insert(binding.clone());
            }
        }
    }
}


#[derive(Clone, PartialEq, Debug)]
struct State<'tcx> {

    imaginary_edges: HashSet<(BasicBlock, BasicBlock)>,
    incoming_data: HashMap<BasicBlock, State<'tcx>>,
    block: Option<BasicBlock>,

    bindings: Bindings<'tcx>,
    path_conditions: PathConditions<'tcx>,

    // The set of all known branch conditions that lead into a basic block
    // We only use this to inherit parent branch conditions, since we can't access this directly 
    branch_cond_to: HashMap<BasicBlock, BranchCond<'tcx>>,

    unreachable_blocks: HashSet<BasicBlock>
}

impl <'tcx> Eq for State<'tcx> {

}

impl <'tcx> State<'tcx> {
    fn new() -> Self {
        State {
            imaginary_edges: HashSet::new(),
            incoming_data: HashMap::new(),
            block: None,

            bindings: Bindings::new(),
            path_conditions: PathConditions::unreachable(),
            branch_cond_to: HashMap::new(),
            unreachable_blocks: HashSet::new(),
        }
    }

    fn insert_binding(&mut self, binding: Binding<'tcx>) {
        self.bindings.insert(binding);
    }

    fn insert_branch_condition(&mut self, cond: BranchCond<'tcx>) {
        self.path_conditions.conjoin_branch_cond(cond);
    }

    fn compute_expr(&self, version: usize) -> MirExpr<'tcx> {
        let mut expr = MirExpr::BoundVar(
            BindVar(mir::Local::from_usize(0), version)
        );
        let bindings = &self.bindings;
        for binding in bindings.0.iter().rev() {
            expr = MirExpr::Let(
                binding.0,
                box binding.1.clone(),
                box expr
            );
        }
        expr
    }


}

impl <'tcx, C> DebugWithContext<C> for State<'tcx> {

}

impl <'tcx> JoinSemiLattice for State<'tcx> {
    fn join(&mut self, other: &Self) -> bool {

        self.imaginary_edges.extend(other.imaginary_edges.iter());
        self.branch_cond_to.extend(other.branch_cond_to.clone().into_iter());
        self.unreachable_blocks.extend(other.unreachable_blocks.iter());

        self.incoming_data.insert(
            other.block.unwrap(), other.clone()
        );

        true
    }
}

impl <'tcx> AnalysisDomain<'tcx> for PureForwardAnalysis {
    type Domain = State<'tcx>;

    const NAME: &'static str = "PureForwardAnalysis";

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        State::new()
    }

    fn initialize_start_block(
            &self,
            body: &mir::Body<'tcx>,
            state: &mut Self::Domain
    ) { 
        state.path_conditions = PathConditions::no_conditions();
    }
}

impl <'tcx> Analysis<'tcx> for PureForwardAnalysis {
    fn apply_before_terminator_effect(
        &self,
        state: &mut Self::Domain,
        _terminator: &mir::Terminator<'tcx>,
        location: mir::Location
    ) {
        self.apply_first(state, location);
    }
    fn apply_before_statement_effect(
        &self,
        state: &mut Self::Domain,
        _stmt: &mir::Statement<'tcx>,
        location: mir::Location
    ) {
        self.apply_first(state, location);
    }
    fn apply_statement_effect(
        &self,
        state: &mut Self::Domain,
        stmt: &mir::Statement<'tcx>,
        location: mir::Location
    ) {
        match &stmt.kind {
            StatementKind::Assign(box (lhs, rhs)) => {
                // println!("Add binding for: {:?}", stmt);
                let lhs = lhs.as_local().unwrap();
                let ssa_version = self.get_ssa_version(location, lhs);
                println!("SSAVersion {:?} {:?}: {}", location, lhs, ssa_version);
                let rhs = MirExpr::Rvalue(
                    Rvalue::from_mir(
                        rhs,
                        &|local| self.get_ssa_version(location, local)
                    )
                );
                state.insert_binding((BindVar(lhs, ssa_version), rhs));
            }
            StatementKind::StorageDead(_) => {},
            StatementKind::StorageLive(_) => {},
            StatementKind::FakeRead(_) => {},
            other => { unimplemented!("{:?}", other) }
        }
    }
    fn apply_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &mir::terminator::Terminator<'tcx>,
        location: mir::Location
    ) {
        match &terminator.kind {
            TerminatorKind::Assert { cond, expected, msg, target, cleanup } => {
                match cleanup {
                    Some(bb) => { state.unreachable_blocks.insert(bb.clone()); },
                    _ => {}
                }
            },
            TerminatorKind::FalseEdge {real_target, imaginary_target} => {
                state.imaginary_edges.insert((state.block.unwrap(), imaginary_target.clone()));

            },
            TerminatorKind::Unreachable {} => {
                state.unreachable_blocks.insert(location.block); 
            },
            TerminatorKind::Goto { target } => {
                // state.branch = Some((
                //     MirExpr::Const(Const::Bool(true)),
                //     *target,
                //     None
                // ));
            },
            TerminatorKind::Resume | TerminatorKind::Return => {

            },
            TerminatorKind::SwitchInt { discr, targets } => {
                let mir_place = discr.place().unwrap();
                let place = Place::from_mir(mir_place, |local| {
                    self.0.version.get(&(location, local)).unwrap().clone()
                });
                let mut non_values = vec![];
                for (value, bb) in targets.iter() {
                    eprintln!("SwitchInt: {:?} = {:?} -> {:?}", discr, value, bb);
                    non_values.push(value);
                    state.branch_cond_to.insert(
                        bb, 
                        BranchCond::Equals(place.clone(), value)
                    );
                }
                state.branch_cond_to.insert(
                    targets.otherwise(),
                    BranchCond::Other(place.clone(), non_values)
                );
            }
            other => { unimplemented!("{:?}", other) }
        }
        // println!("Apply terminator for block w/ state {:?}", state);
    }
    fn apply_call_return_effect(
        &self,
        state: &mut Self::Domain,
        block: mir::BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>
    ) {
        unimplemented!()
    }
}

pub fn run_forward<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    mir: &mir::Body<'tcx>
) -> MirExpr<'tcx> {
    let mut ssa = SsaVisitor::new(mir.local_decls.len());
    ssa.analyse(mir);
    let analysis = PureForwardAnalysis(ssa.analysis);
    let engine = Engine::new_generic(
        tcx,
        mir,
        analysis
    );
    let results = engine.iterate_to_fixpoint();
    let mut cursor = results.into_results_cursor(mir);
    for (bb, data) in mir.basic_blocks.iter_enumerated() {
        cursor.seek_to_block_end(bb);
        let results = cursor.get();
        if data.terminator().successors().count() == 0 && 
           !results.unreachable_blocks.contains(&bb) {
            let result = results.compute_expr(4);
            println!("Terminal block {:?}: {}", bb, result);
            return result;
        }
    }
    unreachable!();
}