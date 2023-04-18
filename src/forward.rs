use prusti_rustc_interface::middle::{mir, ty};
use mir::{BasicBlock, StatementKind, TerminatorKind};
use std::fmt;
use std::{fmt::Debug, iter::FromIterator, marker::Sized, collections::HashMap, collections::HashSet, process::Termination};
use prusti_rustc_interface::dataflow::{
    Analysis, AnalysisDomain, CallReturnPlaces, 
    Engine, JoinSemiLattice, fmt::DebugWithContext
};

struct PureForwardAnalysis;

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Const { Bool(bool), Int(u128) }

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum MirExpr<'tcx> {
    Const(Const),
    Fail,
    Local(mir::Local),
    Rvalue(mir::Rvalue<'tcx>),
    Let(mir::Local, Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Ite(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Eq(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
} 

impl<'tcx> fmt::Display for MirExpr<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MirExpr::Const(c) => write!(f, "{:?}", c),
            MirExpr::Fail => write!(f, "fail"),
            MirExpr::Local(l) => write!(f, "{:?}", l),
            MirExpr::Rvalue(r) => write!(f, "{:?}", r),
            MirExpr::Let(l, a, b) => write!(f, "let {:?} = {} in\n{}", l, a, b),
            MirExpr::Ite(c, t, e) => write!(f, "if {} then {} else {}", c, t, e),
            MirExpr::Eq(a, b) => write!(f, "{} == {}", a, b),
        }
    }
}

impl Eq for MirExpr<'_> {

}

type Binding<'tcx> = (mir::Local, MirExpr<'tcx>);

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
struct Bindings<'tcx>(Vec<Binding<'tcx>>);

impl <'tcx> Bindings<'tcx> {
    fn new() -> Self {
        Bindings(Vec::new())
    }

    fn push(&mut self, binding: Binding<'tcx>) {
        self.0.push(binding);
    }

    fn lookup(&self, local: mir::Local) -> Option<&MirExpr<'tcx>> {
        self.0.iter().find(|(l, _)| *l == local).map(|(_, e)| e)
    }

    fn append(&mut self, other: Bindings<'tcx>) {
        self.0.extend(other.0.into_iter());
    }
}


#[derive(Clone, PartialEq, Eq, Debug, Hash)]
struct BranchCond<'tcx>(MirExpr<'tcx>, bool);

impl <'tcx> BranchCond<'tcx> {
    fn always() -> BranchCond<'tcx> {
        BranchCond(MirExpr::Const(Const::Bool(true)), true)
    }
    fn is_opposite(&self, other: &BranchCond<'tcx>) -> bool {
        self.0 == other.0 && self.1 != other.1
    }

    fn to_expr(&self, ours: &MirExpr<'tcx>, theirs: &MirExpr<'tcx>) -> MirExpr<'tcx> {
        let (thn, els) = if self.1 { 
            (ours, theirs)
        } else { 
            (theirs, ours)
        };
        MirExpr::Ite(
            Box::new(self.0.clone()),
            Box::new(thn.clone()),
            Box::new(els.clone())
        )
    }

    fn join_bindings(&self, 
        our_bindings: &Bindings<'tcx>, 
        their_bindings: &Bindings<'tcx>
    ) -> Bindings<'tcx> {
        let mut bindings = Bindings::new();
        for binding in &our_bindings.0 {
            match their_bindings.lookup(binding.0) {
                Some(their_expr) => {
                    bindings.push((
                        binding.0,
                         self.to_expr(&binding.1, their_expr)
                        )
                    )
                },
                None => {
                    bindings.push(binding.clone())
                }
            }
        }
        for binding in &their_bindings.0 {
            if our_bindings.lookup(binding.0).is_none() {
                bindings.push(binding.clone())
            }
        }
        bindings
    }

}


#[derive(Clone, PartialEq, Eq, Debug)]
struct State<'tcx> {
    bindings: Vec<(BranchCond<'tcx>, Bindings<'tcx>)>,

    // The set of all known branch conditions that lead into a basic block
    // We only use this to inheret parent branch conditions, since we can't access this directly 
    branch_conditions: HashMap<BasicBlock, BranchCond<'tcx>>,

    unreachable_blocks: HashSet<BasicBlock>
}

impl <'tcx> State<'tcx> {
    fn new() -> Self {
        State {
            bindings: Vec::new(),
            branch_conditions: HashMap::new(),
            unreachable_blocks: HashSet::new()
        }
    }

    fn branch_condition(&self) -> &BranchCond<'tcx> {
        &self.bindings.last().unwrap().0
    }

    fn is_bottom(&self) -> bool {
        self.bindings.is_empty()
    }

    fn push_binding(&mut self, binding: Binding<'tcx>) {
        let mut top_bindings = self.pop_top_bindings();
        top_bindings.1.push(binding);
        self.bindings.push((top_bindings));
    }

    fn append_top_bindings(&mut self, bindings: Bindings<'tcx>) {
        let mut top_bindings = self.pop_top_bindings();
        top_bindings.1.append(bindings);
        self.bindings.push((top_bindings));
    }

    fn pop_top_bindings(&mut self) -> (BranchCond<'tcx>, Bindings<'tcx>) {
        self.bindings.pop().unwrap()
    }

    fn peek_top_bindings(&self) -> &(BranchCond<'tcx>, Bindings<'tcx>) {
        self.bindings.last().unwrap()
    }

    fn compute_expr(&self) -> MirExpr<'tcx> {
        assert!(self.bindings.len() == 1);
        let mut expr = MirExpr::Local(mir::Local::from_usize(0));
        let bindings = self.peek_top_bindings();
        for binding in bindings.1.0.iter().rev() {
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
        if self.is_bottom() {
            self.bindings = other.bindings.clone();
            self.branch_conditions = other.branch_conditions.clone();
            self.unreachable_blocks = other.unreachable_blocks.clone();
            return true;
        }
        assert!(self.branch_condition().is_opposite(other.branch_condition()));
        let top_bindings = self.pop_top_bindings();
        let their_top_bindings = other.peek_top_bindings();
        // println!("Joining {:?} and {:?}", top_bindings, their_top_bindings);
        let new_top_bindings = 
            top_bindings.0.join_bindings(&top_bindings.1, &their_top_bindings.1);
        self.append_top_bindings(new_top_bindings);
        self.unreachable_blocks.extend(other.unreachable_blocks.iter());
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
        state.bindings = vec![(BranchCond::always(), Bindings::new())]
    }
}

impl <'tcx> Analysis<'tcx> for PureForwardAnalysis {
    fn apply_before_statement_effect(
        &self,
        state: &mut Self::Domain,
        stmt: &mir::Statement<'tcx>,
        location: mir::Location
    ) {
        if location.statement_index == 0 {
            match state.branch_conditions.get(&location.block) {
                Some(cond) => {
                    state.bindings.push((cond.clone(), Bindings::new()));
                },
                None => {}
            }
        }
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
                state.push_binding((lhs, MirExpr::Rvalue(rhs.clone())));
            }
            StatementKind::StorageDead(_) => {},
            StatementKind::StorageLive(_) => {},
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
                assert!(targets.all_targets().len() == 2);
                for (value, bb) in targets.iter() {
                    let cond = MirExpr::Eq(
                        box MirExpr::Rvalue(mir::Rvalue::Use(discr.clone())),
                        box MirExpr::Const(Const::Int(value))
                    );
                    state.branch_conditions.insert(
                        bb, 
                        BranchCond(cond.clone(), true)
                    );
                    state.branch_conditions.insert(
                        targets.otherwise(),
                        BranchCond(cond , false)
                    );
                }
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
    let analysis = PureForwardAnalysis;
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
            println!("Terminal block {:?}: {}", bb, results.compute_expr());
        }
    }
    MirExpr::Local(mir::Local::from_usize(0))
}