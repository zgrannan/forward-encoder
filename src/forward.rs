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

#[derive(Debug, Clone, PartialEq)]
pub enum MirExpr<'tcx> {
    Const(Const),
    Fail,
    Local(mir::Local),
    Rvalue(mir::Rvalue<'tcx>),
    Let(mir::Local, Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Ite(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Eq(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    NotEq(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    And(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Phi(Vec<(BranchConditions<'tcx>, MirExpr<'tcx>)>),
} 

impl<'tcx> MirExpr<'tcx> {
    fn join (&self, 
        other: &MirExpr<'tcx>, 
        branch_conditions: &BranchConditions<'tcx>, 
        other_branch_conditions: &BranchConditions<'tcx>
    ) -> MirExpr<'tcx> {
        if self == other {
            return self.clone();
        } else {
            let disjoint = branch_conditions.compute_disjoint(other_branch_conditions);
            if disjoint.covers_all_cases() {
                MirExpr::Ite(
                    Box::new(disjoint.left_condition()),
                    Box::new(self.clone()),
                    Box::new(other.clone())
                )
            } else {
                let mut phi = Vec::new();
                phi.push(
                    (disjoint.0, self.clone())
                );
                phi.push((disjoint.1, other.clone()));
                return MirExpr::Phi(phi);
            }
        }
    }
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
            MirExpr::NotEq(a, b) => write!(f, "{} != {}", a, b),
            MirExpr::And(a, b) => write!(f, "{} && {}", a, b),
            MirExpr::Phi(pos) => { write!(f, "phi(")?;
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

type Binding<'tcx> = (mir::Local, MirExpr<'tcx>);

#[derive(Clone, PartialEq, Eq, Debug)]
struct Bindings<'tcx>(Vec<Binding<'tcx>>);

impl <'tcx> Bindings<'tcx> {
    fn new() -> Self {
        Bindings(vec![])
    }

    fn lookup(&self, local: mir::Local) -> Option<MirExpr<'tcx>> {
        self.0.iter().find(|b| b.0 == local).map(|b| b.1.clone())
    }

    fn update(&mut self, local: mir::Local, expr: MirExpr<'tcx>) {
        self.0.iter_mut().find(|b| b.0 == local).map(|b| b.1 = expr);
    }


    fn insert(&mut self, binding: Binding<'tcx>) {
        assert!(self.lookup(binding.0).is_none());
        self.0.push(binding);
    }


    fn merge(&mut self, 
        other_bindings: &Bindings<'tcx>,
        branch_conditions: &BranchConditions<'tcx>,
        other_branch_conditions: &BranchConditions<'tcx>
    ) {
        for binding in other_bindings.0.iter() {
            match self.lookup(binding.0) {
                Some(our_expr) => { 
                    let joined_expr = our_expr.join(&binding.1, branch_conditions, other_branch_conditions);
                    self.update(binding.0, joined_expr);
                },
                None => self.insert(binding.clone()),
            }
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
struct BranchConditions<'tcx>(HashSet<BranchCond<'tcx>>);

impl <'tcx> BranchConditions<'tcx> {
    fn expr(&self) -> MirExpr<'tcx> {
        let mut it = self.conditions();
        let mut result = match it.next() {
            Some(e) => e.expr(),
            None => return MirExpr::Const(Const::Bool(true))
        };
        while let Some(e) = it.next() {
            result = MirExpr::And(Box::new(result), Box::new(e.expr()));
        }
        return result;
    }
    fn conditions(&self) -> impl Iterator<Item = &BranchCond<'tcx>> {
        self.0.iter()
    }
    fn operands(&self) -> impl Iterator<Item = &mir::Operand<'tcx>> {
        self.0.iter().map(|c| c.get_operand())
    }
}

#[derive(Clone, PartialEq, Debug)]
struct DisjointConditions<'tcx>(BranchConditions<'tcx>, BranchConditions<'tcx>);

impl <'tcx> DisjointConditions<'tcx> {
    fn all_conditions(&self) -> impl Iterator<Item = BranchCond<'tcx>> {
        let mut base = self.0.0.clone();
        base.extend(self.1.0.clone().into_iter());
        base.into_iter()
    }

    fn left_condition(&self) -> MirExpr<'tcx> {
        self.0.expr()
    }

    fn covers_all_cases(&self) -> bool {
        let base_operand = self.0.operands().next().unwrap();
        if(self.all_conditions().all(|e| e.get_operand() == base_operand)) {
            let mut seen_values: HashSet<u128> = HashSet::new();
            let mut other: Option<HashSet<u128>> = None;
            for condition in self.all_conditions() {
                match condition {
                    BranchCond::Equals(_, v) => { seen_values.insert(v); },
                    BranchCond::Other(_, v) => other = Some(
                        HashSet::from_iter(v.into_iter())
                    )
                }
            }
            other == Some(seen_values)
        } else {
            false
        }
    }
}

impl <'tcx> BranchConditions <'tcx>{
    fn new() -> Self {
        BranchConditions(HashSet::new())
    }

    fn merge(&mut self, other: &Self) {
        self.0.extend(other.0.clone().into_iter());
    }

    fn compute_disjoint(&self, other: &Self) -> DisjointConditions<'tcx> {
        let mut ours_missing = BranchConditions::new();
        let mut their_missing = BranchConditions::new();

        for ours in self.0.iter() {
            if !other.0.contains(ours) {
                ours_missing.insert(ours.clone());
            }
        }

        for theirs in other.0.iter() {
            if !self.0.contains(theirs) {
                their_missing.insert(theirs.clone());
            }
        }

        eprintln!("Disjoint of: {:?} \nand{:?}\n", self, other);
        eprintln!("is: {:?} and {:?}\n\n", ours_missing, their_missing);

        return DisjointConditions(ours_missing, their_missing);
    }

    fn insert(&mut self, cond: BranchCond<'tcx>) {
        self.0.insert(cond);
    }
}

#[derive(Clone, PartialEq, Debug, Hash)]
enum BranchCond<'tcx> {
    Equals(mir::Operand<'tcx>, u128),
    Other(mir::Operand<'tcx>, Vec<u128>),
}

impl <'tcx> BranchCond<'tcx> {
    fn expr(&self) -> MirExpr<'tcx> {
        match self {
            BranchCond::Equals(op, v) => MirExpr::Eq(
                Box::new(MirExpr::Rvalue(mir::Rvalue::Use(op.clone()))),
                Box::new(MirExpr::Const(Const::Int(*v)))
            ),
            BranchCond::Other(op, v) if v.len() == 1 => MirExpr::NotEq(
                Box::new(MirExpr::Rvalue(mir::Rvalue::Use(op.clone()))),
                Box::new(MirExpr::Const(Const::Int(v.last().unwrap().clone())))
            ),
            _ => unimplemented!()

        }
    }
    fn get_operand(&self) -> &mir::Operand<'tcx> {
        match self {
            BranchCond::Equals(op, _) => op,
            BranchCond::Other(op, _) => op,
        }
    }
}

impl <'tcx> Eq for BranchCond<'tcx> {

}

#[derive(Clone, PartialEq, Debug)]
struct State<'tcx> {
    bindings: Bindings<'tcx>,
    branch_conditions: BranchConditions<'tcx>,

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
            bindings: Bindings::new(),
            branch_conditions: BranchConditions::new(),
            branch_cond_to: HashMap::new(),
            unreachable_blocks: HashSet::new(),
        }
    }

    fn insert_binding(&mut self, binding: Binding<'tcx>) {
        self.bindings.insert(binding);
    }

    fn insert_branch_condition(&mut self, cond: BranchCond<'tcx>) {
        self.branch_conditions.insert(cond);
    }

    fn compute_expr(&self) -> MirExpr<'tcx> {
        let mut expr = MirExpr::Local(mir::Local::from_usize(0));
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
        self.bindings.merge(
            &other.bindings, 
            &self.branch_conditions, 
            &other.branch_conditions
        );
        self.branch_conditions.merge(&other.branch_conditions);
        self.unreachable_blocks.extend(other.unreachable_blocks.iter());
        self.branch_cond_to.extend(other.branch_cond_to.clone().into_iter());
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
    }
}

impl <'tcx> Analysis<'tcx> for PureForwardAnalysis {
    fn apply_before_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &mir::Terminator<'tcx>,
        location: mir::Location
    ) {
        if location.statement_index == 0 {
            // eprintln!("Before terminator for no statements: {:?}", location.block);
            if location.statement_index == 0 {
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
    fn apply_before_statement_effect(
        &self,
        state: &mut Self::Domain,
        stmt: &mir::Statement<'tcx>,
        location: mir::Location
    ) {
        // eprintln!("Before stmt: {:?}", location.block);
        if location.statement_index == 0 {
            match state.branch_cond_to.get(&location.block) {
                Some(cond) => {
                    // eprintln!("Inheriting branch condition: {:?}", cond);
                    state.insert_branch_condition(cond.clone());
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
                state.insert_binding((lhs, MirExpr::Rvalue(rhs.clone())));
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
                state.unreachable_blocks.insert(imaginary_target.clone());
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
                let mut non_values = vec![];
                for (value, bb) in targets.iter() {
                    eprintln!("SwitchInt: {:?} = {:?} -> {:?}", discr, value, bb);
                    non_values.push(value);
                    state.branch_cond_to.insert(
                        bb, 
                        BranchCond::Equals(discr.clone(), value)
                    );
                }
                state.branch_cond_to.insert(
                    targets.otherwise(),
                    BranchCond::Other(discr.clone(), non_values)
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