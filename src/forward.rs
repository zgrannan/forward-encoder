// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A MIR interpreter that translates MIR into vir_poly expressions.
//! 
#![feature(box_syntax)]

use prusti_rustc_interface::middle::{mir, ty};
use mir::{BasicBlock, StatementKind, TerminatorKind};
use std::{fmt::Debug, iter::FromIterator, marker::Sized, collections::HashMap, collections::HashSet};
use prusti_rustc_interface::dataflow::{
    Analysis, AnalysisDomain, CallReturnPlaces, 
    Engine, JoinSemiLattice, fmt::DebugWithContext
};

struct PureForwardAnalysis;

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Const { Bool(bool) }

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum MirExpr<'tcx> {
    Const(Const),
    Fail,
    Local(mir::Local),
    Rvalue(mir::Rvalue<'tcx>),
    Let(mir::Local, Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Eq(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
} 

impl Eq for MirExpr<'_> {

}

#[derive(Clone, PartialEq, Eq, Debug)]
struct State<'tcx> {
    bindings: HashMap<mir::Local, MirExpr<'tcx>>,
    branch_condition: HashSet<MirExpr<'tcx>>,
    out_branch_condition: Option<(MirExpr<'tcx>, BasicBlock, Option<BasicBlock>)>
}

impl <'tcx, C> DebugWithContext<C> for State<'tcx> {

}

impl <'tcx> JoinSemiLattice for State<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        println!("Joining {:?} and {:?}", self, other);
        let mut changed = false;
        for (k, v) in other.bindings.iter() {
            match self.bindings.get(k) {
                None => {
                    self.bindings.insert(*k, v.clone());
                    changed = true;
                },
                Some(v2) => { assert!(v == v2); }
            }
        }
        changed
    }
}

impl <'tcx> AnalysisDomain<'tcx> for PureForwardAnalysis {
    type Domain = State<'tcx>;

    const NAME: &'static str = "PureForwardAnalysis";

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        State {
            bindings: HashMap::new(),
            branch_condition: HashSet::new(),
            out_branch_condition: None
        }
    }

    fn initialize_start_block(
            &self,
            body: &mir::Body<'tcx>,
            state: &mut Self::Domain
    ) { 
    }
}

impl <'tcx> Analysis<'tcx> for PureForwardAnalysis {
    fn apply_statement_effect(
        &self,
        state: &mut Self::Domain,
        stmt: &mir::Statement<'tcx>,
        location: mir::Location
    ) {
        match &stmt.kind {
            StatementKind::Assign(box (lhs, rhs)) => {
                println!("Add binding for: {:?}", stmt);
                let lhs = lhs.as_local().unwrap();
                state.bindings.insert(
                    lhs, 
                    MirExpr::Rvalue(rhs.clone())
                );
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
                state.out_branch_condition = Some((
                    MirExpr::Eq(
                        box MirExpr::Rvalue(mir::Rvalue::Use(cond.clone())),
                        box MirExpr::Const(Const::Bool(*expected)),
                    ),
                    *target,
                    *cleanup
                ));
            },
            TerminatorKind::Resume | TerminatorKind::Return => {

            },
            other => { unimplemented!("{:?}", other) }
        }
        println!("Apply terminator for block w/ state {:?}", state);
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
        println!("EntrySet: {:?}", results);
        // if data.terminator().successors().count() == 0 {
        //     println!("EMPTY BLOCK");
        // }
    }
    MirExpr::Local(mir::Local::from_usize(0))
}

// pub trait ExprFactory<'tcx, Expr, Var> {
//     fn local(&self, local: mir::Local) -> SpannedEncodingResult<Var>;
//     fn var(&self, v: Var) -> SpannedEncodingResult<Expr>;
//     fn bin_op_expr(&self, op: mir::BinOp, left: Expr, right: Expr, ty: ty::Ty<'tcx>) -> EncodingResult<Expr>;
//     fn operand_expr(&self, operand: &mir::Operand<'tcx>) -> EncodingResult<Expr>;
//     fn let_expr(&self, binder: Var, value: Expr, body: Expr) -> Expr;
//     fn switch_int(&self, cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr;
//     fn gt(&self, lhs: Expr, rhs:Expr) -> Expr;
// }

// fn interpret_rvalue<'tcx, F, Expr, Var>(
//     operand_ty: ty::Ty<'tcx>, 
//     rvalue: &mir::Rvalue<'tcx>, 
//     interpreter: &F
// ) -> EncodingResult<Expr> where F: ExprFactory<'tcx, Expr, Var> {
//     match rvalue {
//         &mir::Rvalue::BinaryOp(op, box (ref left, ref right)) => {
//             let lhs = interpreter.operand_expr(left)?;
//             let rhs = interpreter.operand_expr(right)?;
//             interpreter.bin_op_expr(op, lhs, rhs, operand_ty)
//         },
//         &mir::Rvalue::CheckedBinaryOp(op, box (ref left, ref right)) => {
//             let lhs = interpreter.operand_expr(left)?;
//             let rhs = interpreter.operand_expr(right)?;
//             interpreter.bin_op_expr(op, lhs, rhs, operand_ty)
//         },
//         other => { 
//             unimplemented!("How to interpret {:?}", other) 
//         }
//     }
// }

// pub fn run_forward_interpreter<'tcx, F, Expr, Var>(
//     mir: &mir::Body<'tcx>,
//     interpreter: &F
// ) -> SpannedEncodingResult<Expr> 
// where 
//     F: ExprFactory<'tcx, Expr, Var>,
//     Expr: std::fmt::Debug + std::fmt::Display
// {
//     let mut cur_block = &mir.basic_blocks[mir::START_BLOCK];
//     let mut assns: Vec<(Var, Expr)> = vec![];
//     for stmt in cur_block.statements.iter() {
//         match &stmt.kind {
//             StatementKind::Assign(box (lhs, rhs)) => {
//                 let lhs = lhs.as_local().unwrap();
//                 let ty = mir.local_decls[lhs].ty;
//                 let rhs_expr = interpret_rvalue(ty, rhs, interpreter)
//                                 .map_err(|err| err.with_span(stmt.source_info.span))?;
//                 let lhs = interpreter.local(lhs)?;
//                 assns.push((lhs, rhs_expr));
//             }
//             _ => { unimplemented!() }
//         }
//     }
//     let mut result: Expr = interpreter.var(
//         interpreter.local(mir::RETURN_PLACE)?
//     )?;
//     for assn in assns {
//         result = interpreter.let_expr(assn.0, assn.1, result)
//     }
//     Ok(result)
// }