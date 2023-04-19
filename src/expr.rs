use prusti_rustc_interface::middle::{mir, ty};
use mir::{BasicBlock, StatementKind, TerminatorKind};
use std::fmt;
use std::path::Path;
use std::{fmt::Debug, iter::FromIterator, marker::Sized, collections::HashMap, collections::HashSet, process::Termination};
#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Const { Bool(bool), Int(u128) }

#[derive(Clone, PartialEq, Eq, Debug, Copy)]
pub struct BindVar(pub mir::Local, pub usize);

#[derive(Debug, Clone, PartialEq)]
pub enum MirExpr<'tcx> {
    Const(Const),
    Fail,
    BoundVar(BindVar),
    Rvalue(mir::Rvalue<'tcx>),
    Let(BindVar, Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Ite(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Eq(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    NotEq(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    And(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Or(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Phi(Vec<(PathConditions<'tcx>, MirExpr<'tcx>)>),
} 


#[derive(Clone, PartialEq, Debug)]
pub enum PathConditions<'tcx>{
    And(Vec<PathConditions<'tcx>>),
    Or(Vec<PathConditions<'tcx>>),
    Singleton(BranchCond<'tcx>),
}

impl <'tcx> PathConditions<'tcx> {

    pub fn no_conditions() -> Self {
        PathConditions::And(Vec::new())
    }

    pub fn unreachable() -> Self {
        PathConditions::Or(Vec::new())
    }

    pub fn conjoin_branch_cond(&mut self, cond: BranchCond<'tcx>){
        match self {
            (PathConditions::And(vec)) => {
                vec.push(PathConditions::Singleton(cond));
            },
            _ => {
                *self = PathConditions::And(vec![self.clone(), PathConditions::Singleton(cond)])
            }
        }
    }

    pub fn merge(&mut self, other: &PathConditions<'tcx>){
        match (&self, other) {
            (PathConditions::Or(vec), PathConditions::Or(other_vec)) => {
                let mut new_vec = vec.clone();
                new_vec.extend(other_vec.clone());
                *self = PathConditions::Or(new_vec);
            },
            (_, _) => {
                *self = PathConditions::Or(vec![self.clone(), other.clone()])
            }
        }
    }

    fn expr(&self) -> MirExpr<'tcx> {
        match self {
            PathConditions::And(vec) =>
                match vec.split_first() {
                    Some((bc, rest)) => {
                        rest.iter().fold(bc.expr(), |acc, p| MirExpr::And(box acc, box p.expr()))
                    },
                    None => MirExpr::Const(Const::Bool(true))
                }
            PathConditions::Or(vec) =>
                match vec.split_first() {
                    Some((bc, rest)) => {
                        rest.iter().fold(bc.expr(), |acc, p| MirExpr::And(box acc, box p.expr()))
                    },
                    None => MirExpr::Const(Const::Bool(true))
                }
            PathConditions::Singleton(bc) => bc.expr()
        }
    }
}

#[derive(Clone, PartialEq, Debug, Hash)]
pub enum BranchCond<'tcx> {
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