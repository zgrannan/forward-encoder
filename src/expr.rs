use prusti_rustc_interface::middle::{mir, ty};
use mir::{BasicBlock, StatementKind, TerminatorKind};
use std::mem;
use std::{fmt::Debug, iter::FromIterator, marker::Sized, collections::HashMap, collections::HashSet, process::Termination};

#[derive(Clone, PartialEq, Eq, Debug, Copy, Hash)]
pub struct BindVar(pub mir::Local, pub usize);


#[derive(Debug, Clone, PartialEq, Hash, Copy)]
pub enum Place<'tcx> {
    SSAPlace(BindVar),
    FieldPlace(mir::Place<'tcx>)
}

impl <'tcx> Place<'tcx> {
    pub fn from_mir<F>(place: mir::Place<'tcx>, f: F) -> Place<'tcx> 
      where F : Fn(mir::Local) -> usize {
        match place.as_local() {
            Some(local) =>  {
                let version = f(local);
                Place::SSAPlace(BindVar(local, version))
            },
            _ => Place::FieldPlace(place.clone())
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Const<'tcx> {
    Bool(bool),
    Int(u128),
    RustConst(mir::Constant<'tcx>)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operand<'tcx> {
    Place(Place<'tcx>),
    Const(Const<'tcx>)
}

impl <'tcx> From<bool> for Operand<'tcx> {
    fn from(b: bool) -> Self {
        Operand::Const(Const::Bool(b))
    }
}

impl <'tcx> From<u128> for Operand<'tcx> {
    fn from(b: u128) -> Self {
        Operand::Const(Const::Int(b))
    }
}

impl <'tcx> From<mir::Constant<'tcx>> for Operand<'tcx> {
    fn from(c: mir::Constant<'tcx>) -> Self {
        Operand::Const(Const::RustConst(c))
    }
}

impl <'tcx> From<Place<'tcx>> for Operand<'tcx> {
    fn from(c: Place<'tcx>) -> Self {
        Operand::Place(c)
    }
}

impl <'tcx> Operand<'tcx> {
    pub fn from_mir<F>(operand: mir::Operand<'tcx>, f: F) -> Operand<'tcx> 
      where F : Fn(mir::Local) -> usize {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                Operand::Place(Place::from_mir(place, f))
            },
            mir::Operand::Constant(box constant) => {
                constant.into()
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Rvalue<'tcx> {
    Use(Operand<'tcx>),
    BinaryOp(mir::BinOp, Place<'tcx>, Operand<'tcx>),
    UnaryOp(mir::UnOp, Place<'tcx>),
    Discriminant(Place<'tcx>),
    Cast(mir::CastKind, Place<'tcx>, ty::Ty<'tcx>),
}

impl <'tcx> From<bool> for Rvalue<'tcx> {
    fn from(b: bool) -> Self {
        Rvalue::Use(Operand::from(b))
    }
}

impl <'tcx> From<u128> for Rvalue<'tcx> {
    fn from(b: u128) -> Self {
        Rvalue::Use(Operand::from(b))
    }
}

impl <'tcx> From<Place<'tcx>> for Rvalue<'tcx> {
    fn from(b: Place<'tcx>) -> Self {
        Rvalue::Use(Operand::from(b))
    }
}

impl <'tcx> Rvalue<'tcx> {
    pub fn from_mir<F>(expr: &mir::Rvalue<'tcx>, f: &F) -> Rvalue<'tcx> 
      where F : Fn(mir::Local) -> usize {
        match expr {
            mir::Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                Rvalue::BinaryOp(*op, 
                    Place::from_mir(lhs.place().unwrap(), f), 
                    Operand::from_mir(rhs.clone(), f)
                )
            },
            mir::Rvalue::UnaryOp(op, operand) => {
                Rvalue::UnaryOp(*op, 
                    Place::from_mir(operand.place().unwrap(), f)
                )
            },
            mir::Rvalue::Use(op) => {
                Rvalue::Use(Operand::from_mir(op.clone(), f))
            },
            mir::Rvalue::Discriminant(place) => {
                Rvalue::Discriminant(Place::from_mir(place.clone(), f))
            },
            mir::Rvalue::Cast(kind, op, ty) => {
                Rvalue::Cast(kind.clone(), Place::from_mir(op.place().unwrap(), f), ty.clone())
            },
            _ => unimplemented!("{:?} not implemented (disc: {:?})", expr, mem::discriminant(expr))
        }

    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum MirExpr<'tcx> {
    Fail,
    BoundVar(BindVar),
    Rvalue(Rvalue<'tcx>),
    Let(BindVar, Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Ite(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Eq(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    NotEq(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    And(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Or(Box<MirExpr<'tcx>>, Box<MirExpr<'tcx>>),
    Phi(Vec<(PathConditions<'tcx>, MirExpr<'tcx>)>),
} 

impl <'tcx> From<bool> for MirExpr<'tcx> {
    fn from(b: bool) -> Self {
        MirExpr::Rvalue(Rvalue::from(b))
    }
}

impl <'tcx> From<u128> for MirExpr<'tcx> {
    fn from(c: u128) -> Self {
        MirExpr::Rvalue(Rvalue::from(c))
    }
}

impl <'tcx> From<Place<'tcx>> for MirExpr<'tcx> {
    fn from(c: Place<'tcx>) -> Self {
        MirExpr::Rvalue(Rvalue::from(c))
    }
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
            PathConditions::And(vec) if vec.len() == 0 => {
                *self = PathConditions::Singleton(cond)
            },
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
            (PathConditions::Or(vec), p) if vec.len() == 0 => {
                *self = p.clone()
            },
            (PathConditions::Or(vec), p) => {
                let mut new_vec = vec.clone();
                new_vec.push(p.clone());
                *self = PathConditions::Or(new_vec);
            },
            (_, _) => {
                *self = PathConditions::Or(vec![self.clone(), other.clone()])
            }
        }
    }

    pub fn expr(&self) -> MirExpr<'tcx> {
        match self {
            PathConditions::And(vec) =>
                match vec.split_first() {
                    Some((bc, rest)) => {
                        rest.iter().fold(bc.expr(), |acc, p| MirExpr::And(box acc, box p.expr()))
                    },
                    None => true.into()
                }
            PathConditions::Or(vec) =>
                match vec.split_first() {
                    Some((bc, rest)) => {
                        rest.iter().fold(bc.expr(), |acc, p| MirExpr::Or(box acc, box p.expr()))
                    },
                    None => false.into()
                }
            PathConditions::Singleton(bc) => bc.expr()
        }
    }
}

#[derive(Clone, PartialEq, Debug, Hash)]
pub enum BranchCond<'tcx> {
    Equals(Place<'tcx>, u128),
    Other(Place<'tcx>, Vec<u128>),
}

impl <'tcx> BranchCond<'tcx> {
    fn expr(&self) -> MirExpr<'tcx> {
        match self {
            BranchCond::Equals(op, v) => MirExpr::Eq(
                Box::new((*op).into()),
                Box::new((*v).into())
            ),
            BranchCond::Other(op, v) if v.len() == 1 => MirExpr::NotEq(
                Box::new((*op).into()),
                Box::new(v[0].into())
            ),
            _ => unimplemented!()

        }
    }
    fn get_operand(&self) -> &Place<'tcx> {
        match self {
            BranchCond::Equals(op, _) => op,
            BranchCond::Other(op, _) => op,
        }
    }
}

impl <'tcx> Eq for BranchCond<'tcx> {

}