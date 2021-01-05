use crate::lexer::*;
use crate::parser::*;
pub struct Interpreter;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Num(i64),
    Bool(bool),
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter
    }

    pub fn eval(&mut self, expr: &Ast) -> Result<Type, InterpreterError> {
        use self::AstKind::*;
        match expr.value {
            Num(n) => Ok(Type::Num(n as i64)),
            Bool(b) => Ok(Type::Bool(b)),
            UniOp { ref op, ref e } => {
                let e = self.eval(e)?;
                self.eval_uniop(op, e)
                    .map_err(|e| InterpreterError::new(e, expr.loc.clone()))
            }
            //  2 + 3 evalto 5 by E-Plus {
            //    2 evalto 2 by E-Int {};
            //    3 evalto 3 by E-Int {};
            //    2 plus 3 is 5 by B-Plus {}
            //  }
            BinOp {
                ref op,
                ref l,
                ref r,
            } => {
                let l = self.eval(l)?;
                let r = self.eval(r)?;
                self.eval_binop(op, l, r)
                    .map_err(|e| InterpreterError::new(e, expr.loc.clone()))
            }
            TriOp {
                ref op,
                ref b,
                ref l,
                ref r,
            } => {
                let b = self.eval(b)?;
                let l = self.eval(l)?;
                let r = self.eval(r)?;
                self.eval_triop(op, b, l, r)
                    .map_err(|e| InterpreterError::new(e, expr.loc.clone()))
            }
        }
    }

    fn eval_uniop(&mut self, op: &UniOp, n: Type) -> Result<Type, InterpreterErrorKind> {
        use self::UniOpKind::*;
        match n {
            Type::Num(n) => match op.value {
                Plus => Ok(Type::Num(n)),
                Minus => Ok(Type::Num(-n)),
            },
            Type::Bool(_) => Err(InterpreterErrorKind::TypeError),
        }
    }

    fn eval_binop(&mut self, op: &BinOp, l: Type, r: Type) -> Result<Type, InterpreterErrorKind> {
        use self::BinOpKind::*;
        match l {
            Type::Num(l) => match r {
                Type::Num(r) => match op.value {
                    Plus => Ok(Type::Num(l + r)),
                    Minus => Ok(Type::Num(l - r)),
                    Times => Ok(Type::Num(l * r)),
                    Less => Ok(Type::Bool(l < r)),
                },
                Type::Bool(_) => Err(InterpreterErrorKind::TypeError),
            },
            Type::Bool(_) => Err(InterpreterErrorKind::TypeError),
        }
    }

    fn eval_triop(
        &mut self,
        op: &TriOp,
        b: Type,
        l: Type,
        r: Type,
    ) -> Result<Type, InterpreterErrorKind> {
        use self::TriOpKind::*;
        match b {
            Type::Bool(b) => match op.value {
                If => Ok(if b { l } else { r }),
            },
            Type::Num(_) => Err(InterpreterErrorKind::TypeError),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InterpreterErrorKind {
    DivisionByZero,
    TypeError,
}

pub type InterpreterError = Annot<InterpreterErrorKind>;
