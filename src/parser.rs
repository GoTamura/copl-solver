use crate::lexer::*;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AstKind {
    Num(u64),
    Bool(bool),
    UniOp {
        op: UniOp,
        e: Box<Ast>,
    },
    BinOp {
        op: BinOp,
        l: Box<Ast>,
        r: Box<Ast>,
    },
    TriOp {
        op: TriOp,
        b: Box<Ast>,
        l: Box<Ast>,
        r: Box<Ast>,
    },
}

impl Ast {
    fn num(n: u64, loc: Loc) -> Self {
        Self::new(AstKind::Num(n), loc)
    }

    fn bool_(n: bool, loc: Loc) -> Self {
        Self::new(AstKind::Bool(n), loc)
    }

    fn uniop(op: UniOp, e: Ast, loc: Loc) -> Self {
        Self::new(AstKind::UniOp { op, e: Box::new(e) }, loc)
    }

    fn binop(op: BinOp, l: Ast, r: Ast, loc: Loc) -> Self {
        Self::new(
            AstKind::BinOp {
                op,
                l: Box::new(l),
                r: Box::new(r),
            },
            loc,
        )
    }

    fn triop(op: TriOp, b: Ast, l: Ast, r: Ast, loc: Loc) -> Self {
        Self::new(
            AstKind::TriOp {
                op,
                b: Box::new(b),
                l: Box::new(l),
                r: Box::new(r),
            },
            loc,
        )
    }
}

pub type Ast = Annot<AstKind>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UniOpKind {
    Plus,
    Minus,
}

pub type UniOp = Annot<UniOpKind>;

impl UniOp {
    fn plus(loc: Loc) -> Self {
        Self::new(UniOpKind::Plus, loc)
    }

    fn minus(loc: Loc) -> Self {
        Self::new(UniOpKind::Minus, loc)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    Plus,
    Minus,
    Times,
    Less,
}

pub type BinOp = Annot<BinOpKind>;

impl BinOp {
    fn plus(loc: Loc) -> Self {
        Self::new(BinOpKind::Plus, loc)
    }

    fn minus(loc: Loc) -> Self {
        Self::new(BinOpKind::Minus, loc)
    }

    fn times(loc: Loc) -> Self {
        Self::new(BinOpKind::Times, loc)
    }

    fn less(loc: Loc) -> Self {
        Self::new(BinOpKind::Less, loc)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TriOpKind {
    If,
}

pub type TriOp = Annot<TriOpKind>;

impl TriOp {
    fn if_(loc: Loc) -> Self {
        Self::new(TriOpKind::If, loc)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParseError {
    UnexpectedToken(Token),
    NotExpression(Token),
    NotOperator(Token),
    UnclosedOpenParen(Token),
    UnclosedIfThenElse(Token),
    RedundantExpression(Token),
    TypeError,
    Eof,
}

pub fn parse(tokens: Vec<Token>) -> Result<Ast, ParseError> {
    let mut tokens = tokens.into_iter().peekable();
    let ret = parse_expr(&mut tokens)?;
    match tokens.next() {
        Some(tok) => Err(ParseError::RedundantExpression(tok)),
        None => Ok(ret),
    }
}

fn parse_expr<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    parse_expr4(tokens)
}

fn parse_left_binop<Tokens>(
    tokens: &mut std::iter::Peekable<Tokens>,
    subexpr_parser: fn(&mut std::iter::Peekable<Tokens>) -> Result<Ast, ParseError>,
    op_parser: fn(&mut std::iter::Peekable<Tokens>) -> Result<BinOp, ParseError>,
) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    let mut e = subexpr_parser(tokens)?;
    loop {
        match tokens.peek() {
            Some(_) => {
                let op = match op_parser(tokens) {
                    Ok(op) => op,
                    Err(_) => break,
                };
                let r = subexpr_parser(tokens)?;
                let loc = e.loc.merge(&r.loc);
                e = Ast::binop(op, e, r, loc)
            }
            _ => break,
        }
    }
    Ok(e)
}
//
// EXPR = EXPR5
//
// EXPR4 = if EXPR4(bool) then EXPR4 else EXPR4 | EXPR_B
// EXPR_B = EXPR3, "<", EXPR3 | EXPR3
// EXPR3 = EXPR2, EXPR3_Loop(num)
// EXPR3_Loop = ("+" | "-"), EXPR2, EXPR3_Loop | e
// EXPR2 = EXPR1, EXPR2_Loop(num)
// EXPR2_Loop = "*", EXPR1 , EXPR2_Loop | e
// EXPR1 = ("+" | "-"), ATOM(num) | ATOM
// ATOM = BOOL | UNUMBER | "(", EXPR4, ")"
// UNUMBER = DIGIT, {DIGIT}
// DIGIT = "0" | ... | "9"
// BOOL = "true" | "false"
//
//

fn parse_expr4<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    match tokens.peek().map(|tok| tok.value.clone()) {
        Some(TokenKind::If) => {
            let op = tokens.next();
            let condition = parse_expr4(tokens)?;
            match tokens.next() {
                Some(Token {
                    value: TokenKind::Then,
                    ..
                }) => {
                    let l = parse_expr4(tokens)?;
                    let loc = condition.loc.merge(&l.loc);
                    match tokens.next() {
                        Some(Token {
                            value: TokenKind::Else,
                            ..
                        }) => {
                            let r = parse_expr4(tokens)?;
                            let loc = loc.merge(&r.loc);
                            Ok(Ast::triop(
                                TriOp::if_(op.unwrap().loc.clone()),
                                condition,
                                l,
                                r,
                                loc,
                            ))
                        }
                        tok => Err(ParseError::UnclosedIfThenElse(tok.unwrap())),
                    }
                }
                Some(t) => Err(ParseError::RedundantExpression(t)),
                tok => Err(ParseError::UnclosedIfThenElse(tok.unwrap())),
            }
        }
        _ => parse_expr_b(tokens),
    }
}

fn parse_expr_b<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    let e = parse_expr3(tokens)?;
    match tokens.peek().map(|tok| &tok.value) {
        Some(TokenKind::Less) => {
            let op = BinOp::less(tokens.next().unwrap().loc);
            let r = parse_expr3(tokens)?;
            let loc = e.loc.merge(&r.loc);
            Ok(Ast::binop(op, e, r, loc))
        }
        Some(_) => Ok(e),
        None => Ok(e),
    }
}

fn parse_expr3<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    fn parse_expr3_op<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<BinOp, ParseError>
    where
        Tokens: Iterator<Item = Token>,
    {
        let op = tokens
            .peek()
            .ok_or(ParseError::Eof)
            .and_then(|tok| match tok.value {
                TokenKind::Plus => Ok(BinOp::plus(tok.loc.clone())),
                TokenKind::Minus => Ok(BinOp::minus(tok.loc.clone())),
                _ => Err(ParseError::NotOperator(tok.clone())),
            })?;
        tokens.next();
        Ok(op)
    }
    parse_left_binop(tokens, parse_expr2, parse_expr3_op)
}

fn parse_expr2<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    fn parse_expr2_op<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<BinOp, ParseError>
    where
        Tokens: Iterator<Item = Token>,
    {
        let op = tokens
            .peek()
            .ok_or(ParseError::Eof)
            .and_then(|tok| match tok.value {
                TokenKind::Times => Ok(BinOp::times(tok.loc.clone())),
                _ => Err(ParseError::NotOperator(tok.clone())),
            })?;
        tokens.next();
        Ok(op)
    }
    parse_left_binop(tokens, parse_expr1, parse_expr2_op)
}

fn parse_expr1<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    match tokens.peek().map(|tok| &tok.value) {
        Some(TokenKind::Plus) | Some(TokenKind::Minus) => {
            let op = match tokens.next() {
                Some(Token {
                    value: TokenKind::Plus,
                    loc,
                }) => UniOp::plus(loc),
                Some(Token {
                    value: TokenKind::Minus,
                    loc,
                }) => UniOp::minus(loc),
                _ => unreachable!(),
            };

            let e = parse_atom(tokens)?;
            let loc = op.loc.merge(&e.loc);
            Ok(Ast::uniop(op, e, loc))
        }
        _ => parse_atom(tokens),
    }
}

fn parse_atom<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    tokens
        .next()
        .ok_or(ParseError::Eof)
        .and_then(|tok| match tok.value {
            TokenKind::Number(n) => Ok(Ast::num(n, tok.loc)),
            TokenKind::Bool(n) => Ok(Ast::bool_(n, tok.loc)),
            TokenKind::LParen => {
                let e = parse_expr4(tokens)?;
                match tokens.next() {
                    Some(Token {
                        value: TokenKind::RParen,
                        ..
                    }) => Ok(e),
                    Some(t) => Err(ParseError::RedundantExpression(t)),
                    _ => Err(ParseError::UnclosedOpenParen(tok)),
                }
            }
            //_ => Err(ParseError::NotExpression(tok)),
            _ => parse_expr4(tokens),
        })
}

fn parse_expr_b2<Tokens>(tokens: &mut std::iter::Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    match tokens.peek().map(|tok| tok.value.clone()) {
        Some(TokenKind::If) => {
            let op = tokens.next();
            let condition = parse_expr_b2(tokens)?;
            match tokens.next() {
                Some(Token {
                    value: TokenKind::Then,
                    ..
                }) => {
                    let l = parse_expr_b2(tokens)?;
                    let loc = condition.loc.merge(&l.loc);
                    match tokens.next() {
                        Some(Token {
                            value: TokenKind::Else,
                            ..
                        }) => {
                            let r = parse_expr_b2(tokens)?;
                            let loc = loc.merge(&r.loc);
                            Ok(Ast::triop(
                                TriOp::if_(op.unwrap().loc.clone()),
                                condition,
                                l,
                                r,
                                loc,
                            ))
                        }
                        tok => Err(ParseError::UnclosedIfThenElse(tok.unwrap())),
                    }
                }
                Some(t) => Err(ParseError::RedundantExpression(t)),
                tok => Err(ParseError::UnclosedIfThenElse(tok.unwrap())),
            }
        }
        _ => parse_expr_b(tokens),
    }
}
