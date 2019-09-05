#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Loc(usize, usize);

impl Loc {
    pub fn merge(&self, other: &Loc) -> Loc {
        use std::cmp::{max, min};
        Loc(min(self.0, other.0), max(self.1, other.1))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Annot<T> {
    pub value: T,
    pub loc: Loc,
}

impl<T> Annot<T> {
    pub fn new(value: T, loc: Loc) -> Self {
        Self { value, loc }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    Number(u64),
    Plus,
    Minus,
    Times,
    Less,
    RParen,
    LParen,
    If,
    Then,
    Else,
    Evalto,
    Bool(bool),
    Str(String),
}

pub type Token = Annot<TokenKind>;

impl Token {
    pub fn number(n: u64, loc: Loc) -> Self {
        Self::new(TokenKind::Number(n), loc)
    }

    pub fn plus(loc: Loc) -> Self {
        Self::new(TokenKind::Plus, loc)
    }

    pub fn minus(loc: Loc) -> Self {
        Self::new(TokenKind::Minus, loc)
    }

    pub fn times(loc: Loc) -> Self {
        Self::new(TokenKind::Times, loc)
    }

    pub fn less(loc: Loc) -> Self {
        Self::new(TokenKind::Less, loc)
    }

    pub fn rparen(loc: Loc) -> Self {
        Self::new(TokenKind::RParen, loc)
    }

    pub fn lparen(loc: Loc) -> Self {
        Self::new(TokenKind::LParen, loc)
    }

    pub fn if_(loc: Loc) -> Self {
        Self::new(TokenKind::If, loc)
    }

    pub fn then(loc: Loc) -> Self {
        Self::new(TokenKind::Then, loc)
    }

    pub fn else_(loc: Loc) -> Self {
        Self::new(TokenKind::Else, loc)
    }

    pub fn evalto(loc: Loc) -> Self {
        Self::new(TokenKind::Evalto, loc)
    }

    pub fn bool_(b: bool, loc: Loc) -> Self {
        Self::new(TokenKind::Bool(b), loc)
    }

    pub fn str(s: String, loc: Loc) -> Self {
        Self::new(TokenKind::Str(s), loc)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LexErrorKind {
    InvalidChar(char),
    Eof,
}

pub type LexError = Annot<LexErrorKind>;
impl LexError {
    fn invalid_char(c: char, loc: Loc) -> Self {
        LexError::new(LexErrorKind::InvalidChar(c), loc)
    }
    fn eof(loc: Loc) -> Self {
        LexError::new(LexErrorKind::Eof, loc)
    }
}

pub fn lex(input: &str) -> Result<Vec<Token>, LexError> {
    let mut tokens = Vec::new();

    let input = input.as_bytes();

    let mut pos = 0;
    macro_rules! lex_a_token {
        ($lexer:expr) => {{
            let (tok, p) = $lexer?;
            tokens.push(tok);
            pos = p;
        }};
    }

    while pos < input.len() {
        match input[pos] {
            b'0'...b'9' => lex_a_token!(lex_number(input, pos)),
            b'a'...b'z' | b'A'...b'Z' | b'_' => lex_a_token!(lex_str(input, pos)),
            b'+' => lex_a_token!(lex_plus(input, pos)),
            b'-' => lex_a_token!(lex_minus(input, pos)),
            b'*' => lex_a_token!(lex_times(input, pos)),
            b'<' => lex_a_token!(lex_less(input, pos)),
            b'(' => lex_a_token!(lex_lparen(input, pos)),
            b')' => lex_a_token!(lex_rparen(input, pos)),
            b' ' | b'\n' | b'\t' => {
                let ((), p) = skip_spaces(input, pos)?;
                pos = p;
            }
            b => return Err(LexError::invalid_char(b as char, Loc(pos, pos + 1))),
        }
    }
    Ok(tokens)
}

fn consume_byte(input: &[u8], pos: usize, b: u8) -> Result<(u8, usize), LexError> {
    if input.len() <= pos {
        return Err(LexError::eof(Loc(pos, pos)));
    }

    if input[pos] != b {
        return Err(LexError::invalid_char(
            input[pos] as char,
            Loc(pos, pos + 1),
        ));
    }
    Ok((b, pos + 1))
}

fn recognize_many(input: &[u8], mut pos: usize, mut f: impl FnMut(u8) -> bool) -> usize {
    while pos < input.len() && f(input[pos]) {
        pos += 1;
    }
    pos
}

fn lex_plus(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'+').map(|(_, end)| (Token::plus(Loc(start, end)), end))
}

fn lex_minus(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'-').map(|(_, end)| (Token::minus(Loc(start, end)), end))
}

fn lex_times(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'*').map(|(_, end)| (Token::times(Loc(start, end)), end))
}

fn lex_less(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'<').map(|(_, end)| (Token::less(Loc(start, end)), end))
}

fn lex_lparen(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'(').map(|(_, end)| (Token::lparen(Loc(start, end)), end))
}

fn lex_rparen(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b')').map(|(_, end)| (Token::rparen(Loc(start, end)), end))
}

fn lex_number(input: &[u8], pos: usize) -> Result<(Token, usize), LexError> {
    use std::str::from_utf8;
    let start = pos;
    let end = recognize_many(input, start, |b| b"1234567890".contains(&b));
    let n = from_utf8(&input[start..end]).unwrap().parse().unwrap();
    Ok((Token::number(n, Loc(start, end)), end))
}

fn lex_str(input: &[u8], pos: usize) -> Result<(Token, usize), LexError> {
    use std::str::from_utf8;
    let start = pos;
    let end = recognize_many(input, start, |b| {
        (&b).is_ascii_alphanumeric() || b"_".contains(&b)
    });
    let s = from_utf8(&input[start..end]).unwrap();
    match s {
        "if" => Ok((Token::if_(Loc(start, end)), end)),
        "then" => Ok((Token::then(Loc(start, end)), end)),
        "else" => Ok((Token::else_(Loc(start, end)), end)),
        "evalto" => Ok((Token::evalto(Loc(start, end)), end)),
        "true" => Ok((Token::bool_(true, Loc(start, end)), end)),
        "false" => Ok((Token::bool_(false, Loc(start, end)), end)),
        _ => Ok((Token::str(s.to_string(), Loc(start, end)), end)),
    }
}

fn skip_spaces(input: &[u8], pos: usize) -> Result<((), usize), LexError> {
    let pos = recognize_many(input, pos, |b| b" \n\t".contains(&b));

    Ok(((), pos))
}

#[test]
fn test_lexer() {
    assert_eq!(
        lex("1 - 3 plus 2 evalto"),
        Ok(vec![
            Token::number(1, Loc(0, 1)),
            Token::minus(Loc(2, 3)),
            Token::number(3, Loc(4, 5)),
            Token::str("plus".to_string(), Loc(6, 10)),
            Token::number(2, Loc(11, 12)),
            Token::str("evalto".to_string(), Loc(13, 19)),
        ])
    )
}

#[test]
fn test_lexer_operator_number() {
    assert_eq!(
        lex("1 + 2 -3 < 34"),
        Ok(vec![
            Token::number(1, Loc(0, 1)),
            Token::plus(Loc(2, 3)),
            Token::number(2, Loc(4, 5)),
            Token::minus(Loc(6, 7)),
            Token::number(3, Loc(7, 8)),
            Token::less(Loc(9, 10)),
            Token::number(34, Loc(11, 13)),
        ])
    )
}

#[test]
fn test_lexer_str() {
    assert_eq!(
        lex("aBc _ab ab3 +ab 3ab"),
        Ok(vec![
            Token::str("aBc".to_string(), Loc(0, 3)),
            Token::str("_ab".to_string(), Loc(4, 7)),
            Token::str("ab3".to_string(), Loc(8, 11)),
            Token::plus(Loc(12, 13)),
            Token::str("ab".to_string(), Loc(13, 15)),
            Token::number(3, Loc(16, 17)),
            Token::str("ab".to_string(), Loc(17, 19)),
        ])
    )
}
