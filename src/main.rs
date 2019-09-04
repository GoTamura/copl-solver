use std::env;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Loc(usize, usize);

impl Loc {
    fn merge(&self, other: &Loc) -> Loc {
        use std::cmp::{max, min};
        Loc(min(self.0, other.0), max(self.1, other.1))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Annot<T> {
    value: T,
    loc: Loc,
}

impl<T> Annot<T> {
    fn new(value: T, loc: Loc) -> Self {
        Self { value, loc }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TokenKind {
    Number(u64),
    Plus,
    Str(String),
}

type Token = Annot<TokenKind>;

impl Token {
    fn number(n: u64, loc: Loc) -> Self {
        Self::new(TokenKind::Number(n), loc)
    }

    fn plus(loc: Loc) -> Self {
        Self::new(TokenKind::Plus, loc)
    }

    fn str(s: String, loc: Loc) -> Self {
        Self::new(TokenKind::Str(s), loc)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum LexErrorKind {
    InvalidChar(char),
    Eof,
}

type LexError = Annot<LexErrorKind>;
impl LexError {
    fn invalid_char(c: char, loc: Loc) -> Self {
        LexError::new(LexErrorKind::InvalidChar(c), loc)
    }
    fn eof(loc: Loc) -> Self {
        LexError::new(LexErrorKind::Eof, loc)
    }
}

fn lex(input: &str) -> Result<Vec<Token>, LexError> {
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
    let s = from_utf8(&input[start..end]).unwrap().parse().unwrap();
    Ok((Token::str(s, Loc(start, end)), end))
}

fn skip_spaces(input: &[u8], pos: usize) -> Result<((), usize), LexError> {
    let pos = recognize_many(input, pos, |b| b" \n\t".contains(&b));

    Ok(((), pos))
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if 1 < args.len() {
        println!("{:?}", lex(&args[1]));
    }
}

#[test]
fn test_lexer() {
    assert_eq!(
        lex("1 + 3 plus 2 evalto"),
        Ok(vec![
            Token::number(1, Loc(0, 1)),
            Token::plus(Loc(2, 3)),
            Token::number(3, Loc(4, 5)),
            Token::str("plus".to_string(), Loc(6, 10)),
            Token::number(2, Loc(11, 12)),
            Token::str("evalto".to_string(), Loc(13, 19)),
        ])
    )
}

#[test]
fn test_lexer_plus_number() {
    assert_eq!(
        lex("1 + 2 +3 + 34"),
        Ok(vec![
            Token::number(1, Loc(0, 1)),
            Token::plus(Loc(2, 3)),
            Token::number(2, Loc(4, 5)),
            Token::plus(Loc(6, 7)),
            Token::number(3, Loc(7, 8)),
            Token::plus(Loc(9, 10)),
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
