use regex::Regex;
use std::{
    borrow::Cow, error::Error as StdError, fmt::Display, iter::Peekable, mem, str::Chars,
    sync::OnceLock,
};

const START_TAG_RE_STR: &'static str = r"^<[a-z][a-z0-9.-]*(-[a-z0-9.-]+)?";
const END_TAG_RE_STR: &'static str = r"^</[a-z][a-z0-9.-]*(-[a-z0-9.-]+)?\s*>";
const START_TAG_RE: OnceLock<Regex> = OnceLock::new();
const END_TAG_RE: OnceLock<Regex> = OnceLock::new();

#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TokenizeError<'a> {
    InvalidTagName(Cow<'a, str>),
    InvalidTagAttrName(Cow<'a, str>),
    MalformedEndTag(Cow<'a, str>),
    MalformedSelfClosingTag(Cow<'a, str>),
    MalformedTagAttr(Cow<'a, str>),
    MalformedCommentTag,
    MalformedDocTypeTag,
}

impl<'a> Display for TokenizeError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            TokenizeError::InvalidTagName(name) => format!("{} is not a valid tag name", name),
            TokenizeError::InvalidTagAttrName(name) => {
                format!("{} is not a valid tag attr name", name)
            }
            TokenizeError::MalformedEndTag(reason) => format!("malformed end tag. ({})", reason),
            TokenizeError::MalformedSelfClosingTag(reason) => {
                format!("malformed self closing tag. ({})", reason)
            }
            TokenizeError::MalformedTagAttr(reason) => format!("{}", reason),
            TokenizeError::MalformedCommentTag => format!("malformed comment tag"),
            TokenizeError::MalformedDocTypeTag => format!("malformed doctype tag"),
        };

        write!(f, "tokenize error. ({})", message)
    }
}

impl<'a> StdError for TokenizeError<'a> {}

#[derive(Debug, PartialEq, Eq)]
pub struct TagAttr {
    name: String,
    value: Option<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct OpenTag {
    name: String,
    tag_attrs: Vec<TagAttr>,
    self_closing: bool,
}

#[derive(Debug)]
struct OpenTagBuilder {
    name: String,
    tag_attrs: Vec<TagAttr>,
}

impl OpenTagBuilder {
    fn new(name: String) -> Self {
        Self {
            name,
            tag_attrs: vec![],
        }
    }

    fn add_attr_name(&mut self, name: String) {
        let attr = TagAttr { name, value: None };
        self.tag_attrs.push(attr);
    }

    fn set_attr_value(&mut self, value: String) -> Result<&mut Self, TokenizeError<'static>> {
        if let Some(attr) = self.tag_attrs.last_mut() {
            if attr.value.is_some() {
                Err(TokenizeError::MalformedTagAttr(Cow::Borrowed(
                    "the attr for the value is already set a name",
                )))
            } else {
                attr.value = Some(value);
                Ok(self)
            }
        } else {
            Err(TokenizeError::MalformedTagAttr(Cow::Borrowed(
                "tag name for the value does not exist",
            )))
        }
    }

    fn build(self, self_closing: bool) -> OpenTag {
        OpenTag {
            name: self.name,
            tag_attrs: self.tag_attrs,
            self_closing,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    OpenTag(OpenTag),
    Comment(String),
    Text(String),
    CloseTag(String),
    DocTypeTag,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct Loc {
    row: usize,
    col: usize,
}

impl Loc {
    fn advance(&mut self) {
        self.col += 1;
    }

    fn break_line(&mut self) {
        self.row += 1;
        self.col = 0;
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct WithLoc<T> {
    value: T,
    loc: Loc,
}

impl<T> WithLoc<T> {
    fn new(value: T, loc: Loc) -> Self {
        Self { value, loc }
    }
}

impl<T: Display> Display for WithLoc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}. (row: {}, col: {})",
            self.value, self.loc.row, self.loc.col
        )
    }
}

impl<T: StdError + Send + Sync + 'static> StdError for WithLoc<T> {}

#[derive(Debug)]
struct Input<'a> {
    src: &'a str,
    peekable: Peekable<Chars<'a>>,
    loc: Loc,
    pos: usize,
}

impl<'a> Input<'a> {
    fn new(src: &'a str) -> Self {
        let chars = src.chars();
        Self {
            src,
            peekable: chars.peekable(),
            loc: Loc::default(),
            pos: 0,
        }
    }

    fn advance(&mut self) -> bool {
        match self.peekable.next() {
            Some(v) => {
                if v == '\n' {
                    self.loc.break_line();
                } else {
                    self.loc.advance();
                }
                self.pos += v.len_utf8();
                true
            }
            _ => false,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.peekable.peek().copied()
    }

    fn remaining(&self) -> &'a str {
        &self.src[self.pos..]
    }

    fn starts_with(&self, target: impl AsRef<str>) -> bool {
        self.remaining().starts_with(target.as_ref())
    }

    fn starts_with_case_insensitive(&self, target: impl AsRef<str>) -> bool {
        let chars = target.as_ref().chars();
        let mut remaining_chars = self.remaining().chars();

        for c in chars {
            if let Some(v) = remaining_chars.next() {
                if !c.eq_ignore_ascii_case(&v) {
                    return false;
                }
            } else {
                return false;
            }
        }
        true
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum TokenizerState {
    AfterEndTagName,
    AfterTagAttr,
    AfterTagValue,
    BeforeTagAttr,
    BeforeTagValue,
    Comment,
    DocType,
    DocTypeOrComment,
    EndTagOpen,
    SelfClosingTagSlash,
    TagAttr,
    TagName,
    TagOpen,
    TagValue,
    Text,
}

#[derive(Debug)]
pub struct Tokenizer<'a> {
    input: Input<'a>,
    token_loc: Loc,
    state: TokenizerState,
    is_end_tag: bool,
    tag_name: String,
    tag_attr_name: String,
    tag_value: String,
    text: String,
    re_for_tag_name: Regex,
    tokens: Vec<Token>,
    open_tag_builder: Option<OpenTagBuilder>,
    comment: String,
}

type TokenizeResult<'a, T> = Result<T, WithLoc<TokenizeError<'a>>>;

impl<'a> Tokenizer<'a> {
    pub fn new(src: &'a str) -> Self {
        let _ = START_TAG_RE.get_or_init(|| Regex::new(START_TAG_RE_STR).unwrap());
        let _ = END_TAG_RE.get_or_init(|| Regex::new(END_TAG_RE_STR).unwrap());

        Self {
            input: Input::new(src),
            token_loc: Loc::default(),
            state: TokenizerState::Text,
            is_end_tag: false,
            tag_name: String::new(),
            tag_attr_name: String::new(),
            tag_value: String::new(),
            text: String::new(),
            re_for_tag_name: Regex::new(r"^[a-z]+[[:alnum:]]*$").unwrap(),
            tokens: vec![],
            open_tag_builder: None,
            comment: String::new(),
        }
    }

    pub fn tokenize(&mut self) -> TokenizeResult<'a, &[Token]> {
        while let Some(ch) = self.peek() {
            match self.state {
                TokenizerState::AfterEndTagName => self.handle_after_tag_name(ch)?,
                TokenizerState::AfterTagAttr => self.handle_after_tag_attr(ch)?,
                TokenizerState::AfterTagValue => self.handle_after_tag_value(ch)?,
                TokenizerState::BeforeTagAttr => self.handle_before_tag_attr(ch)?,
                TokenizerState::BeforeTagValue => self.handle_before_tag_value(ch)?,
                TokenizerState::Comment => self.handle_comment(ch)?,
                TokenizerState::DocType => self.handle_doc_type(ch)?,
                TokenizerState::DocTypeOrComment => self.handle_before_doc_type_or_comment(ch)?,
                TokenizerState::EndTagOpen => self.handle_end_tag_open(ch)?,
                TokenizerState::SelfClosingTagSlash => self.handle_self_closing_tag_slash(ch)?,
                TokenizerState::TagAttr => self.handle_tag_attr(ch)?,
                TokenizerState::TagName => self.handle_tag_name(ch)?,
                TokenizerState::TagOpen => self.handle_tag_open(ch)?,
                TokenizerState::TagValue => self.handle_tag_value(ch)?,
                TokenizerState::Text => self.handle_text(ch)?,
            }
        }

        if !self.text.is_empty() {
            self.tokens.push(Token::Text(mem::take(&mut self.text)));
        }

        Ok(&self.tokens)
    }

    fn handle_after_tag_name(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        match ch {
            '>' => {
                self.state = TokenizerState::Text;
            }
            _ => {
                if !ch.is_whitespace() {
                    return Err(WithLoc::new(
                        TokenizeError::MalformedEndTag(Cow::Borrowed("end tag can only have name")),
                        self.input.loc,
                    ));
                }
            }
        }
        self.advance();
        Ok(())
    }

    fn handle_after_tag_attr(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        match ch {
            '>' => {
                self.finalize_open_tag(false);
                self.state = TokenizerState::Text;
            }
            '=' => {
                self.state = TokenizerState::BeforeTagValue;
            }
            '/' => {
                self.state = TokenizerState::SelfClosingTagSlash;
            }
            ch if !ch.is_whitespace() => {
                self.tag_attr_name.push(ch);
                self.state = TokenizerState::TagAttr;
            }
            _ => {}
        }

        self.advance();
        Ok(())
    }

    fn handle_after_tag_value(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        match ch {
            '>' => {
                self.finalize_open_tag(false);
                self.state = TokenizerState::Text;
            }
            '/' => {
                self.state = TokenizerState::SelfClosingTagSlash;
            }
            ch => {
                if !ch.is_whitespace() {
                    self.tag_attr_name.push(ch);
                    self.state = TokenizerState::TagAttr;
                }
            }
        }

        self.advance();
        Ok(())
    }

    fn handle_before_tag_attr(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        match ch {
            '>' => {
                self.finalize_open_tag(false);
                self.state = TokenizerState::Text;
            }
            '/' => {
                self.state = TokenizerState::SelfClosingTagSlash;
            }
            ch if !ch.is_whitespace() => {
                self.tag_attr_name.push(ch);
                self.state = TokenizerState::TagAttr;
            }
            _ => {}
        }

        self.advance();
        Ok(())
    }

    fn handle_before_tag_value(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        match ch {
            '"' => {}
            ch => {
                if !ch.is_whitespace() {
                    self.tag_value.push(ch);
                    self.state = TokenizerState::TagValue;
                }
            }
        }

        self.advance();
        Ok(())
    }

    fn handle_comment(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        if ch == '-' {
            if self.input.starts_with("-->") {
                self.advance();
                self.advance();
                self.advance();
                self.tokens
                    .push(Token::Comment(mem::take(&mut self.comment)));
                self.state = TokenizerState::Text;
            } else {
                return Err(WithLoc::new(
                    TokenizeError::MalformedCommentTag,
                    self.input.loc,
                ));
            }
        } else {
            self.comment.push(ch);
            self.advance();
        }
        Ok(())
    }

    fn handle_doc_type(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        if ch == '>' {
            self.tokens.push(Token::DocTypeTag);
            self.state = TokenizerState::Text;
        }
        self.advance();
        Ok(())
    }

    fn handle_before_doc_type_or_comment(&mut self, _ch: char) -> TokenizeResult<'a, ()> {
        if self.input.starts_with("-") {
            if !self.input.starts_with("--") {
                return Err(WithLoc::new(
                    TokenizeError::MalformedCommentTag,
                    self.input.loc,
                ));
            }

            self.advance();
            self.advance();
            self.state = TokenizerState::Comment;
        } else {
            if !self.input.starts_with_case_insensitive("DOCTYPE") {
                return Err(WithLoc::new(
                    TokenizeError::MalformedDocTypeTag,
                    self.input.loc,
                ));
            }
            self.state = TokenizerState::DocType;
            for _ in 0..7 {
                self.advance();
            }
        }
        Ok(())
    }

    fn handle_end_tag_open(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        self.state = TokenizerState::TagName;
        self.tag_name.push(ch);
        self.advance();
        Ok(())
    }

    fn handle_self_closing_tag_slash(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        match ch {
            '>' => {
                self.finalize_open_tag(true);
                self.state = TokenizerState::Text;
            }
            _ => {
                if !ch.is_whitespace() {
                    return Err(WithLoc::new(
                        TokenizeError::MalformedSelfClosingTag(Cow::Borrowed(
                            "self closing tag does not accept any character after slash",
                        )),
                        self.input.loc,
                    ));
                }
            }
        }

        self.advance();
        Ok(())
    }

    fn handle_tag_attr(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        if ch == '>' || ch == '=' || ch.is_whitespace() {
            let tag_attr_name = mem::take(&mut self.tag_attr_name);
            if let None = self.re_for_tag_name.captures(&tag_attr_name) {
                return Err(WithLoc::new(
                    TokenizeError::InvalidTagAttrName(Cow::Owned(tag_attr_name)),
                    self.input.loc,
                ));
            }
            self.open_tag_builder
                .as_mut()
                .unwrap()
                .add_attr_name(tag_attr_name);
            self.state = if ch == '>' {
                self.finalize_open_tag(false);
                TokenizerState::Text
            } else if ch == '=' {
                TokenizerState::BeforeTagValue
            } else if ch == '/' {
                TokenizerState::SelfClosingTagSlash
            } else {
                TokenizerState::AfterTagAttr
            };
        } else {
            self.tag_attr_name.push(ch);
        }

        self.advance();
        Ok(())
    }

    fn handle_tag_name(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        if ch == '>' || ch.is_whitespace() {
            let token_finalized = ch == '>';

            let tag = mem::take(&mut self.tag_name);
            if let None = self.re_for_tag_name.captures(&tag) {
                return Err(WithLoc::new(
                    TokenizeError::InvalidTagName(Cow::Owned(tag)),
                    self.input.loc,
                ));
            }
            if self.is_end_tag {
                self.tokens.push(Token::CloseTag(tag));
            } else {
                if token_finalized {
                    self.tokens.push(Token::OpenTag(OpenTag {
                        name: tag,
                        tag_attrs: vec![],
                        self_closing: false,
                    }));
                } else {
                    self.open_tag_builder = Some(OpenTagBuilder::new(tag));
                }
            }
            self.state = if token_finalized {
                TokenizerState::Text
            } else if self.is_end_tag {
                TokenizerState::AfterEndTagName
            } else {
                TokenizerState::BeforeTagAttr
            };
        } else {
            self.tag_name.push(ch);
        }

        self.advance();
        Ok(())
    }

    fn handle_tag_open(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        if !self.text.is_empty() {
            self.tokens.push(Token::Text(mem::take(&mut self.text)));
        }

        if ch == '!' {
            self.state = TokenizerState::DocTypeOrComment;
        } else {
            if ch == '/' {
                self.state = TokenizerState::EndTagOpen;
                self.is_end_tag = true;
            } else {
                self.state = TokenizerState::TagName;
                self.tag_name.push(ch);
                self.is_end_tag = false;
            }
        }
        self.advance();
        Ok(())
    }

    fn handle_tag_value(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        if ch == '"' {
            let tag_value = mem::take(&mut self.tag_value);
            self.open_tag_builder
                .as_mut()
                .unwrap()
                .set_attr_value(tag_value)
                .map_err(|e| WithLoc::new(e, self.input.loc))?;
            self.state = TokenizerState::AfterTagValue;
        } else {
            self.tag_value.push(ch);
        }

        self.advance();
        Ok(())
    }

    fn handle_text(&mut self, ch: char) -> TokenizeResult<'a, ()> {
        if ch == '<'
            || START_TAG_RE
                .get_or_init(|| Regex::new(START_TAG_RE_STR).unwrap())
                .is_match(self.input.remaining())
            || END_TAG_RE
                .get_or_init(|| Regex::new(END_TAG_RE_STR).unwrap())
                .is_match(self.input.remaining())
            || self.input.starts_with("<!")
        {
            self.state = TokenizerState::TagOpen;
        } else {
            self.text.push(ch);
        }
        self.advance();
        Ok(())
    }

    fn finalize_open_tag(&mut self, self_closing: bool) {
        if let Some(builder) = self.open_tag_builder.take() {
            self.tokens
                .push(Token::OpenTag(builder.build(self_closing)));
        }
    }

    fn advance(&mut self) -> bool {
        self.input.advance()
    }

    fn peek(&mut self) -> Option<char> {
        self.input.peek()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_input() {
        let mut input = Input::new("tあ\nz");
        input.advance();
        assert_eq!(input.loc, Loc { row: 0, col: 1 });
        assert_eq!(input.pos, 1);
        assert_eq!(input.remaining(), "あ\nz");

        input.advance();
        assert_eq!(input.loc, Loc { row: 0, col: 2 });
        assert_eq!(input.pos, 4);
        assert_eq!(input.remaining(), "\nz");

        input.advance();
        assert_eq!(input.loc, Loc { row: 1, col: 0 });
        assert_eq!(input.pos, 5);
        assert_eq!(input.remaining(), "z");

        input.advance();
        assert_eq!(input.loc, Loc { row: 1, col: 1 });
        assert_eq!(input.pos, 6);
        assert_eq!(input.remaining(), "");

        input.advance();
        assert_eq!(input.loc, Loc { row: 1, col: 1 });
        assert_eq!(input.pos, 6);
        assert_eq!(input.remaining(), "");
    }

    #[test]
    fn test_simple_tag_with_no_child() {
        assert_eq!(
            Tokenizer::new("<tag></tag>").tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Token::CloseTag("tag".to_owned())
            ]
            .as_ref())
        );
    }

    #[test]
    fn test_simple_tag_with_child() {
        assert_eq!(
            Tokenizer::new("<tag>abc>hoge</tag>").tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Token::Text("abc>hoge".to_owned()),
                Token::CloseTag("tag".to_owned())
            ]
            .as_ref())
        );
    }

    #[test]
    fn test_simple_tag_with_closed_comment_tag() {
        assert_eq!(
            Tokenizer::new("<tag>before <!-- comment --> after</tag>").tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Token::Text("before ".to_owned()),
                Token::Comment(" comment ".to_owned()),
                Token::Text(" after".to_owned()),
                Token::CloseTag("tag".to_owned()),
            ]
            .as_ref())
        );
    }

    #[test]
    fn test_simple_tag_but_unmatched_tag_name() {
        assert_eq!(
            Tokenizer::new("<tag1></tag>").tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag1".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Token::CloseTag("tag".to_owned())
            ]
            .as_ref())
        );
    }

    #[test]
    fn test_invalid_tag_name() {
        // invalid tag name
        assert_eq!(
            Tokenizer::new("<2a></tag>").tokenize(),
            Err(WithLoc::new(
                TokenizeError::InvalidTagName(Cow::Borrowed("2a")),
                Loc { row: 0, col: 3 }
            ))
        );

        assert_eq!(
            Tokenizer::new("<tag></3b>").tokenize(),
            Err(WithLoc::new(
                TokenizeError::InvalidTagName(Cow::Borrowed("3b")),
                Loc { row: 0, col: 9 }
            ))
        );
    }

    #[test]
    fn test_invalid_tag_name_with_line_break() {
        assert_eq!(
            Tokenizer::new("<tag>\n</999999a>").tokenize(),
            Err(WithLoc::new(
                TokenizeError::InvalidTagName(Cow::Borrowed("999999a")),
                Loc { row: 1, col: 9 }
            ))
        );
    }

    #[test]
    fn test_tag_with_tag_attr() {
        assert_eq!(
            Tokenizer::new("<tag attr></tag>").tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag".to_owned(),
                    tag_attrs: vec![TagAttr {
                        name: "attr".to_owned(),
                        value: None
                    }],
                    self_closing: false,
                }),
                Token::CloseTag("tag".to_owned())
            ]
            .as_ref())
        );
    }

    #[test]
    fn test_tag_with_multi_tag_attrs() {
        assert_eq!(
            Tokenizer::new("<tag attr1 attr2></tag>").tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag".to_owned(),
                    tag_attrs: vec![
                        TagAttr {
                            name: "attr1".to_owned(),
                            value: None
                        },
                        TagAttr {
                            name: "attr2".to_owned(),
                            value: None
                        },
                    ],
                    self_closing: false,
                }),
                Token::CloseTag("tag".to_owned())
            ]
            .as_ref())
        );
    }

    #[test]
    fn test_tag_with_invalid_tag_attr_name() {
        assert_eq!(
            Tokenizer::new("<tag 3attr></tag>").tokenize(),
            Err(WithLoc::new(
                TokenizeError::InvalidTagAttrName(Cow::Borrowed("3attr")),
                Loc { row: 0, col: 10 }
            ))
        );
    }

    #[test]
    fn test_tag_with_attr_and_value() {
        assert_eq!(
            Tokenizer::new(r#"<tag attr="value"></tag>"#).tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag".to_owned(),
                    tag_attrs: vec![TagAttr {
                        name: "attr".to_owned(),
                        value: Some("value".to_owned()),
                    }],
                    self_closing: false,
                }),
                Token::CloseTag("tag".to_owned())
            ]
            .as_ref())
        );

        // allow space between tag attr name and it's value
        assert_eq!(
            Tokenizer::new(r#"<tag attr         = "value"></tag>"#).tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag".to_owned(),
                    tag_attrs: vec![TagAttr {
                        name: "attr".to_owned(),
                        value: Some("value".to_owned()),
                    }],
                    self_closing: false,
                }),
                Token::CloseTag("tag".to_owned())
            ]
            .as_ref())
        );
    }

    #[test]
    fn test_tag_with_multiple_attr_and_values() {
        assert_eq!(
            Tokenizer::new(r#"<tag attr1="value1" attr2 = "value2"></tag>"#).tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag".to_owned(),
                    tag_attrs: vec![
                        TagAttr {
                            name: "attr1".to_owned(),
                            value: Some("value1".to_owned()),
                        },
                        TagAttr {
                            name: "attr2".to_owned(),
                            value: Some("value2".to_owned()),
                        },
                    ],
                    self_closing: false,
                }),
                Token::CloseTag("tag".to_owned())
            ]
            .as_ref())
        );
    }

    #[test]
    fn test_malformed_end_tag() {
        assert_eq!(
            Tokenizer::new("<tag attr1=\"value1\">line1\nline2</tag attr>").tokenize(),
            Err(WithLoc::new(
                TokenizeError::MalformedEndTag(Cow::Borrowed("end tag can only have name")),
                Loc { row: 1, col: 11 }
            ))
        );
    }

    #[test]
    fn test_simple_self_closing_tag() {
        assert_eq!(
            Tokenizer::new("<tag />").tokenize(),
            Ok(vec![Token::OpenTag(OpenTag {
                name: "tag".to_owned(),
                tag_attrs: vec![],
                self_closing: true,
            }),]
            .as_ref())
        );
    }

    #[test]
    fn test_self_closing_tag_with_attr() {
        assert_eq!(
            Tokenizer::new("<tag attr />").tokenize(),
            Ok(vec![Token::OpenTag(OpenTag {
                name: "tag".to_owned(),
                tag_attrs: vec![TagAttr {
                    name: "attr".to_owned(),
                    value: None,
                }],
                self_closing: true,
            }),]
            .as_ref())
        );

        assert_eq!(
            Tokenizer::new("<tag attr1 attr2 />").tokenize(),
            Ok(vec![Token::OpenTag(OpenTag {
                name: "tag".to_owned(),
                tag_attrs: vec![
                    TagAttr {
                        name: "attr1".to_owned(),
                        value: None,
                    },
                    TagAttr {
                        name: "attr2".to_owned(),
                        value: None,
                    }
                ],
                self_closing: true,
            }),]
            .as_ref())
        );
    }

    #[test]
    fn test_self_closing_tag_with_attr_with_value() {
        assert_eq!(
            Tokenizer::new(r#"<tag attr1="value1" />"#).tokenize(),
            Ok(vec![Token::OpenTag(OpenTag {
                name: "tag".to_owned(),
                tag_attrs: vec![TagAttr {
                    name: "attr1".to_owned(),
                    value: Some("value1".to_owned()),
                }],
                self_closing: true,
            }),]
            .as_ref())
        );

        assert_eq!(
            Tokenizer::new(r#"<tag attr1="value1" attr2 = "value2" />"#).tokenize(),
            Ok(vec![Token::OpenTag(OpenTag {
                name: "tag".to_owned(),
                tag_attrs: vec![
                    TagAttr {
                        name: "attr1".to_owned(),
                        value: Some("value1".to_owned()),
                    },
                    TagAttr {
                        name: "attr2".to_owned(),
                        value: Some("value2".to_owned()),
                    },
                ],
                self_closing: true,
            }),]
            .as_ref())
        );
    }

    #[test]
    fn test_self_closing_tag_with_spaces_after_slash() {
        assert_eq!(
            Tokenizer::new("<tag attr /               >").tokenize(),
            Ok(vec![Token::OpenTag(OpenTag {
                name: "tag".to_owned(),
                tag_attrs: vec![TagAttr {
                    name: "attr".to_owned(),
                    value: None,
                }],
                self_closing: true,
            }),]
            .as_ref())
        );
    }

    #[test]
    fn test_malformed_self_closing_tag() {
        assert_eq!(
            Tokenizer::new(r#"<tag attr attr2="value2" /        token       >"#).tokenize(),
            Err(WithLoc::new(
                TokenizeError::MalformedSelfClosingTag(Cow::Borrowed(
                    "self closing tag does not accept any character after slash"
                )),
                Loc { row: 0, col: 34 }
            ))
        );
    }

    #[test]
    fn test_starts_with() {
        let tokenizer = Tokenizer::new("t123");
        assert_eq!(tokenizer.input.starts_with(""), true);
        assert_eq!(tokenizer.input.starts_with("t"), true);
        assert_eq!(tokenizer.input.starts_with("t1"), true);
        assert_eq!(tokenizer.input.starts_with("t12"), true);
        assert_eq!(tokenizer.input.starts_with("T123"), false);
        assert_eq!(tokenizer.input.starts_with("t1234"), false);
    }

    #[test]
    fn test_starts_with_case_insensitive() {
        let tokenizer = Tokenizer::new("t123");
        assert_eq!(tokenizer.input.starts_with_case_insensitive(""), true);
        assert_eq!(tokenizer.input.starts_with_case_insensitive("t"), true);
        assert_eq!(tokenizer.input.starts_with_case_insensitive("t1"), true);
        assert_eq!(tokenizer.input.starts_with_case_insensitive("t12"), true);
        assert_eq!(tokenizer.input.starts_with_case_insensitive("T123"), true);
        assert_eq!(tokenizer.input.starts_with_case_insensitive("t1234"), false);
    }

    #[test]
    fn test_comment_tag() {
        assert_eq!(
            Tokenizer::new("<!--comment-->").tokenize(),
            Ok(vec![Token::Comment("comment".to_owned()),].as_ref())
        );

        let comment = r#"<!--
        this
        is
        comment
        -->"#;

        assert_eq!(
            Tokenizer::new(comment).tokenize(),
            Ok(vec![Token::Comment(
                "\n        this\n        is\n        comment\n        ".to_owned()
            ),]
            .as_ref())
        );
    }

    #[test]
    fn test_malformed_comment_tag() {
        assert_eq!(
            Tokenizer::new("<!-comment-->").tokenize(),
            Err(WithLoc::new(
                TokenizeError::MalformedCommentTag,
                Loc { row: 0, col: 2 }
            ))
        );

        assert_eq!(
            Tokenizer::new("<!--comment--->").tokenize(),
            Err(WithLoc::new(
                TokenizeError::MalformedCommentTag,
                Loc { row: 0, col: 11 }
            ))
        );
    }

    #[test]
    fn test_doc_type_tag() {
        assert_eq!(
            Tokenizer::new("<!doctype>").tokenize(),
            Ok(vec![Token::DocTypeTag].as_ref()),
        );

        // allow case insensitive "doctype"
        assert_eq!(
            Tokenizer::new("<!Doctype>").tokenize(),
            Ok(vec![Token::DocTypeTag].as_ref()),
        );

        assert_eq!(
            Tokenizer::new("test1<!Doctype>test2").tokenize(),
            Ok(vec![
                Token::Text("test1".to_owned()),
                Token::DocTypeTag,
                Token::Text("test2".to_owned()),
            ]
            .as_ref()),
        );
    }

    #[test]
    fn test_malformed_doc_type_tag() {
        assert_eq!(
            Tokenizer::new("<!doctyp>").tokenize(),
            Err(WithLoc::new(
                TokenizeError::MalformedDocTypeTag,
                Loc { row: 0, col: 2 }
            ))
        );
    }

    #[test]
    fn test_html() {
        let html = r#"
<!doctype html>
<html>
<head>
<title>test html</title>
</head>
<body>
<p>this is p tag</p>
<!--
comment start 
<div attr1 attr2="value2">this div in a comment</div>
-->
<img src="test" />
<custom attr1></custom>
</body>
</html>
        "#
        .trim();

        fn new_line_text() -> Token {
            Token::Text("\n".to_owned())
        }
        assert_eq!(
            Tokenizer::new(html).tokenize(),
            Ok(vec![
                Token::DocTypeTag,
                new_line_text(),
                Token::OpenTag(OpenTag {
                    name: "html".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false
                }),
                new_line_text(),
                Token::OpenTag(OpenTag {
                    name: "head".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false
                }),
                new_line_text(),
                Token::OpenTag(OpenTag {
                    name: "title".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false
                }),
                Token::Text("test html".to_owned()),
                Token::CloseTag("title".to_owned()),
                new_line_text(),
                Token::CloseTag("head".to_owned()),
                new_line_text(),
                Token::OpenTag(OpenTag {
                    name: "body".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false
                }),
                new_line_text(),
                Token::OpenTag(OpenTag {
                    name: "p".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false
                }),
                Token::Text("this is p tag".to_owned()),
                Token::CloseTag("p".to_owned()),
                new_line_text(),
                Token::Comment(
                    "\ncomment start \n<div attr1 attr2=\"value2\">this div in a comment</div>\n"
                        .to_owned()
                ),
                new_line_text(),
                Token::OpenTag(OpenTag {
                    name: "img".to_owned(),
                    tag_attrs: vec![TagAttr {
                        name: "src".to_owned(),
                        value: Some("test".to_owned()),
                    }],
                    self_closing: true
                }),
                new_line_text(),
                Token::OpenTag(OpenTag {
                    name: "custom".to_owned(),
                    tag_attrs: vec![TagAttr {
                        name: "attr1".to_owned(),
                        value: None,
                    }],
                    self_closing: false
                }),
                Token::CloseTag("custom".to_owned()),
                new_line_text(),
                Token::CloseTag("body".to_owned()),
                new_line_text(),
                Token::CloseTag("html".to_owned()),
            ]
            .as_ref()),
        );
    }
}
