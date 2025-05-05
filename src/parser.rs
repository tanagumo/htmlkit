use regex::Regex;
use std::{borrow::Cow, error::Error as StdError, fmt::Display, iter::Peekable, mem, str::Chars};

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
    src: Peekable<Chars<'a>>,
    state: TokenizerState,
    is_end_tag: bool,
    tag_name: String,
    tag_attr_name: String,
    tag_value: String,
    text: String,
    re_for_tag_name: Regex,
    tokens: Vec<Token>,
    loc: Loc,
    open_tag_builder: Option<OpenTagBuilder>,
    comment: String,
}

type TokenizeResult<T> = Result<T, WithLoc<TokenizeError<'static>>>;

impl<'a> Tokenizer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src: src.chars().peekable(),
            state: TokenizerState::Text,
            is_end_tag: false,
            tag_name: String::new(),
            tag_attr_name: String::new(),
            tag_value: String::new(),
            text: String::new(),
            re_for_tag_name: Regex::new(r"^[a-z]+[[:alnum:]]*$").unwrap(),
            tokens: vec![],
            loc: Loc::default(),
            open_tag_builder: None,
            comment: String::new(),
        }
    }

    pub fn tokenize(mut self) -> TokenizeResult<Vec<Token>> {
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

        Ok(self.tokens)
    }

    fn handle_after_tag_name(&mut self, ch: char) -> TokenizeResult<()> {
        match ch {
            '>' => {
                self.state = TokenizerState::Text;
            }
            _ => {
                if !ch.is_whitespace() {
                    return Err(WithLoc::new(
                        TokenizeError::MalformedEndTag(Cow::Borrowed("end tag can only have name")),
                        self.loc,
                    ));
                }
            }
        }
        self.advance();
        Ok(())
    }

    fn handle_after_tag_attr(&mut self, ch: char) -> TokenizeResult<()> {
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

    fn handle_after_tag_value(&mut self, ch: char) -> TokenizeResult<()> {
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

    fn handle_before_tag_attr(&mut self, ch: char) -> TokenizeResult<()> {
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

    fn handle_before_tag_value(&mut self, ch: char) -> TokenizeResult<()> {
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

    fn handle_comment(&mut self, ch: char) -> TokenizeResult<()> {
        if ch == '-' {
            if self.starts_with("-->") {
                self.advance();
                self.advance();
                self.advance();
                self.tokens
                    .push(Token::Comment(mem::take(&mut self.comment)));
                self.state = TokenizerState::Text;
            } else {
                return Err(WithLoc::new(TokenizeError::MalformedCommentTag, self.loc));
            }
        } else {
            self.comment.push(ch);
            self.advance();
        }
        Ok(())
    }

    fn handle_doc_type(&mut self, ch: char) -> TokenizeResult<()> {
        if ch == '>' {
            self.tokens.push(Token::DocTypeTag);
            self.state = TokenizerState::Text;
        }
        self.advance();
        Ok(())
    }

    fn handle_before_doc_type_or_comment(&mut self, _ch: char) -> TokenizeResult<()> {
        if self.starts_with("-") {
            if !self.starts_with("--") {
                return Err(WithLoc::new(TokenizeError::MalformedCommentTag, self.loc));
            }

            self.advance();
            self.advance();
            self.state = TokenizerState::Comment;
        } else {
            if !self.starts_with_case_insensitive("DOCTYPE") {
                return Err(WithLoc::new(TokenizeError::MalformedDocTypeTag, self.loc));
            }
            self.state = TokenizerState::DocType;
            for _ in 0..7 {
                self.advance();
            }
        }
        Ok(())
    }

    fn handle_end_tag_open(&mut self, ch: char) -> TokenizeResult<()> {
        self.state = TokenizerState::TagName;
        self.tag_name.push(ch);
        self.advance();
        Ok(())
    }

    fn handle_self_closing_tag_slash(&mut self, ch: char) -> TokenizeResult<()> {
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
                        self.loc,
                    ));
                }
            }
        }

        self.advance();
        Ok(())
    }

    fn handle_tag_attr(&mut self, ch: char) -> TokenizeResult<()> {
        if ch == '>' || ch == '=' || ch.is_whitespace() {
            let tag_attr_name = mem::take(&mut self.tag_attr_name);
            if let None = self.re_for_tag_name.captures(&tag_attr_name) {
                return Err(WithLoc::new(
                    TokenizeError::InvalidTagAttrName(Cow::Owned(tag_attr_name)),
                    self.loc,
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

    fn handle_tag_name(&mut self, ch: char) -> TokenizeResult<()> {
        if ch == '>' || ch.is_whitespace() {
            let token_finalized = ch == '>';

            let tag = mem::take(&mut self.tag_name);
            if let None = self.re_for_tag_name.captures(&tag) {
                return Err(WithLoc::new(
                    TokenizeError::InvalidTagName(Cow::Owned(tag)),
                    self.loc,
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

    fn handle_tag_open(&mut self, ch: char) -> TokenizeResult<()> {
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

    fn handle_tag_value(&mut self, ch: char) -> TokenizeResult<()> {
        if ch == '"' {
            let tag_value = mem::take(&mut self.tag_value);
            self.open_tag_builder
                .as_mut()
                .unwrap()
                .set_attr_value(tag_value)
                .map_err(|e| WithLoc::new(e, self.loc))?;
            self.state = TokenizerState::AfterTagValue;
        } else {
            self.tag_value.push(ch);
        }

        self.advance();
        Ok(())
    }

    fn handle_text(&mut self, ch: char) -> TokenizeResult<()> {
        if ch == '<' {
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

    fn advance(&mut self) {
        if let Some('\n') = self.src.next() {
            self.loc.break_line();
        } else {
            self.loc.advance();
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.src.peek().map(|ch| *ch)
    }

    fn starts_with(&self, target: impl AsRef<str>) -> bool {
        let target = target.as_ref();
        if target.is_empty() {
            return true;
        }

        let mut cloned = self.src.clone();

        let mut ret = true;
        for ch in target.chars() {
            if let Some(&v) = cloned.peek() {
                if v != ch {
                    ret = false;
                    break;
                } else {
                    cloned.next();
                }
            } else {
                ret = false;
                break;
            }
        }
        ret
    }

    fn starts_with_case_insensitive(&self, target: impl AsRef<str>) -> bool {
        let target = target.as_ref();
        if target.is_empty() {
            return true;
        }

        let mut cloned = self.src.clone();

        let mut ret = true;
        for ch in target.chars() {
            if let Some(v) = cloned.peek() {
                if !v.eq_ignore_ascii_case(&ch) {
                    ret = false;
                    break;
                } else {
                    cloned.next();
                }
            } else {
                ret = false;
                break;
            }
        }
        ret
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
            ])
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
            ])
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
            ])
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
            ])
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
            ])
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
            ])
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
            ])
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
            ])
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
            ])
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
            }),])
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
            }),])
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
            }),])
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
            }),])
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
            }),])
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
            }),])
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
        assert_eq!(tokenizer.starts_with(""), true);
        assert_eq!(tokenizer.starts_with("t"), true);
        assert_eq!(tokenizer.starts_with("t1"), true);
        assert_eq!(tokenizer.starts_with("t12"), true);
        assert_eq!(tokenizer.starts_with("t123"), true);
        assert_eq!(tokenizer.starts_with("t1234"), false);
    }

    #[test]
    fn test_comment_tag() {
        assert_eq!(
            Tokenizer::new("<!--comment-->").tokenize(),
            Ok(vec![Token::Comment("comment".to_owned()),])
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
            ),])
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
            Ok(vec![Token::DocTypeTag]),
        );

        // allow case insensitive "doctype"
        assert_eq!(
            Tokenizer::new("<!Doctype>").tokenize(),
            Ok(vec![Token::DocTypeTag]),
        );

        assert_eq!(
            Tokenizer::new("test1<!Doctype>test2").tokenize(),
            Ok(vec![
                Token::Text("test1".to_owned()),
                Token::DocTypeTag,
                Token::Text("test2".to_owned()),
            ]),
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
            ]),
        );
    }
}
