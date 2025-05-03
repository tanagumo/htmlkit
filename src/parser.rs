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
    Text { content: String, ignore_hint: bool },
    CloseTag(String),
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct Pos {
    row: u32,
    col: u16,
}

impl Pos {
    fn advance(&mut self) {
        self.col += 1;
    }

    fn break_line(&mut self) {
        self.row += 1;
        self.col = 0;
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct WithPos<T> {
    value: T,
    pos: Pos,
}

impl<T> WithPos<T> {
    fn new(value: T, pos: Pos) -> Self {
        Self { value, pos }
    }
}

impl<T: Display> Display for WithPos<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}. (row: {}, col: {})",
            self.value, self.pos.row, self.pos.col
        )
    }
}

impl<T: StdError + Send + Sync + 'static> StdError for WithPos<T> {}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum TokenizerState {
    AfterEndTagName,
    AfterTagAttr,
    AfterTagValue,
    BeforeFirstTag,
    BeforeTagAttr,
    BeforeTagValue,
    Data,
    EndTagOpen,
    IgnoreUntilGt,
    SelfClosingTagSlash,
    TagAttr,
    TagName,
    TagOpen,
    TagValue,
}

#[derive(Debug)]
pub struct Tokenizer<'a> {
    src: Peekable<Chars<'a>>,
    state_before_ignore: TokenizerState,
    state: TokenizerState,
    is_end_tag: bool,
    tag_name: String,
    tag_attr_name: String,
    tag_value: String,
    text: String,
    re_for_tag_name: Regex,
    tokens: Vec<Token>,
    pos: Pos,
    open_tag_builder: Option<OpenTagBuilder>,
}

type TokenizeResult<T> = Result<T, WithPos<TokenizeError<'static>>>;

impl<'a> Tokenizer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src: src.chars().peekable(),
            state_before_ignore: TokenizerState::BeforeFirstTag,
            state: TokenizerState::BeforeFirstTag,
            is_end_tag: false,
            tag_name: String::new(),
            tag_attr_name: String::new(),
            tag_value: String::new(),
            text: String::new(),
            re_for_tag_name: Regex::new(r"^[a-z]+[[:alnum:]]*$").unwrap(),
            tokens: vec![],
            pos: Pos::default(),
            open_tag_builder: None,
        }
    }

    pub fn tokenize(mut self) -> TokenizeResult<Vec<Token>> {
        while let Some(ch) = self.peek() {
            match self.state {
                TokenizerState::AfterEndTagName => self.handle_after_tag_name(ch)?,
                TokenizerState::AfterTagAttr => self.handle_after_tag_attr(ch)?,
                TokenizerState::AfterTagValue => self.handle_after_tag_value(ch)?,
                TokenizerState::BeforeFirstTag => self.handle_before_first_tag(ch)?,
                TokenizerState::BeforeTagAttr => self.handle_before_tag_attr(ch)?,
                TokenizerState::BeforeTagValue => self.handle_before_tag_value(ch)?,
                TokenizerState::Data => self.handle_data(ch)?,
                TokenizerState::EndTagOpen => self.handle_end_tag_open(ch)?,
                TokenizerState::IgnoreUntilGt => self.handle_ignore_until_gt(ch)?,
                TokenizerState::SelfClosingTagSlash => self.handle_self_closing_tag_slash(ch)?,
                TokenizerState::TagAttr => self.handle_tag_attr(ch)?,
                TokenizerState::TagName => self.handle_tag_name(ch)?,
                TokenizerState::TagOpen => self.handle_tag_open(ch)?,
                TokenizerState::TagValue => self.handle_tag_value(ch)?,
            }
        }

        Ok(self.tokens)
    }

    fn handle_after_tag_name(&mut self, ch: char) -> TokenizeResult<()> {
        match ch {
            '>' => {
                self.state = TokenizerState::Data;
            }
            _ => {
                if !ch.is_whitespace() {
                    return Err(WithPos::new(
                        TokenizeError::MalformedEndTag(Cow::Borrowed("end tag can only have name")),
                        self.pos,
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
                self.state = TokenizerState::Data;
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
                self.state = TokenizerState::Data;
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

    fn handle_before_first_tag(&mut self, ch: char) -> TokenizeResult<()> {
        if ch == '<' {
            self.state = TokenizerState::TagOpen;
        }
        self.advance();

        if let Some('!') = self.peek() {
            self.text.push('<');
            self.state_before_ignore = TokenizerState::BeforeFirstTag;
            self.state = TokenizerState::IgnoreUntilGt;
        }
        Ok(())
    }

    fn handle_before_tag_attr(&mut self, ch: char) -> TokenizeResult<()> {
        match ch {
            '>' => {
                self.finalize_open_tag(false);
                self.state = TokenizerState::Data;
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

    fn handle_data(&mut self, ch: char) -> TokenizeResult<()> {
        if ch != '<' {
            self.text.push(ch);
            self.advance();
        } else {
            self.advance();

            match self.peek() {
                Some('!') => {
                    self.text.push('<');
                    self.state_before_ignore = self.state;
                    self.state = TokenizerState::IgnoreUntilGt;
                }
                Some(_) => {
                    self.state = TokenizerState::TagOpen;
                    if !self.text.is_empty() {
                        self.tokens.push(Token::Text {
                            content: mem::take(&mut self.text),
                            ignore_hint: false,
                        });
                    }
                }
                _ => {}
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

    fn handle_ignore_until_gt(&mut self, ch: char) -> TokenizeResult<()> {
        self.text.push(ch);
        if ch == '>' {
            self.tokens.push(Token::Text {
                content: mem::take(&mut self.text),
                ignore_hint: self.state_before_ignore == TokenizerState::BeforeFirstTag,
            });
            self.state = self.state_before_ignore;
        }

        self.advance();
        Ok(())
    }

    fn handle_self_closing_tag_slash(&mut self, ch: char) -> TokenizeResult<()> {
        match ch {
            '>' => {
                self.finalize_open_tag(true);
                self.state = TokenizerState::Data;
            }
            _ => {
                if !ch.is_whitespace() {
                    return Err(WithPos::new(
                        TokenizeError::MalformedSelfClosingTag(Cow::Borrowed(
                            "self closing tag does not accept any character after slash",
                        )),
                        self.pos,
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
                return Err(WithPos::new(
                    TokenizeError::InvalidTagAttrName(Cow::Owned(tag_attr_name)),
                    self.pos,
                ));
            }
            self.open_tag_builder
                .as_mut()
                .unwrap()
                .add_attr_name(tag_attr_name);
            self.state = if ch == '>' {
                self.finalize_open_tag(false);
                TokenizerState::Data
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
                return Err(WithPos::new(
                    TokenizeError::InvalidTagName(Cow::Owned(tag)),
                    self.pos,
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
                TokenizerState::Data
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
        if ch == '/' {
            self.state = TokenizerState::EndTagOpen;
            self.is_end_tag = true;
        } else {
            self.state = TokenizerState::TagName;
            self.tag_name.push(ch);
            self.is_end_tag = false;
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
                .map_err(|e| WithPos::new(e, self.pos))?;
            self.state = TokenizerState::AfterTagValue;
        } else {
            self.tag_value.push(ch);
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
            self.pos.break_line();
        } else {
            self.pos.advance();
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.src.peek().map(|ch| *ch)
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
                Token::Text {
                    content: "abc>hoge".to_owned(),
                    ignore_hint: false
                },
                Token::CloseTag("tag".to_owned())
            ])
        );
    }

    #[test]
    fn test_simple_tag_with_text_before_first_tag() {
        // ignore any characters before first tag
        assert_eq!(
            Tokenizer::new("oajofjaj <! > <tag></tag>").tokenize(),
            Ok(vec![
                Token::Text {
                    content: "<! >".to_owned(),
                    ignore_hint: true,
                },
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
    fn test_simple_tag_with_unclosing() {
        // if "<!" appears, read until ">" will appear.
        assert_eq!(
            Tokenizer::new("<tag>abc>hoge<!</tag>").tokenize(),
            Ok(vec![
                Token::OpenTag(OpenTag {
                    name: "tag".to_owned(),
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Token::Text {
                    content: "abc>hoge<!</tag>".to_owned(),
                    ignore_hint: false
                },
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
                Token::Text {
                    content: "before <!-- comment -->".to_owned(),
                    ignore_hint: false
                },
                Token::Text {
                    content: " after".to_owned(),
                    ignore_hint: false
                },
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
            Err(WithPos::new(
                TokenizeError::InvalidTagName(Cow::Borrowed("2a")),
                Pos { row: 0, col: 3 }
            ))
        );

        assert_eq!(
            Tokenizer::new("<tag></3b>").tokenize(),
            Err(WithPos::new(
                TokenizeError::InvalidTagName(Cow::Borrowed("3b")),
                Pos { row: 0, col: 9 }
            ))
        );
    }

    #[test]
    fn test_invalid_tag_name_with_line_break() {
        assert_eq!(
            Tokenizer::new("<tag>\n</999999a>").tokenize(),
            Err(WithPos::new(
                TokenizeError::InvalidTagName(Cow::Borrowed("999999a")),
                Pos { row: 1, col: 9 }
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
            Err(WithPos::new(
                TokenizeError::InvalidTagAttrName(Cow::Borrowed("3attr")),
                Pos { row: 0, col: 10 }
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
            Err(WithPos::new(
                TokenizeError::MalformedEndTag(Cow::Borrowed("end tag can only have name")),
                Pos { row: 1, col: 11 }
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
            Err(WithPos::new(
                TokenizeError::MalformedSelfClosingTag(Cow::Borrowed(
                    "self closing tag does not accept any character after slash"
                )),
                Pos { row: 0, col: 34 }
            ))
        );
    }
}
