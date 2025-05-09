use regex::Regex;
use std::{
    borrow::Cow,
    error::Error as StdError,
    fmt::Display,
    iter::Peekable,
    mem,
    ops::{Range, RangeFrom, RangeFull, RangeTo},
    str::Chars,
    sync::OnceLock,
};

const TAG_NAME_RE_STR: &'static str = r"^[a-z][a-z0-9.-]*(-[a-z0-9.-]+)?$";
const TAG_ATTR_RE_STR: &'static str = r"^[a-zA-Z_:][a-zA-Z0-9:._-]*$";

const TAG_NAME_RE: OnceLock<Regex> = OnceLock::new();
const TAG_ATTR_RE: OnceLock<Regex> = OnceLock::new();

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct Span(usize, usize);

impl From<(usize, usize)> for Span {
    fn from(value: (usize, usize)) -> Self {
        Self(value.0, value.1)
    }
}

impl Into<Range<usize>> for Span {
    fn into(self) -> Range<usize> {
        self.0..self.1
    }
}

#[derive(Debug)]
struct RangeWrapper(Option<usize>, Option<usize>);

impl From<Range<usize>> for RangeWrapper {
    fn from(value: Range<usize>) -> Self {
        Self(Some(value.start), Some(value.end))
    }
}

impl From<RangeFrom<usize>> for RangeWrapper {
    fn from(value: RangeFrom<usize>) -> Self {
        Self(Some(value.start), None)
    }
}

impl From<RangeTo<usize>> for RangeWrapper {
    fn from(value: RangeTo<usize>) -> Self {
        Self(None, Some(value.end))
    }
}

impl From<RangeFull> for RangeWrapper {
    fn from(_: RangeFull) -> Self {
        Self(None, None)
    }
}

/// A span that starts with the first recorded position
/// and keeps updating its end position as input progresses.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
struct GrowingSpan(Option<usize>, Option<usize>);

impl GrowingSpan {
    fn set(&mut self, value: usize) {
        if self.0.is_none() {
            self.0 = Some(value);
        } else {
            self.1 = Some(value);
        }
    }
}

impl From<GrowingSpan> for Span {
    fn from(value: GrowingSpan) -> Self {
        Self(value.0.unwrap(), value.1.unwrap())
    }
}

impl From<GrowingSpan> for Range<usize> {
    fn from(value: GrowingSpan) -> Self {
        value.0.unwrap()..value.1.unwrap()
    }
}

impl From<GrowingSpan> for RangeWrapper {
    fn from(value: GrowingSpan) -> Self {
        Self(Some(value.0.unwrap()), Some(value.1.unwrap()))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TagAttrError<'a> {
    ValueAlreadySet(&'a str),
    AttrNotFound,
}

impl<'a> Display for TagAttrError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TagAttrError::ValueAlreadySet(name) => write!(
                f,
                "the value for the tag attribute `{}` is already set",
                name
            ),
            TagAttrError::AttrNotFound => write!(f, "tag attribute is not yet set"),
        }
    }
}

impl<'a> StdError for TagAttrError<'a> {}

#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TokenizeError<'a> {
    MalformedSelfClosingTag(Cow<'a, str>),
    MalformedCommentTag,
    MalformedDocTypeTag,
    TagAttrError(TagAttrError<'a>),
}

impl<'a> Display for TokenizeError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            TokenizeError::MalformedSelfClosingTag(reason) => {
                format!("malformed self closing tag. ({})", reason)
            }
            TokenizeError::MalformedCommentTag => format!("malformed comment tag"),
            TokenizeError::MalformedDocTypeTag => format!("malformed doctype tag"),
            TokenizeError::TagAttrError(err) => format!("{}", err),
        };

        write!(f, "tokenize error. ({})", message)
    }
}

impl<'a> StdError for TokenizeError<'a> {}

#[derive(Debug, PartialEq, Eq)]
pub struct WithSpan<T> {
    value: T,
    span: Span,
}

impl<T> WithSpan<T> {
    fn new(value: T, span: Span) -> Self {
        Self { value, span }
    }
}

impl<T> Display for WithSpan<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} (span=({}, {}))",
            self.value, self.span.0, self.span.1
        )
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TagAttr<'a> {
    name: &'a str,
    value: Option<&'a str>,
}

impl<'a> Display for TagAttr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = self.value {
            write!(f, r#"attr(name={}, value="{}")"#, self.name, v)
        } else {
            write!(f, "attr(name={})", self.name)
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct OpenTag<'a> {
    name: &'a str,
    tag_attrs: Vec<TagAttr<'a>>,
    self_closing: bool,
}

impl<'a> Display for OpenTag<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tag_attrs = self
            .tag_attrs
            .iter()
            .map(|ta| format!("{}", ta))
            .collect::<Vec<_>>()
            .join(", ");

        write!(
            f,
            "tag(name={}, attrs={}, self_closing={})",
            self.name, tag_attrs, self.self_closing
        )
    }
}

#[derive(Debug)]
struct OpenTagBuilder<'a> {
    name_span: Option<Span>,
    tag_attrs: Vec<TagAttr<'a>>,
}

impl<'a> OpenTagBuilder<'a> {
    fn new() -> Self {
        Self {
            name_span: None,
            tag_attrs: Vec::with_capacity(128),
        }
    }

    fn set_name_span(&mut self, name_span: impl Into<Span>) {
        if self.name_span.is_some() {
            panic!("`name_span` is already set");
        }
        self.name_span = Some(name_span.into());
    }

    fn add_attr_name(&mut self, name: &'a str) {
        let attr = TagAttr { name, value: None };
        self.tag_attrs.push(attr);
    }

    fn set_attr_value(&mut self, value: &'a str) -> Result<&mut Self, TokenizeError<'a>> {
        if let Some(attr) = self.tag_attrs.last_mut() {
            if attr.value.is_some() {
                Err(TokenizeError::TagAttrError(TagAttrError::ValueAlreadySet(
                    attr.name,
                )))
            } else {
                attr.value = Some(value);
                Ok(self)
            }
        } else {
            Err(TokenizeError::TagAttrError(TagAttrError::AttrNotFound))
        }
    }

    fn build(&mut self, input: &Input<'a>, self_closing: bool) -> OpenTag<'a> {
        let ns = self.name_span.take().unwrap();
        OpenTag {
            name: &input.src[ns.0..ns.1],
            tag_attrs: mem::take(&mut self.tag_attrs),
            self_closing,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Token<'a> {
    OpenTag(OpenTag<'a>),
    Comment(&'a str),
    Text(&'a str),
    CloseTag(&'a str),
    DocTypeTag,
}

#[derive(Debug)]
struct Input<'a> {
    src: &'a str,
    peekable: Peekable<Chars<'a>>,
    pos: usize,
}

impl<'a> Input<'a> {
    fn new(src: &'a str) -> Self {
        let chars = src.chars();
        Self {
            src,
            peekable: chars.peekable(),
            pos: 0,
        }
    }

    fn advance(&mut self) -> bool {
        match self.peekable.next() {
            Some(v) => {
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

    fn read_str(&self, range: impl Into<RangeWrapper>) -> &'a str {
        let range = range.into();
        match (range.0, range.1) {
            (Some(start), Some(end)) => &self.src[start..end],
            (Some(start), None) => &self.src[start..],
            (None, Some(end)) => &self.src[..end],
            (None, None) => &self.src[..],
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum TokenizerState {
    AfterComment,
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
    state: TokenizerState,
    is_end_tag: bool,
    tag_name_span: GrowingSpan,
    tag_attr_name_span: GrowingSpan,
    tag_value_span: GrowingSpan,
    text_pos: usize,
    comment_span: GrowingSpan,
    tokens: Vec<WithSpan<Token<'a>>>,
    open_tag_builder: OpenTagBuilder<'a>,
    tag_start_pos: usize,
}

impl<'a> Tokenizer<'a> {
    pub fn new(src: &'a str) -> Self {
        let _ = TAG_NAME_RE.get_or_init(|| Regex::new(TAG_NAME_RE_STR).unwrap());
        let _ = TAG_ATTR_RE.get_or_init(|| Regex::new(TAG_ATTR_RE_STR).unwrap());

        Self {
            input: Input::new(src),
            state: TokenizerState::Text,
            is_end_tag: false,
            tag_name_span: GrowingSpan::default(),
            tag_attr_name_span: GrowingSpan::default(),
            comment_span: GrowingSpan::default(),
            tag_value_span: GrowingSpan::default(),
            text_pos: 0,
            tokens: vec![],
            open_tag_builder: OpenTagBuilder::new(),
            tag_start_pos: 0,
        }
    }

    pub fn tokenize(&mut self) -> &[WithSpan<Token<'a>>] {
        while let Some(ch) = self.input.peek() {
            match self.state {
                TokenizerState::AfterComment => self.handle_after_comment(ch),
                TokenizerState::AfterEndTagName => self.handle_after_end_tag_name(ch),
                TokenizerState::AfterTagAttr => self.handle_after_tag_attr(ch),
                TokenizerState::AfterTagValue => self.handle_after_tag_value(ch),
                TokenizerState::BeforeTagAttr => self.handle_before_tag_attr(ch),
                TokenizerState::BeforeTagValue => self.handle_before_tag_value(ch),
                TokenizerState::Comment => self.handle_comment(ch),
                TokenizerState::DocType => self.handle_doc_type(ch),
                TokenizerState::DocTypeOrComment => self.handle_before_doc_type_or_comment(ch),
                TokenizerState::EndTagOpen => self.handle_end_tag_open(ch),
                TokenizerState::SelfClosingTagSlash => self.handle_self_closing_tag_slash(ch),
                TokenizerState::TagAttr => self.handle_tag_attr(ch),
                TokenizerState::TagName => self.handle_tag_name(ch),
                TokenizerState::TagOpen => self.handle_tag_open(ch),
                TokenizerState::TagValue => self.handle_tag_value(ch),
                TokenizerState::Text => self.handle_text(ch),
            }
        }

        let remaining = self.input.read_str(self.text_pos..);
        if !remaining.is_empty() {
            let span = Span(self.next_start_pos(), self.input.pos - 1);
            self.push_token(Token::Text(remaining), span);
        }
        &self.tokens
    }

    fn handle_after_comment(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        } else if ch == '>' {
            self.state = TokenizerState::Text;
        }
        self.input.advance();
    }

    fn handle_after_end_tag_name(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        } else if ch == '>' {
            let tag_name = self.input.read_str(self.tag_name_span);
            self.finalize_close_tag(tag_name);
            self.state = TokenizerState::Text;
        } else if !ch.is_whitespace() {
            self.state = TokenizerState::Text;
        }
        self.input.advance();
    }

    fn handle_after_tag_attr(&mut self, ch: char) {
        match ch {
            '<' => {
                self.prepare_for_tag_open();
            }
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
                self.tag_attr_name_span.set(self.input.pos);
                self.state = TokenizerState::TagAttr;
            }
            _ => {}
        }

        self.input.advance();
    }

    fn handle_after_tag_value(&mut self, ch: char) {
        match ch {
            '<' => {
                self.prepare_for_tag_open();
            }
            '>' => {
                self.finalize_open_tag(false);
                self.state = TokenizerState::Text;
            }
            '/' => {
                self.state = TokenizerState::SelfClosingTagSlash;
            }
            ch => {
                if !ch.is_whitespace() {
                    self.tag_attr_name_span.set(self.input.pos);
                    self.state = TokenizerState::TagAttr;
                }
            }
        }

        self.input.advance();
    }

    fn handle_before_tag_attr(&mut self, ch: char) {
        match ch {
            '<' => {
                self.prepare_for_tag_open();
            }
            '>' => {
                self.finalize_open_tag(false);
                self.state = TokenizerState::Text;
            }
            '/' => {
                self.state = TokenizerState::SelfClosingTagSlash;
            }
            ch if !ch.is_whitespace() => {
                self.tag_attr_name_span.set(self.input.pos);
                self.state = TokenizerState::TagAttr;
            }
            _ => {}
        }

        self.input.advance();
    }

    fn handle_before_tag_value(&mut self, ch: char) {
        match ch {
            '<' => {
                self.prepare_for_tag_open();
            }
            '"' => {}
            ch => {
                if !ch.is_whitespace() {
                    self.tag_value_span.set(self.input.pos);
                    self.state = TokenizerState::TagValue;
                }
            }
        }

        self.input.advance();
    }

    fn handle_comment(&mut self, ch: char) {
        if ch == '-' {
            if !self.input.remaining().starts_with("-->") {
                self.state = TokenizerState::Text;
            } else {
                self.finalize_text_if_exist(self.tag_start_pos);
                self.text_pos = self.input.pos + 3;

                self.comment_span.set(self.input.pos);
                let comment = self.input.read_str(self.comment_span);
                self.comment_span = GrowingSpan::default();
                let span = Span(self.next_start_pos(), self.input.pos + 2);
                self.push_token(Token::Comment(comment), span);
                self.state = TokenizerState::AfterComment;
            }
        }
        self.input.advance();
    }

    fn handle_doc_type(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        } else if ch == '>' {
            self.finalize_doctype();
            self.state = TokenizerState::Text;
        }
        self.input.advance();
    }

    fn handle_before_doc_type_or_comment(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        } else if self.input.starts_with("-") {
            if !self.input.starts_with("--") {
                self.state = TokenizerState::Text;
                self.input.advance();
                return;
            }

            self.input.advance();
            self.input.advance();
            self.state = TokenizerState::Comment;
            self.comment_span.set(self.input.pos);
        } else {
            if !self.input.starts_with_case_insensitive("DOCTYPE") {
                self.state = TokenizerState::Text;
                self.input.advance();
                return;
            }
            self.state = TokenizerState::DocType;
            for _ in 0..7 {
                self.input.advance();
            }
        }
    }

    fn handle_end_tag_open(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        } else {
            self.state = TokenizerState::TagName;
            self.tag_name_span.set(self.input.pos);
        }
        self.input.advance();
    }

    fn handle_self_closing_tag_slash(&mut self, ch: char) {
        match ch {
            '<' => {
                self.prepare_for_tag_open();
            }
            '>' => {
                self.finalize_open_tag(true);
                self.state = TokenizerState::Text;
            }
            _ => {
                if !ch.is_whitespace() {
                    self.state = TokenizerState::Text;
                }
            }
        }

        self.input.advance();
    }

    fn handle_tag_attr(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        } else if ch == '>' || ch == '=' || ch.is_whitespace() {
            self.tag_attr_name_span.set(self.input.pos);
            let tag_attr_name = self.input.read_str(self.tag_attr_name_span);

            if !TAG_ATTR_RE
                .get_or_init(|| Regex::new(TAG_ATTR_RE_STR).unwrap())
                .is_match(&tag_attr_name)
            {
                self.state = TokenizerState::Text;
                self.input.advance();
                return;
            }

            self.open_tag_builder.add_attr_name(tag_attr_name.into());
            self.tag_attr_name_span = GrowingSpan::default();
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
            self.tag_attr_name_span.set(self.input.pos);
        }

        self.input.advance();
    }

    fn handle_tag_name(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        } else if ch == '>' || ch == '/' || ch.is_whitespace() {
            self.tag_name_span.set(self.input.pos);
            let token_finalized = ch == '>';
            let name_start_pos = self.tag_start_pos + if self.is_end_tag { 2 } else { 1 };

            let tag_name = self.input.read_str(name_start_pos..self.input.pos);
            if !TAG_NAME_RE
                .get_or_init(|| Regex::new(TAG_NAME_RE_STR).unwrap())
                .is_match(tag_name)
            {
                self.state = TokenizerState::Text;
                return;
            }

            match (self.is_end_tag, token_finalized) {
                (true, true) => {
                    self.finalize_close_tag(tag_name);
                }
                (false, true) => {
                    self.open_tag_builder.set_name_span(self.tag_name_span);
                    self.finalize_open_tag(false);
                }
                (false, false) => {
                    self.open_tag_builder.set_name_span(self.tag_name_span);
                }
                (true, false) => {}
            }

            self.state = if token_finalized {
                TokenizerState::Text
            } else if self.is_end_tag {
                TokenizerState::AfterEndTagName
            } else if ch == '/' {
                TokenizerState::SelfClosingTagSlash
            } else {
                TokenizerState::BeforeTagAttr
            };
        }

        self.input.advance();
    }

    fn handle_tag_open(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        } else if ch == '!' {
            self.state = TokenizerState::DocTypeOrComment;
        } else {
            if ch == '/' {
                self.state = TokenizerState::EndTagOpen;
                self.is_end_tag = true;
                self.tag_name_span.set(self.input.pos + 1);
            } else {
                self.state = TokenizerState::TagName;
                self.is_end_tag = false;
                self.tag_name_span.set(self.input.pos);
            }
        }
        self.input.advance();
    }

    fn handle_tag_value(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        } else if ch == '"' {
            self.tag_value_span.set(self.input.pos);
            let tag_value = self.input.read_str(self.tag_value_span);
            self.tag_value_span = GrowingSpan::default();

            if let Err(e) = self.open_tag_builder.set_attr_value(tag_value) {
                match e {
                    TokenizeError::TagAttrError(_) => {
                        self.state = TokenizerState::Text;
                        self.input.advance();
                        return;
                    }
                    _ => {
                        unreachable!("the error set_attr_value returns should be TagAttrError")
                    }
                }
            }

            self.state = TokenizerState::AfterTagValue;
        } else {
            self.tag_value_span.set(self.input.pos);
        }

        self.input.advance();
    }

    fn handle_text(&mut self, ch: char) {
        if ch == '<' {
            self.prepare_for_tag_open();
        }
        self.input.advance();
    }

    fn finalize_open_tag(&mut self, self_closing: bool) {
        self.finalize_text_if_exist(self.tag_start_pos);
        self.text_pos = self.input.pos + 1;
        let token = Token::OpenTag(self.open_tag_builder.build(&self.input, self_closing));
        self.push_token(token, Span(self.next_start_pos(), self.input.pos));
        self.tag_name_span = GrowingSpan::default();
    }

    fn finalize_close_tag(&mut self, tag_name: &'a str) {
        self.finalize_text_if_exist(self.tag_start_pos);
        self.text_pos = self.input.pos + 1;
        let span = Span(self.next_start_pos(), self.input.pos);
        self.push_token(Token::CloseTag(tag_name), span);
        self.tag_name_span = GrowingSpan::default();
    }

    fn finalize_doctype(&mut self) {
        self.finalize_text_if_exist(self.tag_start_pos);
        self.text_pos = self.input.pos + 1;
        let span = Span(self.next_start_pos(), self.input.pos);
        self.push_token(Token::DocTypeTag, span);
    }

    fn finalize_text_if_exist(&mut self, end_pos: usize) {
        let text = self.input.read_str(self.text_pos..end_pos);
        if !text.is_empty() {
            let span = Span(self.next_start_pos(), end_pos - 1);
            self.push_token(Token::Text(text), span);
        }
    }

    fn push_token(&mut self, token: Token<'a>, span: impl Into<Span>) {
        self.tokens.push(WithSpan::new(token, span.into()));
    }

    fn next_start_pos(&self) -> usize {
        if let Some(t) = self.tokens.last() {
            t.span.1 + 1
        } else {
            0
        }
    }

    fn prepare_for_tag_open(&mut self) {
        self.tag_start_pos = self.input.pos;
        self.state = TokenizerState::TagOpen;
        self.tag_name_span = Default::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_tokens_are_contiguous(tokens: &[WithSpan<Token<'_>>]) {
        for pair in tokens.windows(2) {
            let t1 = &pair[0];
            let t2 = &pair[1];
            assert_eq!(t1.span.1 + 1, t2.span.0);
        }
    }

    fn assert_tokens<'a>(actual: &[WithSpan<Token<'a>>], expected: &[WithSpan<Token<'a>>]) {
        assert_eq!(actual, expected);
        assert_tokens_are_contiguous(actual);
    }

    #[test]
    fn test_input() {
        let mut input = Input::new("tあ\nz");
        input.advance();
        assert_eq!(input.pos, 1);
        assert_eq!(input.remaining(), "あ\nz");

        input.advance();
        assert_eq!(input.pos, 4);
        assert_eq!(input.remaining(), "\nz");

        input.advance();
        assert_eq!(input.pos, 5);
        assert_eq!(input.remaining(), "z");

        input.advance();
        assert_eq!(input.pos, 6);
        assert_eq!(input.remaining(), "");

        input.advance();
        assert_eq!(input.pos, 6);
        assert_eq!(input.remaining(), "");
    }

    fn with_span<'a>(token: Token<'a>, span: Span) -> WithSpan<Token<'a>> {
        WithSpan::new(token, span)
    }

    #[test]
    fn test_tag() {
        assert_tokens(
            Tokenizer::new("<tag>").tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Span(0, 4),
            )],
        );

        assert_tokens(
            Tokenizer::new("<tag attr>").tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![TagAttr {
                        name: "attr",
                        value: None,
                    }],
                    self_closing: false,
                }),
                Span(0, 9),
            )],
        );

        assert_tokens(
            Tokenizer::new("<tag attr1  attr2 >").tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![
                        TagAttr {
                            name: "attr1",
                            value: None,
                        },
                        TagAttr {
                            name: "attr2",
                            value: None,
                        },
                    ],
                    self_closing: false,
                }),
                Span(0, 18),
            )],
        );

        assert_tokens(
            Tokenizer::new(r#"<tag attr1="value1"  attr2 =       "value2" >"#).tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![
                        TagAttr {
                            name: "attr1",
                            value: Some("value1"),
                        },
                        TagAttr {
                            name: "attr2",
                            value: Some("value2"),
                        },
                    ],
                    self_closing: false,
                }),
                Span(0, 44),
            )],
        );

        assert_tokens(
            // text + tag + text
            Tokenizer::new(r#"before<tag attr1="value1"  attr2 =       "value2" >after"#)
                .tokenize(),
            &vec![
                with_span(Token::Text("before"), Span(0, 5)),
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "tag",
                        tag_attrs: vec![
                            TagAttr {
                                name: "attr1",
                                value: Some("value1"),
                            },
                            TagAttr {
                                name: "attr2",
                                value: Some("value2"),
                            },
                        ],
                        self_closing: false,
                    }),
                    Span(6, 50),
                ),
                with_span(Token::Text("after"), Span(51, 55)),
            ],
        );
    }

    #[test]
    fn test_invalid_tag() {
        assert_tokens(
            Tokenizer::new("< tag>").tokenize(),
            &vec![with_span(Token::Text("< tag>"), Span(0, 5))],
        );

        assert_tokens(
            Tokenizer::new("<+>").tokenize(),
            &vec![with_span(Token::Text("<+>"), Span(0, 2))],
        );

        assert_tokens(
            Tokenizer::new("<3a>").tokenize(),
            &vec![with_span(Token::Text("<3a>"), Span(0, 3))],
        );

        assert_tokens(
            Tokenizer::new("<a~b>").tokenize(),
            &vec![with_span(Token::Text("<a~b>"), Span(0, 4))],
        );

        assert_tokens(
            // text + invalid tag
            Tokenizer::new("text< tag>").tokenize(),
            &vec![with_span(Token::Text("text< tag>"), Span(0, 9))],
        );

        assert_tokens(
            // invalid tag + text
            Tokenizer::new("< tag>text").tokenize(),
            &vec![with_span(Token::Text("< tag>text"), Span(0, 9))],
        );

        assert_tokens(
            Tokenizer::new("123< tag><validtag>text").tokenize(),
            &vec![
                with_span(Token::Text("123< tag>"), Span(0, 8)),
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "validtag",
                        tag_attrs: vec![],
                        self_closing: false,
                    }),
                    Span(9, 18),
                ),
                with_span(Token::Text("text"), Span(19, 22)),
            ],
        )
    }

    #[test]
    fn test_close_tag() {
        assert_tokens(
            Tokenizer::new("</tag>").tokenize(),
            &vec![with_span(Token::CloseTag("tag"), Span(0, 5))],
        );

        assert_tokens(
            Tokenizer::new("</tag       >").tokenize(),
            &vec![with_span(Token::CloseTag("tag"), Span(0, 12))],
        );

        assert_tokens(
            // text + close tag + text
            Tokenizer::new("before </tag       > after").tokenize(),
            &vec![
                with_span(Token::Text("before "), Span(0, 6)),
                with_span(Token::CloseTag("tag"), Span(7, 19)),
                with_span(Token::Text(" after"), Span(20, 25)),
            ],
        );
    }

    #[test]
    fn test_invalid_close_tag() {
        assert_tokens(
            Tokenizer::new("< /tag>").tokenize(),
            &vec![with_span(Token::Text("< /tag>"), Span(0, 6))],
        );

        assert_tokens(
            Tokenizer::new("</ tag>").tokenize(),
            &vec![with_span(Token::Text("</ tag>"), Span(0, 6))],
        );

        assert_tokens(
            // text + invalid close tag
            Tokenizer::new("text</ tag>").tokenize(),
            &vec![with_span(Token::Text("text</ tag>"), Span(0, 10))],
        );

        assert_tokens(
            // invalid close tag + text
            Tokenizer::new("</ tag>text").tokenize(),
            &vec![with_span(Token::Text("</ tag>text"), Span(0, 10))],
        );

        assert_tokens(
            Tokenizer::new("123</ tag></validtag>text").tokenize(),
            &vec![
                with_span(Token::Text("123</ tag>"), Span(0, 9)),
                with_span(Token::CloseTag("validtag"), Span(10, 20)),
                with_span(Token::Text("text"), Span(21, 24)),
            ],
        )
    }

    #[test]
    fn test_doctype_tag() {
        assert_tokens(
            Tokenizer::new("<!doctype>").tokenize(),
            &vec![with_span(Token::DocTypeTag, Span(0, 9))],
        );

        assert_tokens(
            // case insensitive
            Tokenizer::new("<!doctyPe>").tokenize(),
            &vec![with_span(Token::DocTypeTag, Span(0, 9))],
        );

        assert_tokens(
            // text + doctype + text
            Tokenizer::new("before<!doctype>after").tokenize(),
            &vec![
                with_span(Token::Text("before"), Span(0, 5)),
                with_span(Token::DocTypeTag, Span(6, 15)),
                with_span(Token::Text("after"), Span(16, 20)),
            ],
        );
    }

    #[test]
    fn test_invalid_doctype_tag() {
        assert_tokens(
            Tokenizer::new("< !doctype>").tokenize(),
            &vec![with_span(Token::Text("< !doctype>"), Span(0, 10))],
        );

        assert_tokens(
            Tokenizer::new("<! doctype>").tokenize(),
            &vec![with_span(Token::Text("<! doctype>"), Span(0, 10))],
        );

        assert_tokens(
            // text + invalid doctype
            Tokenizer::new("text<! doctype>").tokenize(),
            &vec![with_span(Token::Text("text<! doctype>"), Span(0, 14))],
        );

        assert_tokens(
            // invalid doctype + text
            Tokenizer::new("<! doctype>text").tokenize(),
            &vec![with_span(Token::Text("<! doctype>text"), Span(0, 14))],
        );

        assert_tokens(
            Tokenizer::new("<! doct<abc>ype>text").tokenize(),
            &vec![
                with_span(Token::Text("<! doct"), Span(0, 6)),
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "abc",
                        tag_attrs: vec![],
                        self_closing: false,
                    }),
                    Span(7, 11),
                ),
                with_span(Token::Text("ype>text"), Span(12, 19)),
            ],
        );
    }

    #[test]
    fn test_comment_tag() {
        assert_tokens(
            Tokenizer::new("<!--コメント-->").tokenize(),
            &vec![with_span(Token::Comment("コメント"), Span(0, 18))],
        );

        assert_tokens(
            Tokenizer::new("<!--line1\nline2-->").tokenize(),
            &vec![with_span(Token::Comment("line1\nline2"), Span(0, 17))],
        );

        assert_tokens(
            // '<' in the comment is treated as normal character
            Tokenizer::new("<!--<line1\nline2<-->").tokenize(),
            &vec![with_span(Token::Comment("<line1\nline2<"), Span(0, 19))],
        );

        assert_tokens(
            // text + comment + text
            Tokenizer::new("before<!--コメント-->after").tokenize(),
            &vec![
                with_span(Token::Text("before"), Span(0, 5)),
                with_span(Token::Comment("コメント"), Span(6, 24)),
                with_span(Token::Text("after"), Span(25, 29)),
            ],
        );
    }

    #[test]
    fn test_invalid_comment_tag() {
        assert_tokens(
            Tokenizer::new("< !--コメント-->").tokenize(),
            &vec![with_span(Token::Text("< !--コメント-->"), Span(0, 19))],
        );

        assert_tokens(
            Tokenizer::new("<!--コメント-- >").tokenize(),
            &vec![with_span(Token::Text("<!--コメント-- >"), Span(0, 19))],
        );

        assert_tokens(
            Tokenizer::new("<!---コメント-->").tokenize(),
            &vec![with_span(Token::Text("<!---コメント-->"), Span(0, 19))],
        );

        assert_tokens(
            Tokenizer::new("<!--コメント--->").tokenize(),
            &vec![with_span(Token::Text("<!--コメント--->"), Span(0, 19))],
        );

        assert_tokens(
            // text + invalid comment
            Tokenizer::new("text<!--コメント--->").tokenize(),
            &vec![with_span(Token::Text("text<!--コメント--->"), Span(0, 23))],
        );

        assert_tokens(
            // invalid comment + text
            Tokenizer::new("<!--コメント--->text").tokenize(),
            &vec![with_span(Token::Text("<!--コメント--->text"), Span(0, 23))],
        );
    }

    #[test]
    fn test_self_closing_tag() {
        assert_tokens(
            Tokenizer::new("<tag/>").tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![],
                    self_closing: true,
                }),
                Span(0, 5),
            )],
        );

        assert_tokens(
            Tokenizer::new("<tag/ >").tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![],
                    self_closing: true,
                }),
                Span(0, 6),
            )],
        );

        assert_tokens(
            Tokenizer::new("<tag />").tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![],
                    self_closing: true,
                }),
                Span(0, 6),
            )],
        );

        assert_tokens(
            Tokenizer::new("<tag / >").tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![],
                    self_closing: true,
                }),
                Span(0, 7),
            )],
        );

        assert_tokens(
            Tokenizer::new("<tag attr />").tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![TagAttr {
                        name: "attr",
                        value: None,
                    }],
                    self_closing: true,
                }),
                Span(0, 11),
            )],
        );

        assert_tokens(
            Tokenizer::new("<tag attr1  attr2 /    >").tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![
                        TagAttr {
                            name: "attr1",
                            value: None,
                        },
                        TagAttr {
                            name: "attr2",
                            value: None,
                        },
                    ],
                    self_closing: true,
                }),
                Span(0, 23),
            )],
        );

        assert_tokens(
            Tokenizer::new(r#"<tag attr1="value1"  attr2 =       "value2" / >"#).tokenize(),
            &vec![with_span(
                Token::OpenTag(OpenTag {
                    name: "tag",
                    tag_attrs: vec![
                        TagAttr {
                            name: "attr1",
                            value: Some("value1"),
                        },
                        TagAttr {
                            name: "attr2",
                            value: Some("value2"),
                        },
                    ],
                    self_closing: true,
                }),
                Span(0, 46),
            )],
        );

        assert_tokens(
            // text + tag + text
            Tokenizer::new(r#"before<tag attr1="value1"  attr2 =       "value2"/ >after"#)
                .tokenize(),
            &vec![
                with_span(Token::Text("before"), Span(0, 5)),
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "tag",
                        tag_attrs: vec![
                            TagAttr {
                                name: "attr1",
                                value: Some("value1"),
                            },
                            TagAttr {
                                name: "attr2",
                                value: Some("value2"),
                            },
                        ],
                        self_closing: true,
                    }),
                    Span(6, 51),
                ),
                with_span(Token::Text("after"), Span(52, 56)),
            ],
        );

        assert_tokens(
            // text + tag + text
            Tokenizer::new(r#"before<tag attr1="value1"  attr2 =       "value2"/ >after"#)
                .tokenize(),
            &vec![
                with_span(Token::Text("before"), Span(0, 5)),
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "tag",
                        tag_attrs: vec![
                            TagAttr {
                                name: "attr1",
                                value: Some("value1"),
                            },
                            TagAttr {
                                name: "attr2",
                                value: Some("value2"),
                            },
                        ],
                        self_closing: true,
                    }),
                    Span(6, 51),
                ),
                with_span(Token::Text("after"), Span(52, 56)),
            ],
        );
    }

    #[test]
    fn test_invalid_self_closing_tag() {
        assert_tokens(
            Tokenizer::new("< tag />").tokenize(),
            &vec![with_span(Token::Text("< tag />"), Span(0, 7))],
        );

        assert_tokens(
            Tokenizer::new("<+ />").tokenize(),
            &vec![with_span(Token::Text("<+ />"), Span(0, 4))],
        );

        assert_tokens(
            Tokenizer::new("<3a       / >").tokenize(),
            &vec![with_span(Token::Text("<3a       / >"), Span(0, 12))],
        );

        assert_tokens(
            // text + invalid tag
            Tokenizer::new("text< tag      />").tokenize(),
            &vec![with_span(Token::Text("text< tag      />"), Span(0, 16))],
        );

        assert_tokens(
            // invalid tag + text
            Tokenizer::new("< tag />text").tokenize(),
            &vec![with_span(Token::Text("< tag />text"), Span(0, 11))],
        );

        assert_tokens(
            Tokenizer::new("123< tag ><validtag />text").tokenize(),
            &vec![
                with_span(Token::Text("123< tag >"), Span(0, 9)),
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "validtag",
                        tag_attrs: vec![],
                        self_closing: true,
                    }),
                    Span(10, 21),
                ),
                with_span(Token::Text("text"), Span(22, 25)),
            ],
        )
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

        fn new_line_text(start: usize, end: usize) -> WithSpan<Token<'static>> {
            with_span(Token::Text("\n"), Span(start, end))
        }

        let mut tk = Tokenizer::new(html);
        let actual = tk.tokenize();
        let expected = vec![
            with_span(Token::DocTypeTag, Span(0, 14)),
            new_line_text(15, 15),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "html",
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Span(16, 21),
            ),
            new_line_text(22, 22),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "head",
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Span(23, 28),
            ),
            new_line_text(29, 29),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "title",
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Span(30, 36),
            ),
            with_span(Token::Text("test html"), Span(37, 45)),
            with_span(Token::CloseTag("title"), Span(46, 53)),
            new_line_text(54, 54),
            with_span(Token::CloseTag("head"), Span(55, 61)),
            new_line_text(62, 62),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "body",
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Span(63, 68),
            ),
            new_line_text(69, 69),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "p",
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Span(70, 72),
            ),
            with_span(Token::Text("this is p tag"), Span(73, 85)),
            with_span(Token::CloseTag("p"), Span(86, 89)),
            new_line_text(90, 90),
            with_span(
                Token::Comment(
                    "\ncomment start\n<div attr1 attr2=\"value2\">this div in a comment</div>\n",
                ),
                Span(91, 166),
            ),
            new_line_text(167, 167),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "img",
                    tag_attrs: vec![TagAttr {
                        name: "src",
                        value: Some("test"),
                    }],
                    self_closing: true,
                }),
                Span(168, 185),
            ),
            new_line_text(186, 186),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "custom",
                    tag_attrs: vec![TagAttr {
                        name: "attr1",
                        value: None,
                    }],
                    self_closing: false,
                }),
                Span(187, 200),
            ),
            with_span(Token::CloseTag("custom"), Span(201, 209)),
            new_line_text(210, 210),
            with_span(Token::CloseTag("body"), Span(211, 217)),
            new_line_text(218, 218),
            with_span(Token::CloseTag("html"), Span(219, 225)),
        ];

        assert_tokens(actual, &expected);
    }
}
