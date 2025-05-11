use regex::Regex;
use std::{
    error::Error as StdError,
    fmt::{Debug, Display},
    iter::Peekable,
    mem,
    ops::{Deref, Range, RangeBounds},
    slice::Iter,
    str::Chars,
    sync::OnceLock,
};

const TAG_NAME_RE_STR: &'static str = r"^[a-z][a-z0-9.-]*(-[a-z0-9.-]+)?$";
const TAG_ATTR_RE_STR: &'static str = r"^[a-zA-Z_:][a-zA-Z0-9:._-]*$";

const TAG_NAME_RE: OnceLock<Regex> = OnceLock::new();
const TAG_ATTR_RE: OnceLock<Regex> = OnceLock::new();

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Span(usize, usize);

impl Span {
    pub fn start(&self) -> usize {
        self.0
    }

    pub fn end(&self) -> usize {
        self.1
    }
}

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

impl RangeBounds<usize> for GrowingSpan {
    fn start_bound(&self) -> std::ops::Bound<&usize> {
        use std::ops::Bound::*;
        let start = self.0.as_ref().unwrap();
        Included(start)
    }

    fn end_bound(&self) -> std::ops::Bound<&usize> {
        use std::ops::Bound::*;
        let end = self.1.as_ref().unwrap();
        Excluded(end)
    }
}

#[derive(Debug, PartialEq, Eq)]
enum TagAttrError<'a> {
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
pub struct WithSpan<T> {
    value: T,
    span: Span,
}

impl<T> WithSpan<T> {
    pub fn value(&self) -> &T {
        &self.value
    }

    pub fn span(&self) -> Span {
        self.span
    }
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

impl<'a> TagAttr<'a> {
    pub fn name(&self) -> &'a str {
        self.name
    }

    pub fn value(&self) -> Option<&'a str> {
        self.value
    }
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

impl<'a> OpenTag<'a> {
    pub fn name(&self) -> &'a str {
        self.name
    }

    pub fn tag_attrs(&self) -> &[TagAttr<'a>] {
        &self.tag_attrs
    }

    pub fn self_closing(&self) -> bool {
        self.self_closing
    }
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
            "OpenTag(name={}, attrs={}, self_closing={})",
            self.name, tag_attrs, self.self_closing
        )
    }
}

#[derive(Debug)]
struct OpenTagBuilder<'a> {
    name: Option<&'a str>,
    tag_attrs: Vec<TagAttr<'a>>,
}

impl<'a> OpenTagBuilder<'a> {
    fn new() -> Self {
        Self {
            name: None,
            tag_attrs: Vec::with_capacity(128),
        }
    }

    fn set_name(&mut self, name: &'a str) {
        if self.name.is_some() {
            panic!("`name_span` is already set");
        }
        self.name = Some(name);
    }

    fn add_attr_name(&mut self, name: &'a str) {
        let attr = TagAttr { name, value: None };
        self.tag_attrs.push(attr);
    }

    fn set_attr_value(&mut self, value: &'a str) -> Result<&mut Self, TagAttrError<'a>> {
        if let Some(attr) = self.tag_attrs.last_mut() {
            if attr.value.is_some() {
                Err(TagAttrError::ValueAlreadySet(attr.name))
            } else {
                attr.value = Some(value);
                Ok(self)
            }
        } else {
            Err(TagAttrError::AttrNotFound)
        }
    }

    fn build(&mut self, self_closing: bool) -> OpenTag<'a> {
        OpenTag {
            name: self.name.take().unwrap(),
            tag_attrs: mem::take(&mut self.tag_attrs),
            self_closing,
        }
    }

    fn clear(&mut self) {
        self.name = None;
        self.tag_attrs.clear();
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

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Token::*;

        match self {
            OpenTag(ot) => write!(f, "{}", ot),
            Comment(c) => write!(f, "Comment({})", c),
            Text(t) => write!(f, "Text({})", t),
            CloseTag(tag_name) => write!(f, "CloseTag(name={})", tag_name),
            DocTypeTag => write!(f, "DocType"),
        }
    }
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

    fn read_str<R>(&self, range: R) -> &'a str
    where
        R: RangeBounds<usize>,
    {
        use std::ops::Bound::*;

        let start = match range.start_bound() {
            Included(&s) => s,
            Excluded(&s) => s + 1,
            Unbounded => 0,
        };

        let end = match range.end_bound() {
            Included(&e) => e + 1,
            Excluded(&e) => e,
            Unbounded => self.src.len(),
        };

        &self.src[start..end]
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

pub struct TokenStream<'a>(Vec<WithSpan<Token<'a>>>);

impl<'a> Display for TokenStream<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tokens = self
            .0
            .iter()
            .map(|t| format!("    <{}>", t))
            .collect::<Vec<_>>()
            .join(",\n");
        write!(f, "[\n{}\n]", tokens)
    }
}

impl<'a> Debug for TokenStream<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl<'a> Deref for TokenStream<'a> {
    type Target = [WithSpan<Token<'a>>];

    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl<'b, 'a: 'b> IntoIterator for &'b TokenStream<'a> {
    type IntoIter = Iter<'b, WithSpan<Token<'a>>>;
    type Item = &'b WithSpan<Token<'a>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

pub struct Tokenizer<'a> {
    input: Input<'a>,
    state: TokenizerState,
    is_end_tag: bool,
    tag_name_span: GrowingSpan,
    tag_attr_name_span: GrowingSpan,
    tag_value_span: GrowingSpan,
    text_pos: usize,
    comment_span: GrowingSpan,
    tokens: TokenStream<'a>,
    open_tag_builder: OpenTagBuilder<'a>,
    tag_start_pos: usize,
    raw_text_tag_name: Option<&'a str>,
}

impl<'a> Tokenizer<'a> {
    const RAW_TEXT_TAG_NAMES: [&'static str; 2] = ["script", "style"];

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
            tokens: TokenStream(vec![]),
            open_tag_builder: OpenTagBuilder::new(),
            tag_start_pos: 0,
            raw_text_tag_name: None,
        }
    }

    pub fn tokenize(&mut self) -> &TokenStream<'a> {
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

            let tag_name = self
                .input
                .read_str(Range::<usize>::from(self.tag_name_span));
            if !TAG_NAME_RE
                .get_or_init(|| Regex::new(TAG_NAME_RE_STR).unwrap())
                .is_match(tag_name)
            {
                self.state = TokenizerState::Text;
                return;
            }

            self.open_tag_builder.set_name(tag_name);
            match (self.is_end_tag, token_finalized) {
                (true, true) => {
                    self.finalize_close_tag(tag_name);
                }
                (false, true) => {
                    self.finalize_open_tag(false);
                }
                (_, false) => {}
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
        if ch != '/' && self.raw_text_tag_name.is_some() {
            self.state = TokenizerState::Text;
        } else {
            match ch {
                '<' => {
                    self.prepare_for_tag_open();
                }
                '!' => {
                    self.state = TokenizerState::DocTypeOrComment;
                }
                '/' => {
                    let mut transit_to_end_tag_open = || {
                        self.state = TokenizerState::EndTagOpen;
                        self.is_end_tag = true;
                        self.tag_name_span.set(self.input.pos + 1);
                    };

                    if let Some(raw_text_tag) = self.raw_text_tag_name {
                        if !self.input.remaining()[1..].starts_with(raw_text_tag) {
                            self.state = TokenizerState::Text;
                        } else {
                            transit_to_end_tag_open();
                        }
                    } else {
                        transit_to_end_tag_open();
                    }
                }
                _ => {
                    self.state = TokenizerState::TagName;
                    self.is_end_tag = false;
                    self.tag_name_span.set(self.input.pos);
                }
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

            if let Err(_) = self.open_tag_builder.set_attr_value(tag_value) {
                self.state = TokenizerState::Text;
                self.input.advance();
            } else {
                self.state = TokenizerState::AfterTagValue;
            }
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
        let token = self.open_tag_builder.build(self_closing);
        let tag_name = token.name;
        self.push_token(
            Token::OpenTag(token),
            Span(self.next_start_pos(), self.input.pos),
        );
        if self.is_raw_text_tag(tag_name) {
            self.raw_text_tag_name = Some(tag_name);
        }

        self.tag_name_span = GrowingSpan::default();
    }

    fn finalize_close_tag(&mut self, tag_name: &'a str) {
        self.finalize_text_if_exist(self.tag_start_pos);
        self.text_pos = self.input.pos + 1;
        let span = Span(self.next_start_pos(), self.input.pos);
        self.push_token(Token::CloseTag(tag_name), span);
        self.tag_name_span = GrowingSpan::default();
        self.raw_text_tag_name = None;
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
        self.tokens.0.push(WithSpan::new(token, span.into()));
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
        self.open_tag_builder.clear();
    }

    fn is_raw_text_tag(&self, name: &str) -> bool {
        Self::RAW_TEXT_TAG_NAMES.iter().any(|n| *n == name)
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
    fn script_tag_ignores_non_matching_close_tag() {
        assert_tokens(
            Tokenizer::new(r#"<script type="text/javascript">console.log("</scrip>")</script>"#)
                .tokenize(),
            &vec![
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "script",
                        tag_attrs: vec![TagAttr {
                            name: "type",
                            value: Some("text/javascript"),
                        }],
                        self_closing: false,
                    }),
                    Span(0, 30),
                ),
                with_span(Token::Text(r#"console.log("</scrip>")"#), Span(31, 53)),
                with_span(Token::CloseTag("script"), Span(54, 62)),
            ],
        );

        assert_tokens(
            Tokenizer::new(r#"<script type="text/javascript">console.log("</script>")</script>"#)
                .tokenize(),
            &vec![
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "script",
                        tag_attrs: vec![TagAttr {
                            name: "type",
                            value: Some("text/javascript"),
                        }],
                        self_closing: false,
                    }),
                    Span(0, 30),
                ),
                with_span(Token::Text(r#"console.log(""#), Span(31, 43)),
                with_span(Token::CloseTag("script"), Span(44, 52)),
                with_span(Token::Text(r#"")"#), Span(53, 54)),
                with_span(Token::CloseTag("script"), Span(55, 63)),
            ],
        );
    }

    #[test]
    fn style_tag_ignores_non_matching_close_tag() {
        assert_tokens(
            Tokenizer::new(r#"<style>console.log("</styl>")</style>"#).tokenize(),
            &vec![
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "style",
                        tag_attrs: vec![],
                        self_closing: false,
                    }),
                    Span(0, 6),
                ),
                with_span(Token::Text(r#"console.log("</styl>")"#), Span(7, 28)),
                with_span(Token::CloseTag("style"), Span(29, 36)),
            ],
        );

        assert_tokens(
            Tokenizer::new(r#"<style>console.log("</style>")</style>"#).tokenize(),
            &vec![
                with_span(
                    Token::OpenTag(OpenTag {
                        name: "style",
                        tag_attrs: vec![],
                        self_closing: false,
                    }),
                    Span(0, 6),
                ),
                with_span(Token::Text(r#"console.log(""#), Span(7, 19)),
                with_span(Token::CloseTag("style"), Span(20, 27)),
                with_span(Token::Text(r#"")"#), Span(28, 29)),
                with_span(Token::CloseTag("style"), Span(30, 37)),
            ],
        );
    }

    #[test]
    fn test_html() {
        let html = r#"
<!doctype html>
<html>
<head>
<title>test html</title>
<style>
    div#main {
        color: red
    }
</style>
</head>
<body>
<p>this is p tag</p>
<!--
comment start
<div attr1 attr2="value2">this div in a comment</div>
-->
<img src="test" />
<custom attr1></custom>
<script type="text/javascript">
console.log("</script>");
</script>
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
            with_span(
                Token::OpenTag(OpenTag {
                    name: "style",
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Span(55, 61),
            ),
            with_span(
                Token::Text("\n    div#main {\n        color: red\n    }\n"),
                Span(62, 102),
            ),
            with_span(Token::CloseTag("style"), Span(103, 110)),
            new_line_text(111, 111),
            with_span(Token::CloseTag("head"), Span(112, 118)),
            new_line_text(119, 119),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "body",
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Span(120, 125),
            ),
            new_line_text(126, 126),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "p",
                    tag_attrs: vec![],
                    self_closing: false,
                }),
                Span(127, 129),
            ),
            with_span(Token::Text("this is p tag"), Span(130, 142)),
            with_span(Token::CloseTag("p"), Span(143, 146)),
            new_line_text(147, 147),
            with_span(
                Token::Comment(
                    "\ncomment start\n<div attr1 attr2=\"value2\">this div in a comment</div>\n",
                ),
                Span(148, 223),
            ),
            new_line_text(224, 224),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "img",
                    tag_attrs: vec![TagAttr {
                        name: "src",
                        value: Some("test"),
                    }],
                    self_closing: true,
                }),
                Span(225, 242),
            ),
            new_line_text(243, 243),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "custom",
                    tag_attrs: vec![TagAttr {
                        name: "attr1",
                        value: None,
                    }],
                    self_closing: false,
                }),
                Span(244, 257),
            ),
            with_span(Token::CloseTag("custom"), Span(258, 266)),
            new_line_text(267, 267),
            with_span(
                Token::OpenTag(OpenTag {
                    name: "script",
                    tag_attrs: vec![TagAttr {
                        name: "type",
                        value: Some("text/javascript"),
                    }],
                    self_closing: false,
                }),
                Span(268, 298),
            ),
            with_span(Token::Text("\nconsole.log(\""), Span(299, 312)),
            with_span(Token::CloseTag("script"), Span(313, 321)),
            with_span(Token::Text("\");\n"), Span(322, 325)),
            with_span(Token::CloseTag("script"), Span(326, 334)),
            new_line_text(335, 335),
            with_span(Token::CloseTag("body"), Span(336, 342)),
            new_line_text(343, 343),
            with_span(Token::CloseTag("html"), Span(344, 350)),
        ];

        assert_tokens(actual, &expected);
    }
}
