# htmlkit

**htmlkit** is a modular HTML processing toolkit in Rust, built for safety, traceability, and clarity of structure.  
It's designed as a learning project, but aims for practical extensibility.

> **Note:** This project is intended for parser and AST construction learning purposes.  
> It does **not** aim for full compliance with the HTML specification, nor does it prioritize runtime performance.

## Project Structure

This is a Cargo workspace that consists of:

- `tokenizer`: Lexical tokenizer using a deterministic FSM with span tracking.
- `dom` _(planned)_: Parser for building a typed HTML AST or DOM tree.
- `query` _(planned)_: Selector engine like `BeautifulSoup` or `jsoup`.

## Philosophy

- Precise tokenization with span-based traceability (`WithSpan<T>`)
- Clear separation of responsibilities (tokenizer ≠ parser ≠ query)
- Zero-copy architecture (`&str`) and no unnecessary allocations

## Status

- ✅ Tokenizer completed and well-tested
- ⏳ DOM construction in progress
- 🔭 Query layer planned

## License

MIT

