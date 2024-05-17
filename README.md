# `plist_pls` - XML & ASCII plist lexing & parsing

`plist_pls` is very much in development right now, with me mainly trying to get a XML plist lexer & parser in a good enough state to ship

In the longer run, this repository may break into several crates, with the following aims:
- Zero-copy, zero-allocation lexing
- Minimal-allocation parsing (only allocating for variable-sized collections, not the values within)
- Awesome, high quality errors that non-programmers can understand (powered by [`miette`](https://lib.rs/crates/miette))
- [`serde`](https://lib.rs/crates/serde) support (deserialisation **and** serialisation)
- Owned variants of Plist primitives
- ASCII plist syntax highlighting for VSCode
- ASCII plist formatter
- (super long term) mutability

Non-aims:
- Short compile times (I'd rather avoid boilerplate in the source code by using proc macros)
- Small size footprint
