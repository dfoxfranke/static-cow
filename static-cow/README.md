# `static-cow`

This Rust crate provides a framework of traits for writing types that are
generic over ownership of their contents, by lifting `Cow` to the type level so
that whether a particular object is borrowed or owned can be specified through a
generic type parameter. 

<div style="max-width: 20em; margin-left: auto; margin-right: auto;">
<img src="https://raw.githubusercontent.com/dfoxfranke/static-cow/10cffdd130d62af2ee0c437bc06500cfe8123417/static-cow/images/mascot.webp" alt="Mascot"/>
</div>

## Documentation

See [API docs on docs.rs](https://docs.rs/static_cow).

## License

This project licensed under the [Apache License
2.0](https://spdx.org/licenses/Apache-2.0.html) with [LLVM
exception](https://spdx.org/licenses/LLVM-exception.html). Unless you explicitly
state otherwise, any contribution intentionally submitted for inclusion in
`static-cow` by you, shall be licensed as Apache 2.0 with LLVM exception,
without any additional terms or conditions.