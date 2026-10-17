# probatum

Write the contract, get the proof: compile behavioral intent into programs with
machine-checkable proof certificates. Zero external dependencies.

## Install

From source:

```sh
cargo build --release
# binary at target/release/probatum
```

Or install globally:

```sh
cargo install --path .
```

## Usage

```sh
probatum compile <spec.ic> [--emit rust,go,dsl] [--out DIR]
probatum check   <spec.ic>
probatum verify  <cert-file> <spec.ic>
probatum replay  <cert-file>
probatum examples [DIR]
```