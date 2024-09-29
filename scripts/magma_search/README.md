
# Magma Search

Search for proofs of implication/non-implication in magmas.

The goal is to have a tool you can just run in the background that might occasionally find a proof.

### Usage

Install Rust: https://www.rust-lang.org/tools/install

```bash
# defaul usage:
cargo run
# for help:
cargo run -- --help
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.21s
     Running `target/debug/magma_search --help`
Search for proofs of implication/non-implication in magmas

Usage: magma_search [OPTIONS]

Options:
      --db <DB>                The name to say hello to [default: db.ron]
      --equations <EQUATIONS>  Load equations from Lean file
      --wipe                   Wipe the database before starting
      --debug                  Debug mode
      --image <IMAGE>          Generate an image from the database
  -h, --help                   Print help
  -V, --version                Print version
```

Press `q` to quit.

By default, it will use `db.ron` as the database file.

### Searchers

- `TransitivitySearcher`: Simple demo
- `ModelSearcher`:
  - Choose a small `N`
  - Randomly build a magma model as a `NxN` matrix of naturals `<N`
  - Check the validity of all equations
    - Parition into `(Valid, Invalid)`
  - For all `(V, I)` pairs, `V -> I` is a non-impliation

### TODO

- [ ] Improve the "in-memory database approach"
  - Will more compact serialization help?
- [ ] Add an `EggSearcher`:
  - Choose an equation `E`
  - Choose a term `t` from one side of some other equation
  - Use egg to perform equality saturation from `t` using `E`
  - For all `u` in the output, `E -> t=u` is an implication
- [ ] Add a `TransitivitySearcher`
- [ ] Run all `Searcher`s in parallel
- [ ] Generate Lean proofs from the results
