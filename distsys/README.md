# DistSys

Distributed systems notes & exercises.

## `veil-consensus/`

A reproduction of the blog post
[Liveness Proofs in Veil, Part I: The First Step](https://proofsandintuitions.net/2026/06/24/liveness-proofs-in-veil-part-1/):
the one-step `Consensus` example from the TLA+ examples repository, with its
agreement (safety) property checked and its "eventually a value is chosen"
(liveness) property proved in [Veil](https://github.com/verse-lab/veil).
See `veil-consensus/VeilConsensus/Consensus.lean`.

It is a **separate Lake project**, not part of the root `my-lean` build, because:

* Veil's liveness support (`temporal` properties, the Lentil temporal proof mode)
  exists only on Veil's unreleased `veil-live-demo` branch, pinned by commit in
  `veil-consensus/lakefile.toml`.
* That branch is on Lean v4.28.0, while the root package is on v4.32.0.
* Veil calls the cvc5 SMT (Satisfiability Modulo Theories) solver through a
  native FFI (foreign function interface) binding that is compiled during the
  build.

### Prerequisites

* NodeJS and `npm` on the `PATH` (Veil builds its widgets with them).
* `unzip` (the cvc5 binding downloads a prebuilt cvc5 archive).
* libc++ headers, used to compile the cvc5 binding. On Ubuntu:

  ```sh
  sudo apt-get install -y libc++-18-dev libc++abi-18-dev
  ```

`elan` downloads the Lean v4.28.0 toolchain automatically on the first `lake`
command in the directory.

### Building

```sh
cd distsys/veil-consensus
lake exe cache get   # prebuilt Mathlib v4.28.0, pulled in transitively by Veil
lake build
```

The first build compiles Veil and its dependencies from source and takes a
while. `lake build` prints the `#check_invariants` result for `agreement`; the
liveness proof `success` is checked as part of the build. If the cvc5 binding
fails to build, `rm -rf .lake/packages/cvc5 && lake build` usually fixes it
(known sporadic issue, see Veil's README).

To re-elaborate the file on its own (for example after editing it), the cvc5
binding must be loaded as a plugin, otherwise `lean` aborts with "Could not find
native implementation of external declaration 'cvc5.TermManager.new'":

```sh
lake env lean --plugin=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so \
  VeilConsensus/Consensus.lean
```
