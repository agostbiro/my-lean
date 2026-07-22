# my-lean

A monorepo containing my personal Lean projects. 

## Projects

| Directory                 | Description                    |
| ------------------------- |  ------------------------------ |
| `theory-of-computation/`  | Theory of computation exercises |
| `functional-programming/` | Functional programming exercises                |


The shared package keeps the toolchain, dependency lockfile, and build commands
in one place.

Both libraries share [Batteries](https://github.com/leanprover-community/batteries),
pinned to `v4.32.0` to match `lean-toolchain`, and use its linter.

For quick throwaway experiments, create `scratch.lean` in the repo root — it's
gitignored and checked live by the Lean editor extension (not part of any build).

## Building

Build both libraries from the repo root:

```sh
lake build
```

To build one library only, name its Lake target, for example
`lake build TheoryOfComputation`.

## Linting

Run the Batteries linter over both libraries:

```sh
lake lint
```

CI uses `leanprover/lean-action` to run the same build and lint checks.
