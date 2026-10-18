# AssocMem: outer-product memory capacity

This folder proves an exact capacity theorem for the outer-product memory store.
The source is the article "You could have invented transformers from memory" (Alex Wang, 2026):
<https://alexwang.ai/posts/associative-memory/>.
The article says that the store holds about `d` memories. This folder proves an exact version of that claim.

## The setup

- The store holds `M` memories. Each key has dimension `d ≥ 1`. Each value has dimension `dv`.
- Each key entry is `1 / √d` or `-1 / √d`, with equal probability. All entries are independent.
  Lean models this as the uniform measure `signMeasure M d` on all sign patterns.
- The values `V i` are fixed vectors.
- The store is `W = Vᵀ K`. The recall of a query `x` is `f(x) = W x`.
- `‖v‖²` is the Euclidean squared length `sqLen v = v ⬝ᵥ v`.
  The Lean code does not use `‖v‖`, because Mathlib gives `Fin n → ℝ` the sup norm.

## The main theorem

For each memory `j`, `AssocMem.main` states:

```latex
\mathbb{E}\,\|f(k_j) - v_j\|^2 = \frac{1}{d}\sum_{i \ne j}\|v_i\|^2
```

If each value has length 1, `AssocMem.main_unit` states that the mean squared error is `(M - 1) / d`.
`AssocMem.capacity` states that this error is not more than the signal if and only if `M ≤ d + 1`.

## The proof

The proof uses two moment facts about the keys, for `i ≠ j` and `l ≠ j`:

- (H1) If `i = l`, then the mean of `(k_i ⬝ k_j)²` is `1 / d`.
- (H2) If `i ≠ l`, then the mean of `(k_i ⬝ k_j)(k_l ⬝ k_j)` is 0.

A sign flip of one key entry proves both facts. The proof does not use the independence API of Mathlib.

## File map

| File | Content |
| --- | --- |
| `Defs.lean` | The store, the recall (`retrieve`), the interference, and `sqLen` |
| `Algebra.lean` | Exact algebra, with no probability |
| `Expectation.lean` | The main theorem for any keys with (H1) and (H2) |
| `Signs.lean` | Random-sign keys satisfy (H1) and (H2) |
| `Capacity.lean` | The main theorem and the capacity for random-sign keys |
| `Check.lean` | The axiom lines and the statement guards. It is not part of the `AI` library. |

The definition has the name `retrieve`, not `recall`, because Mathlib uses `recall` as a command keyword.

## Build

Run these commands from the repository root:

```sh
lake build AI
lake env lean ai/AI/AssocMem/Check.lean
```

To get a guided walk through a proof, say "Walk me through AssocMem.main."
