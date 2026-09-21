import Veil
import Veil.Liveness

/-!
# One-Step Consensus: a Liveness Proof in Veil

Reproduction of the blog post
[Liveness Proofs in Veil, Part I: The First Step](https://proofsandintuitions.net/2026/06/24/liveness-proofs-in-veil-part-1/)
by Qiyuan Zhao and Ilya Sergey (June 24, 2026). The model and the proof script
below are copied verbatim from the post's companion file
[`Examples/Liveness/TLA/Consensus.lean`](https://github.com/verse-lab/veil/blob/veil-live-demo/Examples/Liveness/TLA/Consensus.lean)
on Veil's `veil-live-demo` branch. Only the comments are ours.

## The problem

A safety property says "nothing bad ever happens". A liveness property says
"something good eventually happens". The post proves a liveness property for the
smallest example it could find: the `Consensus` module from the TLA+ examples
repository. TLA+ is the specification language built on TLA (Temporal Logic of
Actions). The TLA+ specification is:

```
CONSTANT Value

VARIABLE chosen

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}

TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen)

Inv ==  /\ TypeOK
        /\ Cardinality(chosen) \leq 1

ASSUME ValueNonempty == Value # {}

Success == <>(chosen # {})

Spec == Init /\ [][Next]_chosen

LiveSpec == Spec /\ WF_chosen(Next)
```

The state is one set `chosen ⊆ Value`, initially empty. The only transition `Next`
is enabled while `chosen` is empty and replaces it by `{v}` for some `v ∈ Value`.
So the protocol takes exactly one meaningful step, and that step is the "something
good" whose inevitability we prove.

* `Inv` is the safety property: at most one value is ever chosen (agreement).
* `Success` is the liveness property: eventually `chosen` is nonempty.
* `Spec` is the set of all traces: `Init` holds at the start and every step is
  either a `Next` step or a stuttering step that leaves `chosen` unchanged
  (that is what `[Next]_chosen` means).
* `LiveSpec` adds WF (weak fairness) of `Next`: if a non-stuttering `Next` step
  stays enabled from some point on, the trace must eventually take one. Without
  it, the all-stuttering trace `{}, {}, {}, …` satisfies `Spec` but never
  `Success`.

The theorem is `LiveSpec => Success`.

## Temporal operators

Traces are infinite sequences of states `s₀, s₁, s₂, …`. The operators used below,
in the notation of Lentil (the TLA library Veil builds on):

* `□ P` ("always"): `P` holds at every position of the trace.
* `◇ P` ("eventually"): `P` holds at some position of the trace.
* `◯ P` ("next"): `P` holds at the next position.
* `⌜ p ⌝` lifts a state predicate `p : σ → Prop` to a temporal formula.
* `⟨ a ⟩` lifts an action (a two-state relation `a : σ → σ → Prop`) to a temporal
  formula: it holds at position `i` when `(sᵢ, sᵢ₊₁)` satisfies `a`. Not to be
  confused with TLA+'s `<<Next>>_chosen`, which is the non-stuttering version of
  `Next`.
* `P ↝ Q` ("leads to") abbreviates `□ (P → ◇ Q)`: from any point where `P` holds,
  `Q` eventually holds.
* `P ⇒ Q` abbreviates `□ (P → Q)`.
* `Enabled a` holds in a state from which some `a` step is possible.
* `𝒲ℱ a` is weak fairness of action `a`, the counterpart of `WF_chosen(Next)`.
* `Γ |-tla- P` is a sequent between temporal formulas: `Γ` implies `P` on every
  trace.

## Reading the formalization

| TLA+                          | Veil                                             |
| ----------------------------- | ------------------------------------------------ |
| `CONSTANT Value`              | `type value` (comes with an `Inhabited` instance) |
| `chosen ⊆ Value`              | `relation chosen : value → Bool`                 |
| `Init == chosen = {}`         | `after_init { chosen V := false }`               |
| `chosen = {}` / `chosen # {}` | ghost relations `noneChosen` / `someChosen`       |
| `Next`                        | `action choose`                                  |
| stuttering in `[Next]_chosen` | `action stutter`                                 |
| `Inv` (cardinality ≤ 1)       | `safety [agreement] chosen V1 ∧ chosen V2 → V1 = V2` |
| `ASSUME ValueNonempty`        | the `Inhabited value` instance                   |
| `Success == <>(chosen # {})`  | `◇ ⌜ someChosen ⌝`                               |
| `WF_chosen(Next)`             | `𝒲ℱ choose`                                     |

Two choices differ from the TLA+ text: the set `chosen` is a unary relation, and
the two state predicates the liveness proof needs are named as ghost relations.

## Tooling

`#check_invariants` proves the safety property by sending one-step verification
conditions to an SMT (Satisfiability Modulo Theories) solver, cvc5, through an
FFI (foreign function interface) binding. `veil.smt.trust false` asks Veil to
reconstruct Lean proofs from the solver's answers instead of trusting them.

The temporal proof uses Lentil's proof mode. Its tactics are the ordinary Lean
ones prefixed with `t` (`tsuffices`, `tapply`, `tclear`, …) acting on temporal
sequents. `veil_solve_temporal` leaves the temporal proof mode: it reduces a
one-step temporal obligation to a first-order verification condition and
discharges it with Veil's automation.

## Sanity checks

Two edits that should break the development do break it (checked by hand, not
committed):

* Removing `require noneChosen` from `choose` makes `#check_invariants` report
  `agreement ... ❌` for `choose`, with a counterexample where a value is already
  chosen and `choose` picks another.
* Removing the premise `𝒲ℱ choose →` from `success` makes the proof script fail
  at `tintro hwf`: there is no fairness hypothesis to introduce, and the
  argument cannot proceed without it.
-/

veil module Consensus

open TLA

-- `CONSTANT Value`. Declaring a type in Veil provides an `Inhabited value`
-- instance, the analogue of `ASSUME ValueNonempty`. It is needed for the WF1
-- obligation that `choose` is enabled: choosing a value presupposes one exists.
type value

-- The set `chosen ⊆ Value`, as a unary relation.
relation chosen : value → Bool

#gen_state

-- `Init == chosen = {}`
after_init {
  chosen V := false
}

-- The two state predicates `chosen = {}` and `chosen # {}`, named so the liveness
-- proof can talk about them.
ghost relation noneChosen := ∀ v, ¬ chosen v
ghost relation someChosen := ∃ v, chosen v

-- `Next`: enabled while nothing is chosen; picks some `v` and records it.
action choose {
  require noneChosen
  let v ← pick value
  chosen v := true
}

-- TLA stuttering step: `chosen` does not change. Veil's generated next-step
-- relation `NextStep` is the disjunction of all actions, here `choose ∨ stutter`,
-- which is the counterpart of `[][Next]_chosen`.
action stutter {
  pure ()
}

-- `Inv`, modulo `TypeOK`: at most one value is chosen.
safety [agreement] chosen V1 ∧ chosen V2 → V1 = V2

set_option veil.smt.trust false

#gen_spec

-- Proves `agreement` is an inductive invariant. Veil does this automatically.
#check_invariants

-- `LiveSpec => Success`. Fairness is stated directly as a premise.
temporal [success] 𝒲ℱ choose → ◇ ⌜ someChosen ⌝

/-!
## The paper proof

**Part 1: reduce "eventually" to "leads-to".** Instead of proving `◇ someChosen`
directly, prove `noneChosen ↝ someChosen`. Unfolding it, `noneChosen → ◇ someChosen`
holds at every position, in particular at the initial one. `noneChosen` holds
there because `after_init` leaves every value unchosen, so `◇ someChosen` follows
at the start of the trace.

**Part 2: prove the leads-to with WF1.** WF1 is Lamport's rule for turning weak
fairness into progress. Lentil provides it in the original shape:

```
theorem wf1_original p q next a :
  ((p ∧ ⟨next⟩ ⇒ ◯ (p ∨ q)) ∧
   ((p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯ q)) ∧
   ((p ⇒ Enabled a))) |-tla-
    (□ ⟨next⟩ ∧ 𝒲ℱ a → p ↝ q)
```

With `p = noneChosen`, `q = someChosen`, `next = NextStep`, and `a = choose`, the
three obligations are:

1. `noneChosen` is preserved until `someChosen`: from a state where no value is
   chosen, a `stutter` step keeps `noneChosen` and a `choose` step reaches
   `someChosen`.
2. A `choose` step achieves `someChosen`: it picks a value and records it.
3. `choose` is enabled while `noneChosen` holds: there is always some value to
   pick, because `value` is inhabited.

Suppose that from some point where `noneChosen` holds, `someChosen` is never
reached. By (1) the system stays in `noneChosen` forever; by (3) `choose` stays
enabled; so weak fairness eventually forces a `choose` step; by (2) that step
makes `someChosen` true. Contradiction. Hence `noneChosen ↝ someChosen`.

## The proof in Veil

`prove_temporal_by [success]` opens the goal

```
(⌜ Init ⌝ ∧ □⟨ NextStep ⟩ ∧ □⌜ Invariants ⌝) |-tla- success
```

The left side is the specification Veil generates from the model, matching `Spec`:
the initial-state predicate, "every step satisfies `NextStep`", and the declared
invariants (here just `agreement`, which this proof does not need). Each of the
three WF1 obligations is about a single step, so once `tmonotone` strips its
outer `□` it is a first-order verification condition that `veil_solve_temporal`
discharges.
-/

prove_temporal_by [success]
  -- Name each of the three conjuncts: ⌜ Init ⌝, □⟨ NextStep ⟩ and □⌜ Invariants ⌝
  tstart hInit hNext hInv
  tclear hInv             -- the agreement invariant is not needed for this proof
  tdsimp only [success]   -- unfold `success`
  tintro hwf              -- introduce hwf : weak fairness of `choose` to the
                          -- temporal proof context

  -- Part 1: reduce the goal to `noneChosen ↝ someChosen`
  tsuffices hleadsto :
   ⌜fun st => (veil_term% noneChosen) st⌝ ↝ ⌜fun st => (veil_term% someChosen) st⌝ by
    tunfold leads_to at hleadsto           -- unfold leads-to to expose the outer □
    thave himp := always_weaken _ hleadsto -- fix it at the initial position
    tapply himp                            -- prove with `noneChosen` as the state
    tclear *- hInit                        -- clear unrelated temporal hypotheses
    veil_solve_temporal                    -- reduce the goal to FO VC and prove it

  -- Part 2: prove the leads-to via WF1:
  -- `p = noneChosen`, `q = someChosen`, `next = NextStep`, and `a = choose`
  tclear hInit                             -- ⌜ Init ⌝ is not used here
  trevert hNext hwf ; trewrite [← TLA.and_imp]
                                           -- massage the goal to match it with
                                           --   the conclusion of `wf1_original`
  tapply wf1_original                      -- leaves the three obligations
  tsplit_ands
  --  (1) noneChosen is stable until someChosen
  --  (2) a `choose` step achieves someChosen
  --  (3) `choose` is enabled while noneChosen holds
  --  Each is about one transition: strip the outer □,
  --                                reduce to first-order VC and discharge it
  all_goals tmonotone ; veil_solve_temporal

end Consensus
