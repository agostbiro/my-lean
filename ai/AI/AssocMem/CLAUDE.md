# AssocMem style rules

These rules apply to the Lean files in this folder. They come from section 2 of the plan "Lean plan: outer-product memory capacity": <https://claude.ai/artifact/LWSSdEtKnSuAffomYUtU9P>.

The Lean code must be easy to explain with the skill walk-me-through-lean (github.com/agostbiro/walk-me-through-lean). That skill explains one declaration as a sequence of Steps. Each Step is one tactic or one combinator chain. The skill shows the Goal State after each Step, and it links each Step to a Plan item. Write the code so that this walk is short and clear.

## Proof structure

This section is a convention of this project. The skill does not need it, but the convention makes each walk easier.

- Each theorem and each Helper has a docstring.
- If a proof has more than 3 Steps, its docstring has three parts:
  - Statement: one sentence that says the claim in plain words.
  - Concepts: the mathematical ideas a reader needs, as a short list.
  - Plan: at most 5 numbered items. Each item is one high-level move of the proof.
- If a proof has more than 3 Steps, put a comment `-- Plan n: <short text>` before the tactics that do Plan item n.
- If a proof has 3 Steps or fewer, the docstring has only the Statement. The proof has no `-- Plan` comments. The skill gives no Plan Turn to such a proof.
- Write one tactic or one combinator chain per line.
- A proof has at most 12 tactic Steps. If a proof needs more, move a part into a Helper lemma with its own docstring.
- Give each Helper lemma a name that says its claim, for example `sum_eq_zero_of_flipSign_neg`.

## Tactics

- Use `simp only [...]` with an explicit list of lemmas. A reader must see which Library items a Step uses.
- Use `simp`, `ring`, `linarith`, `nlinarith`, `positivity`, `omega`, and `norm_num` only as the last tactic of a goal.
- You can use `field_simp` at any Step. A `field_simp` Step is usually followed by `ring`.
- To rewrite under `fun ω => ...` or under an integral, use `simp only [...]` or `MeasureTheory.integral_congr_ae`. `rw` cannot rewrite a term that contains a bound variable.
- Do not use `simp_all`, `aesop`, `exact?`, or `apply?` in the final code. You can use `exact?` and `apply?` to find lemma names while you work.
- Do not use `sorry`, `axiom`, `native_decide`, or `#eval!` in the final code.
- Use full names for Library items, for example `Finset.sum_comm`, not `sum_comm` after `open`.

## Prose (docstrings, comments, README)

Write all prose in ASD-STE100 (Simplified Technical English). Use the rules in STYLE.md of the skill repository:

- At most 20 words in an instruction. At most 25 words in other sentences.
- One idea per sentence.
- Active voice. Name the actor: "The rw step replaces the left side."
- Simple present, simple past, simple future, infinitive, and imperative only.
- Third person: "the proof", "the lemma", "Lean". Do not write "we" or "let's".
- No semicolons. No humor. No rhetorical questions.
- Use the replacement table in STYLE.md: "make sure", not "verify", "check", or "ensure". "Use", not "utilize". "Because", not "since".
- Lean identifiers and mathematical terms are exempt from the vocabulary rules.

## Get each fact from Lean

Do not guess a Goal State. Get it from Lean. Use the method in LEAN-FACTS.md of the skill repository:

1. Copy the file to a scratch directory. Do not edit the source file for probes.
2. Add `trace_state` after the tactic.
3. Run `lake env lean --json <scratch file>` from the project root.
4. Read the `trace_state` message.

## Implicit arguments

Each file turns off `autoImplicit` with `set_option autoImplicit false`. Declare every name in a statement with `variable` or with a binder.

Many definitions take `{M d : ℕ}` as implicit arguments. Lean infers them only from the other arguments. If no argument fixes `d`, Lean reports "don't know how to synthesize implicit argument". To prevent this error:

- Give a type to each bound variable: write `fun ω : Signs M d => ...`, not `fun ω => ...`.
- Pass `M` and `d` explicitly when no argument fixes them, for example `signMeasure M d`.
