import Mathlib.Computability.NFA

namespace TheoryOfComputation.Chapter1.Problem32

/-!
# Problem 1.32 — Specification

Let `Σ₃` be the alphabet of all 3-bit columns, i.e. `Bool × Bool × Bool`.
A string `w ∈ Σ₃*` therefore gives three rows of bits. Read each row as a
binary number, most significant bit first (all three rows have the same
length `|w|`, so no overflow is permitted). Define

    B = { w ∈ Σ₃*  | the bottom row of w is the sum of the top two rows }

For example:

⎡ 0 ⎤⎡ 1 ⎤⎡ 1 ⎤
⎢ 0 ⎥⎢ 0 ⎥⎢ 1 ⎥ ∈ B, because 011 + 001 = 100
⎣ 1 ⎦⎣ 0 ⎦⎣ 0 ⎦

But

⎡ 0 ⎤⎡ 1 ⎤
⎢ 0 ⎥⎢ 0 ⎥ ∉ B, because 01 + 00 ≠ 11
⎣ 1 ⎦⎣ 1 ⎦

This file is the specification only: the alphabet `Σ₃`, the language `B`, the
row extractors and value readers `B` is stated with, and a sanity check that
`B` agrees with an independent second translation of the problem statement.
The DFA that recognizes `B.reverse` is in `Implementation.lean`, and its
correctness proof is in `Proof.lean`.
-/

/-- A symbol in the alphabet `Σ₃`: a column of three bits. -/
abbrev Sigma3 := Bool × Bool × Bool

/-- Little endian interpretation of a list of bools. -/
def valueLE : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * valueLE bs

/-- Big endian interpretation of a list of bools: reading a list most significant bit first
is reading its reverse least significant bit first.

This definition is the insight the whole solution rests on, stated once: the `B` side of the
problem is most significant bit first (fixed by the problem statement), the automaton side is
least significant bit first (fixed by the direction carries flow in), and `reverse` is what
connects them. -/
def valueBE (bs : List Bool) : Nat := valueLE bs.reverse

/-- The top row of a word: the first bit of every column. -/
def row1 (w : List Sigma3) : List Bool := w.map fun (x, _, _) => x

/-- The middle row of a word: the second bit of every column. -/
def row2 (w : List Sigma3) : List Bool := w.map fun (_, y, _) => y

/-- The bottom row of a word: the third bit of every column. -/
def row3 (w : List Sigma3) : List Bool := w.map fun (_, _, z) => z

/-- The language `B` of the problem: words whose bottom row is the sum of the top two rows.

Note that all three rows have equal length by definition (they're extracted from the same list). -/
def B : Language Sigma3 :=
  { wBE | valueBE (row3 wBE) = valueBE (row1 wBE) + valueBE (row2 wBE) }

/-- Helper to avoid unfolding manually in subsequent proofs. -/
lemma mem_B_iff (wBE : List Sigma3) :
    wBE ∈ B ↔ valueBE (row3 wBE) = valueBE (row1 wBE) + valueBE (row2 wBE) := Iff.rfl

/-! ### Rewriting rules for rows

Peeling the leading column off a word peels the leading bit off each of its rows, and reversing
a word reverses each of its rows. Both facts hold by computation, but they are needed as
rewrite rules (rather than by unfolding `row1`/`row2`/`row3`) so that the proofs below can keep
talking about `row1 columns` instead of an unfolded `List.map`. -/

/-- Peeling a column off a word peels the leading bit off its top row. -/
@[simp] lemma row1_cons (x y z : Bool) (columns : List Sigma3) :
    row1 ((x, y, z) :: columns) = x :: row1 columns := rfl

/-- Peeling a column off a word peels the leading bit off its middle row. -/
@[simp] lemma row2_cons (x y z : Bool) (columns : List Sigma3) :
    row2 ((x, y, z) :: columns) = y :: row2 columns := rfl

/-- Peeling a column off a word peels the leading bit off its bottom row. -/
@[simp] lemma row3_cons (x y z : Bool) (columns : List Sigma3) :
    row3 ((x, y, z) :: columns) = z :: row3 columns := rfl

/-- Reversing a word reverses its top row. -/
@[simp] lemma row1_reverse (w : List Sigma3) : row1 w.reverse = (row1 w).reverse := by
  simp [row1]

/-- Reversing a word reverses its middle row. -/
@[simp] lemma row2_reverse (w : List Sigma3) : row2 w.reverse = (row2 w).reverse := by
  simp [row2]

/-- Reversing a word reverses its bottom row. -/
@[simp] lemma row3_reverse (w : List Sigma3) : row3 w.reverse = (row3 w).reverse := by
  simp [row3]

/-! ### The examples from the problem statement

The matrix art above writes the three rows across the page, so each *column* of the picture
is one letter of `Σ₃`. Reading the first example column by column gives
`(0,0,1)`, `(1,0,0)`, `(1,1,0)`. -/

/-- `011 + 001 = 100`, so this word is in `B`. -/
example : [(false, false, true), (true, false, false), (true, true, false)] ∈ B := by
  rw [mem_B_iff]; decide

/-- `01 + 00 ≠ 11`, so this word is not in `B`. -/
example : [(false, false, true), (true, false, true)] ∉ B := by
  rw [mem_B_iff]; decide

/-! ### Sanity check: encoding numbers into words

`B` is a definition, so nothing in this file can prove it correct: it is the trusted
translation of the problem statement into Lean. What we can do is translate the statement a
second time, independently, and prove that the two translations agree. `encode` builds the
word for the addition `a + b = c` directly from the three numbers, and `encode_mem_B_iff`
restates membership in `B` with no lists, rows or endianness in sight:
`encode n a b c ∈ B ↔ c = a + b`. A convention error in `B` (wrong endianness, top and bottom
row confused) would make that theorem unprovable. The check leaves no word out either:
`encode_rows` shows that every word is the encoding of its own three rows, so the words the
theorem talks about are all of them, not just those `encode` happens to build.

Limitations of this check:

* It does not prove `B` correct — nothing can. `encode` is itself a trusted translation of
  the English statement; the theorem only shows the two translations agree.
* A shared misunderstanding survives it: if `B` and `encode` both misread the problem the
  same way (say, both swap what "top row" means, or both pick the wrong endianness), the
  theorem still goes through.
* It is only as strong as the independence of the two definitions; see the warning on
  `encode`.
* Swapping the two summand rows is invisible to it. `B` asks for `row3 = row1 + row2`, and
  addition commutes, so a `B` that had the two top rows the other way round would prove the
  same theorem. Only the sum row is pinned down.
* The bounds `a, b, c < 2 ^ n` restrict the theorem to numbers representable in `n` bits.
  That is not a gap: it is the problem's no-overflow rule made explicit.
-/

/-- The `n`-bit big-endian bit string of `a`. Bits from position `n` up are dropped, so this
only spells out `a` itself when `a < 2 ^ n`; both uses below carry that hypothesis. -/
def bitsBE (n a : Nat) : List Bool := (List.range n).reverse.map a.testBit

/-- The word for the addition `a + b = c`, written in `n` columns: column `i` holds bit `i`
of each number, most significant column first.

Warning: the sanity check `encode_mem_B_iff` is only meaningful while this definition stays
stylistically independent of `valueLE`. Do not rewrite it as the step-by-step inverse of
`valueLE` (peeling `% 2` and `/ 2`); that would make the check essentially tautological rather
than an independent consistency check. -/
def encode (n a b c : Nat) : List Sigma3 :=
  (List.range n).reverse.map fun i => (a.testBit i, b.testBit i, c.testBit i)

/-- Extracting the top row of an encoded word gives back the bits of `a`. -/
lemma row1_encode (n a b c : Nat) : row1 (encode n a b c) = bitsBE n a := by
  simp [row1, encode, bitsBE, List.map_map, Function.comp]

/-- Extracting the middle row of an encoded word gives back the bits of `b`. -/
lemma row2_encode (n a b c : Nat) : row2 (encode n a b c) = bitsBE n b := by
  simp [row2, encode, bitsBE, List.map_map, Function.comp]

/-- Extracting the bottom row of an encoded word gives back the bits of `c`. -/
lemma row3_encode (n a b c : Nat) : row3 (encode n a b c) = bitsBE n c := by
  simp [row3, encode, bitsBE, List.map_map, Function.comp]

/-- Reading the first `n` bits of `a` least significant first recovers `a`, provided `a`
fits in `n` bits.

This is where the two translations meet: the left-hand side reads bits the way `valueLE`
does, the right-hand side produces them the way `encode` does
(by `Nat.testBit`). -/
lemma valueLE_range_testBit {n a : Nat} (h : a < 2 ^ n) :
    valueLE ((List.range n).map a.testBit) = a := by
  induction n generalizing a with
  | zero =>
    -- `a < 2 ^ 0` forces `a = 0`, and the empty bit string reads as `0`.
    simp only [pow_zero, Nat.lt_one_iff] at h
    simp [h, valueLE]
  | succ n induction_hypothesis =>
    -- Halving strips the low bit: `a / 2` fits in `n` bits.
    have hdiv : a / 2 < 2 ^ n := by
      rw [pow_succ] at h
      omega
    -- The tail bits of `a` are the bits of `a / 2`.
    have htail : a.testBit ∘ Nat.succ = (a / 2).testBit := by
      funext i
      exact Nat.testBit_succ a i
    -- The head bit of `a` is its parity.
    have hbit : (a.testBit 0).toNat = a % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with hpar | hpar <;> simp [Nat.testBit_zero, hpar]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, htail]
    simp only [valueLE]
    rw [induction_hypothesis hdiv, hbit]
    omega

/-- Reading an `n`-bit big-endian bit string most significant bit first recovers the number,
provided it fits in `n` bits. -/
lemma valueBE_bitsBE {n a : Nat} (h : a < 2 ^ n) : valueBE (bitsBE n a) = a := by
  rw [valueBE, bitsBE, List.map_reverse, List.reverse_reverse]
  exact valueLE_range_testBit h

/-- The sanity check: membership in `B` of an encoded word says exactly that the addition
holds, stated with plain numbers only.

The bounds are `B`'s implicit no-overflow rule made explicit: only sums representable in
`n` bits are in scope, because all three rows have the same length. -/
theorem encode_mem_B_iff {n : Nat} (a b c : Nat)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) :
    encode n a b c ∈ B ↔ c = a + b := by
  rw [mem_B_iff, row1_encode, row2_encode, row3_encode,
    valueBE_bitsBE ha, valueBE_bitsBE hb, valueBE_bitsBE hc]

/-! ### The check leaves no word out

`encode_mem_B_iff` speaks about the words `encode` builds. That would be a weak check if
`encode` only reached some words: the rest of `B` would go unexamined. It reaches all of
them. Reading a word's three rows as numbers and encoding those numbers back gives the word
again, so every word of length `n` is `encode n a b c` for some `a, b, c < 2 ^ n`. -/

/-- Reading a little-endian bit string as a number and asking for bit `i` gives bit `i` of
the string back. -/
lemma testBit_valueLE {bs : List Bool} {i : Nat} (h : i < bs.length) :
    (valueLE bs).testBit i = bs[i] := by
  induction bs generalizing i with
  | nil =>
    -- The empty string has no bit `i`.
    simp at h
  | cons b bs induction_hypothesis =>
    cases i with
    | zero =>
      -- Bit `0` of `b.toNat + 2 * valueLE bs` is its parity, which is `b`.
      cases b <;> simp [valueLE, Nat.testBit_zero]
    | succ i =>
      -- Bit `i + 1` is bit `i` after halving, and halving strips the leading bit off.
      rw [valueLE, Nat.testBit_succ]
      have hbit : b.toNat < 2 := Bool.toNat_lt b
      have hhalve : (b.toNat + 2 * valueLE bs) / 2 = valueLE bs := by omega
      rw [hhalve]
      simp only [List.getElem_cons_succ]
      exact induction_hypothesis (by simpa using h)

/-- The same for a big-endian string of known length `n`: bit `i` of the string is bit
`n - 1 - i` of the number, since big-endian counts positions the other way round. -/
lemma testBit_valueBE {bs : List Bool} {n i : Nat} (hn : bs.length = n) (h : i < n) :
    (valueBE bs).testBit (n - 1 - i) = bs[i]'(hn ▸ h) := by
  subst hn
  have hrev : bs.length - 1 - i < bs.reverse.length := by simp; omega
  have hidx : bs.length - 1 - (bs.length - 1 - i) = i := by omega
  -- `valueBE bs` is `valueLE bs.reverse`, so the bit is position `n - 1 - i` of the reverse.
  rw [valueBE, testBit_valueLE hrev]
  -- Indexing the reverse counts from the other end, which undoes the `n - 1 - ·`.
  simp [List.getElem_reverse, hidx]

/-- Every word is the encoding of the three numbers its own rows spell out. Together with
`encode_mem_B_iff` this makes the sanity check exhaustive: no word of `Σ₃*` escapes it. -/
theorem encode_rows (w : List Sigma3) :
    encode w.length (valueBE (row1 w)) (valueBE (row2 w)) (valueBE (row3 w)) = w := by
  -- Both sides have length `|w|`, so it is enough to compare them column by column.
  apply List.ext_getElem (by simp [encode])
  intro i _ hi
  -- Column `i` of the encoding holds bit `|w| - 1 - i` of each of the three numbers, because
  -- `encode` maps over `(List.range n).reverse`, whose `i`-th entry is `n - 1 - i`.
  simp only [encode, List.getElem_map, List.getElem_reverse, List.length_range,
    List.getElem_range]
  -- Each of those bits is the `i`-th bit of the row it came from.
  rw [testBit_valueBE (by simp [row1]) hi, testBit_valueBE (by simp [row2]) hi,
    testBit_valueBE (by simp [row3]) hi]
  -- The three rows at position `i` are the three components of column `i`.
  simp [row1, row2, row3]

/-- Encoding `3 + 1 = 4` in 3 bits gives the first example's word. -/
example : encode 3 3 1 4 =
    [(false, false, true), (true, false, false), (true, true, false)] := by decide

/-- Encoding `1 + 0 ≟ 3` in 2 bits gives the second example's word. -/
example : encode 2 1 0 3 =
    [(false, false, true), (true, false, true)] := by decide

end TheoryOfComputation.Chapter1.Problem32
