import Mathlib

namespace Misc.BezoutIdentity


-- Proof of Bezout's identity. There is already a proof in Mathlib, so this for educational purposes only.
--
-- The proof is the extended Euclidean algorithm written as a strong induction on `a`.
-- The Euclidean algorithm says gcd a b = gcd (b % a) a, and b % a < a, so the first
-- argument strictly decreases. That justifies strong induction on `a`.
--
-- The inductive step assumes we already have a Bezout combination for the smaller pair
-- (b % a, a), i.e. numbers x, y with
--     (b % a) * x + a * y = gcd (b % a) a
-- and turns it into one for (a, b). Substituting b % a = b - a * (b / a) and collecting
-- terms gives
--     a * (y - (b / a) * x) + b * x = gcd (b % a) a = gcd a b
-- so the new coefficients are (y - (b / a) * x, x). Everything happens in ℤ because the
-- coefficients can be negative, while a, b and the gcd stay in ℕ and get cast.
theorem bezout_identity : ∀ a b : ℕ, ∃ x y : ℤ, (a : ℤ) * x + (b : ℤ) * y = Nat.gcd a b := by
  -- Fix `a`, but keep `b` universally quantified: the inductive hypothesis is applied at a
  -- different `b` (namely `a`) than the one we are proving for, so `b` must stay general.
  intro a
  -- Strong induction on `a`: `ih` gives the statement for every natural number below `a`.
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b
    -- Split on whether `a` is zero, since the recursion step needs `0 < a` (to divide by `a`).
    rcases Nat.eq_zero_or_pos a with rfl | ha
    -- Base case a = 0: gcd 0 b = b, and 0 * 0 + b * 1 = b. `simp` closes it.
    · exact ⟨0, 1, by simp⟩
    -- Inductive step. Apply `ih` to `b % a`, which is legal because `b % a < a` when `0 < a`,
    -- and instantiate its universally quantified second argument at `a`. This yields
    --   h : (b % a) * x + a * y = gcd (b % a) a
    · obtain ⟨x, y, h⟩ := ih (b % a) (Nat.mod_lt b ha) a
      -- Supply the new coefficients; the remaining goal `?_` is the arithmetic identity
      --   a * (y - (b / a) * x) + b * x = gcd a b
      refine ⟨y - (b / a : ℕ) * x, x, ?_⟩
      -- The bridge between the two statements: rewrite the remainder in terms of b, a and b / a,
      -- as an equation in ℤ so it can be used by `ring` later.
      have key : ((b % a : ℕ) : ℤ) = (b : ℤ) - (a : ℤ) * ((b / a : ℕ) : ℤ) := by
        -- `Nat.div_add_mod b a : a * (b / a) + b % a = b` holds in ℕ; `exact_mod_cast` transports
        -- it to ℤ, pushing the casts through the multiplication and addition.
        have h2 : (a : ℤ) * ((b / a : ℕ) : ℤ) + ((b % a : ℕ) : ℤ) = (b : ℤ) := by
          exact_mod_cast Nat.div_add_mod b a
        -- Rearranging a linear equation: subtract a * (b / a) from both sides.
        linarith
      -- Three rewrites turn the goal into a pure ring identity:
      --   `Nat.gcd_rec a b`  : gcd a b = gcd (b % a) a, matching the gcd in `h`
      --   `← h`              : replaces that gcd by (b % a) * x + a * y
      --   `key`              : replaces every `b % a` by b - a * (b / a)
      rw [Nat.gcd_rec a b, ← h, key]
      -- What remains is an identity of polynomials in a, b, b / a, x, y over ℤ:
      --   a * (y - (b / a) * x) + b * x = (b - a * (b / a)) * x + a * y
      -- Both sides expand to a * y + b * x - a * (b / a) * x, so `ring` finishes.
      ring

-- Bezout's identity says gcd a b is *some* value of the linear form a * x + b * y. This says it is
-- the smallest positive one: `IsLeast S d` unfolds to `d ∈ S ∧ ∀ n ∈ S, d ≤ n`, so the proof has
-- two halves.
--   Membership: gcd a b is positive (given a or b is nonzero) and is representable, by the theorem
--   above.
--   Lower bound: gcd a b divides both a and b, hence divides every value a * x + b * y, and a
--   positive multiple of a number is at least that number.
-- The hypothesis `a ≠ 0 ∨ b ≠ 0` is needed: for a = b = 0 the form only ever takes the value 0, so
-- the set is empty and has no least element, while gcd 0 0 = 0.
theorem gcd_isLeast_linear (a b : ℕ) (hab : a ≠ 0 ∨ b ≠ 0) :
    IsLeast {n : ℕ | 0 < n ∧ ∃ x y : ℤ, (n : ℤ) = (a : ℤ) * x + (b : ℤ) * y} (Nat.gcd a b) := by
  constructor
  -- First half: gcd a b belongs to the set.
  · refine ⟨Nat.pos_of_ne_zero ?_, ?_⟩
    -- Positivity. `Nat.gcd_eq_zero_iff` turns `gcd a b = 0` into `a = 0 ∧ b = 0`, and `not_and_or`
    -- turns its negation into the disjunction we were handed.
    · simp only [ne_eq, Nat.gcd_eq_zero_iff, not_and_or]
      exact hab
    -- Representability is exactly Bezout, up to the orientation of the equation.
    · obtain ⟨x, y, h⟩ := bezout_identity a b
      exact ⟨x, y, h.symm⟩
  -- Second half: every element of the set is at least gcd a b.
  · rintro n ⟨hn, x, y, hxy⟩
    -- gcd a b divides all n = a*x + b*y, argued in ℤ where the linear form lives.
    have hd : (Nat.gcd a b : ℤ) ∣ (n : ℤ) := by
      -- Replace n by the linear form, then divide the two summands separately: gcd a b divides a
      -- and b (`Nat.gcd_dvd_left` / `Nat.gcd_dvd_right`, cast to ℤ), so it divides a * x and b * y.
      rw [hxy]
      exact dvd_add
        (((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a b))).mul_right x)
        (((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a b))).mul_right y)
    -- Bring the divisibility back to ℕ and conclude: a divisor of a positive number is at most it.
    exact Nat.le_of_dvd hn (Int.natCast_dvd_natCast.mp hd)

end Misc.BezoutIdentity
