import Batteries

namespace TheoryOfComputation

/-- 
# Problem 1.32

Let `Σ₃` be the alphabet of all 3-bit columns, i.e. `Bool × Bool × Bool`.
A string `w ∈ Σ₃*` therefore gives three rows of bits. Read each row as a
binary number, most significant bit first (all three rows have the same
length `|w|`, so no overflow is permitted). Define

    B = { w ∈ Σ₃*  |  value(row3 w) = value(row1 w) + value(row2 w) }

For example:

⎡ 0 ⎤⎡ 1 ⎤⎡ 1 ⎤
⎢ 0 ⎥⎢ 0 ⎥⎢ 1 ⎥ ∈ B, because 011 + 001 = 100
⎣ 1 ⎦⎣ 0 ⎦⎣ 0 ⎦

But 

⎡ 0 ⎤⎡ 1 ⎤
⎢ 0 ⎥⎢ 0 ⎥ ∉ B, because 01 + 00 ≠ 11
⎣ 1 ⎦⎣ 1 ⎦

## Solution

We can use the theorem that if a language is regular, then its reverse is
regular as well to simplify the problem. This way, we can iterate through the
reversed string and keep track of the carries to recognize a string (the string
is in B if the carry is zero at th end).

We can construct a DFA that recognizes B^R as follows (dead states are
omitted):

              000                              010
              011                              100
              101                              111
            ┌──────┐                        ┌──────┐
            │      ↓                        │      ↓
           ╔════════╗       110            ┌──────────┐
  start ──▶║   q0   ║───────────────────▶  │    q1    │
           ║ carry 0║  ◀───────────────────│ carry 1  │
           ╚════════╝       001            └──────────┘

-/
theorem todo: true := sorry

end TheoryOfComputation
