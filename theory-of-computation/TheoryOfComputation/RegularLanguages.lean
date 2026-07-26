import Batteries

namespace TheoryOfComputation

/-- 
Problem 1.32

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

-/
theorem todo: true := sorry

end TheoryOfComputation
