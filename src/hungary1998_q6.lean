import algebra.big_operators.pi
import data.int.basic

/-
Hungarian Mathematical Olympiad 1998, Problem 6

Let x, y, z be integers with z > 1. Show that

 (x + 1)² + (x + 2)² + ... + (x + 99)² ≠ y^z.
-/

open_locale big_operators

theorem hungary1998_q6 (x y : ℤ) (z : ℕ) (hz : 1 < z) :
    ∑(i : ℕ) in finset.range 99, (x + i + 1)^2 ≠ y^z :=
begin
 -- Suppose (x + 1)² + (x + 2)² + ... + (x + 99)² ≠ y^z.

 -- We notice that
 -- y^z = (x + 1)² + (x + 2)² + ... + (x + 99)²
 --     = 99x² + 2(1 + 2 + ... + 99)x + (1² + 2² + ... + 99²)
 --     = 99x² + 2[(99 ⬝ 100)/2]x + (99 ⬝ 100 ⬝ 199)/6
 --     = 33(3x² + 300x + 50 ⬝ 199).

 -- which implies that 3∣y. Since z ≥ 2, 3²∣y^z, but 3² does not divide
 -- 33(3x² + 300x + 50 ⬝ 199), contradiction.


 -- (note that mathlib has finset.sum_range_id)

 sorry
end
