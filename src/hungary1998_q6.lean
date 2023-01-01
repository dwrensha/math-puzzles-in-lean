import algebra.big_operators.pi
import data.int.basic

/-
Hungarian Mathematical Olympiad 1998, Problem 6

Let x, y, z be integers with z > 1. Show that

 (x + 1)² + (x + 2)² + ... + (x + 99)² ≠ y^z.
-/

open_locale big_operators

theorem hungary1998_q6 (x y) (z : ℕ) (hz : 1 < z) :
    ∑(i : ℕ) in finset.range 99, (x + i + 1)^2 ≠ y^z :=
begin
 sorry
end
