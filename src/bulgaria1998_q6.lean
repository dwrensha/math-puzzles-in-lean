import data.int.basic

/-
Bulgarian Mathematical Olympiad 1998, Problem 6

Prove that the equation

     x²y² = z²(z² - x² - y²)

has no solutions in positive integers.

-/

theorem bulgaria1998_q6
  (x y z : ℤ)
  (hx : 0 < x)
  (hy : 0 < y)
  (hz : 0 < z)
  (h : x^2 * y^2 = z^2 * (z^2 - x^2 - y^2)) :
  false :=
begin
  sorry
end
