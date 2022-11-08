import data.int.basic
import tactic.ring

/-
Bulgarian Mathematical Olympiad 1998, Problem 6

Prove that the equation

     x²y² = z²(z² - x² - y²)

has no solutions in positive integers.

-/

lemma lemma_1
  (s t u : ℤ)
  (hs : 0 < s)
  (ht : 0 < t)
  (hu : 0 < u)
  (h : s^4 - t^4 = u^2) :
  false :=
begin
  sorry
end

theorem bulgaria1998_q6
  (x y z : ℤ)
  (hx : 0 < x)
  (hy : 0 < y)
  (hz : 0 < z)
  (h : x^2 * y^2 = z^2 * (z^2 - x^2 - y^2)) :
  false :=
begin
  have : 0 = (z^2)^2 - z^2 * (x^2 + y^2) - x^2 * y^2 := by {rw[h], ring},
  sorry
end
