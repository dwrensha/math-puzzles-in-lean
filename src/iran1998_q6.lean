import data.nat.basic
import data.pnat.basic

/-
Iranian Mathematical Olympiad 1998, Problem 6

Let x,a,b be positive integers such that x^(a+b) = a^b * b. Prove
that a = x and b = x^x.
-/

theorem iran1998_q6
  (x a b : ℕ)
  (hx : 0 < x)
  (ha : 0 < a)
  (hb : 0 < b)
  (h : x^(a+b) = a^b * b)
 : a = x ∧ b = x^x :=
begin
  sorry
end
