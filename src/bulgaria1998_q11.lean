import data.nat.basic
import algebra.group_power.basic

/-
Bulgarian Mathematical Olympiad 1998, Problem 11

Let m,n be natural numbers such that

   A = ((m + 3)ⁿ + 1) / (3m)

is an integer. Prove that A is odd.

-/

theorem bulgaria1998_q11 (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) :
  odd A :=
begin
  by_contra he,
  sorry
end
