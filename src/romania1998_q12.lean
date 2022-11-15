import data.real.basic
import data.complex.exponential

/-
Romanian Mathematical Olympiad 1998, Problem 12

Find all functions u : ℝ → ℝ for which there exists a strictly monotoic
function f : ℝ → ℝ such that

  ∀ x,y ∈ ℝ, f(x + y) = f(x)u(y) + f(y)

-/

theorem romania1998_q12 (u : ℝ → ℝ) :
  (∃ f : ℝ → ℝ, ∀ x y : ℝ, f (x + y) = f x * u x + f y) ↔
  (∃ k : ℝ, k ≠ 0 ∧ ∀ x : ℝ, u x = real.exp (k * x)) :=
begin
  sorry
end
