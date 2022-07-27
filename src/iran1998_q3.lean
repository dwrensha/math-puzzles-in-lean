import data.real.basic

open_locale big_operators

/-
Iranian Mathematical Olympiad 1998, problem 3

Let x₁, x₂, x₃, x₄ be positive real numbers such that

  x₁ ⬝ x₂ ⬝ x₃ ⬝ x₄ = 1.

Prove that
  x₁³ + x₂³ + x₃³ + x₄³ ≥ max(x₁ + x₂ + x₃ + x₄, 1/x₁ + 1/x₂ + 1/x₃ + 1/x₄).

-/

theorem iran1998_q3
  (x : fin 4 → ℝ)
  (x_positive : ∀ i, 0 < x i)
  (h : ∏ (i : fin 4), x i = 1)
  : max (∑(i : fin 4), x i) (∑(i : fin 4), 1 / x i) ≤ ∑ (i : fin 4), (x i)^3 :=
begin
  let A := ∑ (i : fin 4), (x i)^3,
  let B : fin 4 → ℝ := λ i, A - (x i)^3,
  have : A = (1/3) * (∑ (i : fin 4), B i),
  { sorry },
  sorry
end
