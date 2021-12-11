import data.real.basic

/-
Iranian Mathematical Olympiad 1998, problem 11

Let f₁, f₂, f₃ : ℝ → ℝ be functions such that

  a₁f₁ + a₂f₂ + a₃f₃

is monotonic for all a₁,a₂,a₃ ∈ ℝ. Prove that there exist c₁,c₂,c₃ ∈ ℝ, not all zero,
such that

  c₁f₁(x) + c₂f₂(x) + c₃f₃(x) = 0

for all x ∈ ℝ.
-/

theorem iran1998_q11
  (f₁ f₂ f₃ : ℝ -> ℝ)
  (hf : (∀a₁ a₂ a₃ : ℝ, monotone (λ x, a₁ * f₁ x + a₂ * f₂ x + a₃ * f₃ x))) :
  ∃c₁ c₂ c₃ : ℝ, (¬ (c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0) ∧
                  ∀ x, c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x = 0) :=
begin
  sorry
end
