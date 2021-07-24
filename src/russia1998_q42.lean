import data.real.basic

/-
 Russian Mathematical Olympiad 1998, problem 42

 A binary operation ⋆ on real numbers has the property that (a ⋆ b) ⋆ c = a + b + c.
 Prove that a ⋆ b = a + b.

-/

theorem russion1998_q42 (star : ℝ → ℝ → ℝ) (h : ∀ a b c, star (star a b) c = a + b + c) :
  (∀ a b, star a b = a + b) :=
begin
  sorry
end
