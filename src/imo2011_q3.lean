import data.real.basic

theorem imo2011Q3
  (f: ℝ → ℝ) (hf: ∀ x y, f (x + y) ≤ y * f x + f (f x))
  : (∀ x ≤ 0, f x = 0) :=
begin
  have hab: (∀ x t, f t ≤ t * f x - x * f x + f (f x)),
  {
    sorry,
  },
  sorry,
end
