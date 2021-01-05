import data.rat.basic
import data.rat.order

theorem imo2013Q4
  (f: ℚ → ℚ)
  (f_positive: ∀ x, 0 < f x)
  (f_i: ∀ x y, (0 < x ∧ 0 < y) → f (x * y) ≤ f x * f y)
  (f_ii: ∀ x y, (0 < x ∧ 0 < y) → f (x + y) ≤ f x + f y)
  (f_iii: ∃ a, 1 < a ∧ f a = a)
  : ∀ x, 0 < x → f x = x :=
begin
  obtain ⟨a, ha1, hae⟩ := f_iii,
  have hf1: 1 ≤ f 1,
  {
    have := (f_i a 1) ⟨lt_trans zero_lt_one ha1, zero_lt_one⟩,
    rw mul_one at this,
    exact (le_mul_iff_one_le_right (f_positive a)).mp this
  },
  sorry,
end
