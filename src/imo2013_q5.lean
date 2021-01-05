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
sorry,
end
