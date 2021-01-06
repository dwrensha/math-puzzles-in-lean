import data.rat.basic
import data.rat.order

/-
Direct translation of solution found in https://www.imo-official.org/problems/IMO2013SL.pdf
-/

theorem imo2013Q4
  (f: ℚ → ℚ)
  (f_positive: ∀ x, 0 < f x)
  (f_i: ∀ x y, (0 < x ∧ 0 < y) → f (x * y) ≤ f x * f y)
  (f_ii: ∀ x y, (0 < x ∧ 0 < y) → f x + f y ≤ f (x + y))
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
  have hfn: ∀x: ℚ, (0 < x → ∀ n: ℕ, (↑n + 1) * f x ≤ f ((n + 1) * x)),
  {
    intros x hx n,
    induction n with pn hpn,
    { simp only [one_mul, nat.cast_zero, zero_add], },
    rw nat.cast_succ,
    calc (↑pn + 1 + 1) * f x = ((pn : ℚ) + 1) * f x + 1 * f x : add_mul (↑pn + 1) 1 (f x)
        ... = (↑pn + 1) * f x + f x : by rw one_mul
        ... ≤ f ((↑pn + 1) * x) + f x : add_le_add_right hpn (f x)
        ... ≤ f ((↑pn + 1) * x + x) : f_ii ((↑pn + 1) * x) x ⟨mul_pos (nat.cast_add_one_pos pn) hx, hx⟩
        ... = f ((↑pn + 1) * x + 1 * x) : by rw one_mul
        ... = f ((↑pn + 1 + 1) * x) : congr_arg f (add_mul (↑pn + 1) 1 x).symm
  },
  sorry,
end
