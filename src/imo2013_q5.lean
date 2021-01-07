import data.rat.basic
import data.rat.order
import data.real.basic

/-
Direct translation of solution found in https://www.imo-official.org/problems/IMO2013SL.pdf
-/

theorem imo2013Q4
  (f: ℚ → ℝ)
  (f_i:  ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
  (f_ii: ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y))
  (f_iii: ∃ a, 1 < a ∧ f a = a)
  : ∀ x, 0 < x → f x = x :=
begin
  obtain ⟨a, ha1, hae⟩ := f_iii,
  have ha1r : 1 < (a:ℝ),
  {
    rw ←rat.cast_one,
    exact rat.cast_lt.mpr ha1,
  },
  have hf1: 1 ≤ f 1,
  {
    have := (f_i a 1) (lt_trans zero_lt_one ha1) zero_lt_one,
    rw [mul_one, hae] at this,
    have haz : 0 < (a:ℝ),
    {
      calc 0 < 1 : zero_lt_one
          ... < (a:ℝ) : ha1r
    },
    have h11 : ↑a * 1 ≤ ↑a * f 1 := by simpa only [mul_one],
    exact (mul_le_mul_left haz).mp h11,
  },
  have hfn: ∀x: ℚ, (0 < x → ∀ n: ℕ, (↑n + 1) * f x ≤ f ((n + 1) * x)),
  {
    intros x hx n,
    induction n with pn hpn,
    { simp only [one_mul, nat.cast_zero, zero_add], },
    rw nat.cast_succ,
    calc (↑pn + 1 + 1) * f x = ((pn : ℝ) + 1) * f x + 1 * f x : add_mul (↑pn + 1) 1 (f x)
        ... = (↑pn + 1) * f x + f x : by rw one_mul
        ... ≤ f ((↑pn + 1) * x) + f x : add_le_add_right hpn (f x)
        ... ≤ f ((↑pn + 1) * x + x) : f_ii ((↑pn + 1) * x) x (mul_pos (nat.cast_add_one_pos pn) hx) hx
        ... = f ((↑pn + 1) * x + 1 * x) : by rw one_mul
        ... = f ((↑pn + 1 + 1) * x) : congr_arg f (add_mul (↑pn + 1) 1 x).symm
  },
  have : ∀ q: ℚ, 0 < q → 0 < f q,
  {
    intros q hq,
    have hqn : (q.num: ℚ) = q * (q.denom : ℚ) := rat.mul_denom_eq_num.symm,
    have : f q.num ≤ f q * f q.denom,
    {
      have := f_i q q.denom hq (nat.cast_pos.mpr q.pos),
      rwa hqn,
    },
    sorry,
  },
  sorry,
end
