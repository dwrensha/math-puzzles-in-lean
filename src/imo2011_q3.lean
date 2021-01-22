import data.real.basic

/-!
# IMO 2011 Q3

Let f : ℝ → ℝ be a function that satisfies

   f(x + y) ≤ y * f(x) + f(f(x))

for all x and y. Prove that f(x) = 0 for all x ≤ 0.

# Solution

Direct translation of the solution found in https://www.imo-official.org/problems/IMO2011SL.pdf
-/

theorem imo2011_q3
  (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) ≤ y * f x + f (f x))
  : ∀ x ≤ 0, f x = 0 :=
begin
  -- reparameterize
  have hxt : (∀ x t, f t ≤ t * f x - x * f x + f (f x)),
  { intros x t,
    calc f t = f (x + (t - x))             : by rw (add_eq_of_eq_sub' rfl)
         ... ≤ (t - x) * f x + f (f x)     : hf x (t - x)
         ... = t * f x - x * f x + f (f x) : by rw sub_mul },

  have hab : (∀ a b, f (f a) - f (f b) ≤ (f a) * (f b) - b * f b ∧
                     f (f b) - f (f a) ≤ (f a) * (f b) - a * f a),
  { intros a b,
    split; linarith [hxt b (f a), hxt a (f b)] },

  have hab_combined : (∀ a b, a * f a + b * f b ≤ 2 * f a * f b),
  { intros a b,
    linarith [hab a b] },

  have ha : (∀ a < 0, 0 ≤ f a),
  { intros a han,
    suffices : a * f a ≤ 0, from nonneg_of_mul_nonpos_right this han,
    exact add_le_iff_nonpos_left.mp (hab_combined a (2 * f a)) },

  have h_fx_nonpos : (∀ x, f x ≤ 0),
  { intros x,
    by_contra,
    have hp : 0 < f x := not_le.mp h,
    let s := ((x * f x - f (f x)) / (f x)),
    have hm : min 0 s - 1 < s := by linarith [min_le_right 0 s],
    have hml : min 0 s - 1 < 0 := by linarith [min_le_left 0 s],

    have hmz : f (min 0 s - 1) < 0 :=
      calc f (min 0 s - 1)
           ≤ (min 0 s - 1) * f x - x * f x + f (f x) : hxt x (min 0 s - 1)
      ...  < s * f x - x * f x + f (f x) : by linarith [(mul_lt_mul_right hp).mpr hm]
      ...  = 0 : by rw ((eq_div_iff (ne.symm (ne_of_lt hp))).mp rfl); linarith,

    have hmp : 0 ≤ f (min 0 s - 1) := ha (min 0 s - 1) hml,
    linarith },

  have h_fx_zero_of_neg : (∀ x < 0, f x = 0),
  { intros x hxz,
    exact le_antisymm (h_fx_nonpos x) (ha x hxz) },

  have h_zero_of_zero : f 0 = 0,
  { suffices : 0 ≤ f 0, from le_antisymm (h_fx_nonpos 0) this,
    have hno : f (-1) = 0 := h_fx_zero_of_neg (-1) neg_one_lt_zero,
    have hp := hxt (-1) (-1),
    rw hno at hp,
    linarith },

  intros x hx,
  have hcases : x < 0 ∨ x = 0 := lt_or_eq_of_le hx,

  cases hcases,
  { exact h_fx_zero_of_neg x hcases },
  rw hcases,
  exact h_zero_of_zero
end
