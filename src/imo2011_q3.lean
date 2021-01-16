import data.real.basic

/-
Direct translation of the solution found in https://www.imo-official.org/problems/IMO2011SL.pdf
-/

theorem imo2011Q3
  (f: ℝ → ℝ) (hf: ∀ x y, f (x + y) ≤ y * f x + f (f x))
  : (∀ x ≤ 0, f x = 0) :=
begin
  have hxt: (∀ x t, f t ≤ t * f x - x * f x + f (f x)),
  {
    intros x t,
    have h := (hf x (t - x)),
    rw (add_eq_of_eq_sub' rfl) at h,
    linarith,
  },
  have hab: (∀ a b, f (f a) - f (f b) ≤ (f a) * (f b) - b * f b ∧
                    f (f b) - f (f a) ≤ (f a) * (f b) - a * f a),
  {
     intros a b,
     have h1 := hxt b (f a),
     have h2 := hxt a (f b),
     split; linarith,
  },
  have hab1: (∀ a b, a * f a + b * f b ≤ 2 * f a * f b),
  {
    intros a b,
    have h := hab a b,
    linarith,
  },
  have ha: (∀ a < 0, 0 ≤ f a),
  {
     intros a han,
     have h := hab1 a (2 * f a),
     simp only [add_le_iff_nonpos_left] at h,
     exact nonneg_of_mul_nonpos_right h han,
  },
  have hx: (∀ x, f x ≤ 0),
  {
    intros x,
    by_contra,
    have hp : 0 < f x := not_le.mp h,
    let s := ((x * f x - f (f x)) / (f x)),
    have h' := hxt x (min 0 s - 1),
    have hm : min 0 s - 1 < s,
    {
      have := min_le_right 0 s,
      linarith,
    },
    have hml : min 0 s - 1 < 0,
    {
      have := min_le_left 0 s,
      linarith,
    },

    have hm1 : (min 0 s - 1) * f x < s * f x := (mul_lt_mul_right hp).mpr hm,

    have hmz: f (min 0 s - 1) < 0 :=
      calc f (min 0 s - 1)
           ≤ (min 0 s - 1) * f x - x * f x + f (f x) : h'
      ...  < s * f x - x * f x + f (f x) : by linarith
      ...  = 0 : by rw ((eq_div_iff (ne.symm (ne_of_lt hp))).mp rfl); linarith,

    have hmp : 0 ≤ f (min 0 s - 1) := ha (min 0 s - 1) hml,
    linarith,
  },
  have hn: (∀x < 0, f x = 0),
  {
    intros x hxz,
    exact le_antisymm (hx x) (ha x hxz)
  },
  have hz: f 0 = 0,
  {
    have hno := hn (-1) neg_one_lt_zero;
    have hp := hxt (-1) (-1),
    rw hno at hp,
    simp only [sub_zero, zero_add, mul_zero] at hp,
    exact le_antisymm (hx 0) hp,
  },
  intros x hx,
  have hcases : x < 0 ∨ x = 0 := lt_or_eq_of_le hx,
  cases hcases,
  {
    exact hn x hcases,
  },
  rwa hcases,
end
