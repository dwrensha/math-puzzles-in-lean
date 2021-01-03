import data.real.basic

theorem imo2011Q3
  (f: ℝ → ℝ) (hf: ∀ x y, f (x + y) ≤ y * f x + f (f x))
  : (∀ x ≤ 0, f x = 0) :=
begin
  have hxt: (∀ x t, f t ≤ t * f x - x * f x + f (f x)),
  {
    intros x t,
    have h := (hf x (t - x)),
    conv at h begin
      congr,
      { congr,
        simp,
        skip,
      },
      ring,
      congr,
      {
        skip,
      },
      congr,
      { ring,
        skip, },
      skip,
    end,
    ring,
    exact h,
  },
  have hab: (∀ a b, f (f a) - f (f b) ≤ (f a) * (f b) - b * f b ∧
                    f (f b) - f (f a) ≤ (f a) * (f b) - a * f a),
  {
    sorry,
  },
  have hab1: (∀ a b, a * f a + b * f b ≤ 2 * f a * f b),
  {
    intros a b,
    have h := hab a b,
    cases h,
    sorry,
  },
  have ha: (∀ a < 0, 0 ≤ f a),
  {
     intros a han,
     have h := hab1 a (2 * f a),
     simp at h,
     exact nonneg_of_mul_nonpos_right h han,
  },
  have hx: (∀ x, f x ≤ 0),
  {
    sorry,
  },
  have hn: (∀x < 0, f x = 0),
  {
    intros x hxz,
    exact le_antisymm (hx x) (ha x hxz)
  },
  have hz: f 0 = 0,
  {
    sorry,
  },
  intros x hx,
  sorry,
end
