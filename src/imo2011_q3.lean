import data.real.basic

lemma less_than_both (a b : ℝ) : (∃ c, c < a ∧ c < b) :=
begin
  use (min a b - 1),
  have ha := min_le_right a b,
  have ha := min_le_left a b,
  split,
  linarith,
  linarith,
end

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
     simp at h,
     exact nonneg_of_mul_nonpos_right h han,
  },
  have hx: (∀ x, f x ≤ 0),
  {
    intros x,
    classical,
    by_contra,
    have hp : 0 < f x := not_le.mp h,
    let s := ((x * f x - f (f x)) / (f x)),
    have h' := hxt x (min 0 s - 1),
    sorry,
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
    simp at hp,
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
