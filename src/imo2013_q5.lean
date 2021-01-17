import algebra.geom_sum
import data.rat.basic
import data.rat.order
import data.real.basic

/-!
# IMO 2013 Q5
This is a direct translation of the solution found in
https://www.imo-official.org/problems/IMO2013SL.pdf
-/

open_locale big_operators

lemma factor_xn_minus_yn (x : ℝ) (y : ℝ) (n : ℕ)
      :  x^n - y^n = (x - y) * (∑ (i:ℕ) in finset.range n, (x ^(i) * y ^(n - 1 -i))) :=
begin
  have := geom_sum₂_mul_add (x-y) y n,
  rw [sub_add_cancel x y, geom_series₂_def] at this,
  nlinarith,
end

lemma le_of_all_pow_lt_succ (x y : ℝ) (hx : 1 < x) (hy : 1 < y)
      (h : ∀n:ℕ, 0 < n → x^n - 1 < y^n)
      : x ≤ y :=
begin
   by_contra hxy,
   push_neg at hxy,
   have hxmy : 0 < x - y := sub_pos.mpr hxy,
   have hn: (∀n:ℕ, 0 < n → (x - y) * (n:ℝ) ≤ x^n - y^n),
   {
     intros n hn,
     have hterm : (∀i:ℕ, i ∈ finset.range n → 1 ≤ x^i * y^(n - 1 - i)),
     {
       intros i hi,
       have hx' : 1 ≤ x ^ i := one_le_pow_of_one_le (le_of_lt hx) i,
       have hy' : 1 ≤ y ^ (n - 1 - i) := one_le_pow_of_one_le (le_of_lt hy) (n - 1 - i),
       nlinarith,
     },
     have : ((n:ℝ) = (∑ (i : ℕ) in finset.range n, (1:ℝ))),
     {
       simp only [mul_one, finset.sum_const, nsmul_eq_mul, finset.card_range]
     },

     calc (x - y) * (n:ℝ)
             = (x - y) *  (∑ (i : ℕ) in finset.range n, (1:ℝ))
               : by simp only [mul_one, finset.sum_const, nsmul_eq_mul, finset.card_range]
         ... ≤ (x-y) * (∑ (i : ℕ) in finset.range n, x ^ i * y ^ (n - 1 - i))
               : (mul_le_mul_left hxmy).mpr (finset.sum_le_sum hterm)
         ... = x^n - y^n : (factor_xn_minus_yn x y n).symm,
   },

   -- Choose n larger than 1 / (x - y).
   obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - y)),
   have hNpr : (0:ℝ) < N := lt_trans (one_div_pos.mpr hxmy) hN,
   have hNp : 0 < N,
   {
      cases N,
      { exfalso, exact lt_asymm hNpr hNpr },
      exact nat.succ_pos N
   },

   have := calc 1 = (x - y) * (1 / (x - y)) : by field_simp [ne_of_gt hxmy]
              ... < (x - y) * N             : (mul_lt_mul_left hxmy).mpr hN
              ... ≤ x^N - y^N               : hn N hNp,
   linarith [h N hNp],
end

/--
 Like le_of_all_pow_lt_succ, but with a weaker assumption for y.
-/
lemma le_of_all_pow_lt_succ' (x y: ℝ) (hx: 1 < x) (hy: 0 < y)
      (h: ∀n:ℕ, 0 < n → x^n - 1 < y^n)
      : x ≤ y :=
begin
  have hy': 1 < y,
  {
    by_contra hy'',
    push_neg at hy'', -- hy'' :  y ≤ 1.

    -- Then there exists y' such that 0 < y ≤ 1 < y' < x.
    let y' := (x + 1) / 2,
    have h_y'_lt_x: y' < x,
    {
      have hh: (x + 1)/2 < (x * 2) / 2 := by linarith,
      calc y' < (x * 2) / 2 : hh
          ... = x : by field_simp
    },
    have h1_lt_y' : 1 < y',
    {
      have hh': 1 * 2 / 2 < (x + 1) / 2 := by linarith,
      calc 1 = 1 * 2 / 2 : by field_simp
         ... < y' : hh'
    },
    have h_y_lt_y' := calc y ≤ 1 : hy''
                         ... < y': h1_lt_y',
    have hh: (∀ n, 0 < n → x^n - 1 < y'^n),
    {
      intros n hn,
      calc x^n - 1 < y^n : h n hn
              ...  ≤ y'^n : pow_le_pow_of_le_left (le_of_lt hy) (le_of_lt h_y_lt_y') n
    },
    have : x ≤ y' := le_of_all_pow_lt_succ x y' hx h1_lt_y' hh,
    linarith, -- contradiction
  },
  exact le_of_all_pow_lt_succ x y hx hy' h
end

lemma power_bound (n: ℕ) (ε:ℚ) (ha: 0 < ε) : 1 + (n:ℚ) * ε ≤ (1 + ε)^n :=
begin
  induction n with pn hpn,
  { simp only [add_zero, nat.cast_zero, zero_mul, pow_zero] },

  have hpnp : 0 ≤ (pn:ℚ) := nat.cast_nonneg pn,
  have hpnep: 0 ≤ (pn:ℚ) * ε := (zero_le_mul_right ha).mpr hpnp,
  have hpp := calc 1 ≤ 1 + (pn:ℚ) * ε : le_add_of_nonneg_right hpnep
                ...  ≤ (1+ε)^pn : hpn,
  have hppe : ε ≤ ε * (1+ ε)^pn := (le_mul_iff_one_le_right ha).mpr hpp,

  calc 1 + ↑(pn.succ) * ε
       = 1 + (↑pn * ε + 1 * ε) : by simp only [one_mul, nat.cast_succ, add_right_inj]; ring
   ... = (1 + ↑pn * ε) + 1 * ε : (add_assoc 1 (↑pn * ε) (1 * ε)).symm
   ... = (1 + ↑pn * ε) + ε : by rw one_mul
   ... ≤ (1 + ε) ^ pn + ε : add_le_add_right hpn ε
   ... ≤ (1 + ε) ^ pn + ε * (1 + ε)^pn : add_le_add_left hppe ((1 + ε) ^ pn)
   ... = 1 * (1 + ε) ^ pn + ε * (1 + ε)^pn : by ring
   ... = (1 + ε) * (1 + ε) ^ pn : by ring
   ... = (1 + ε) ^ (pn.succ) : (pow_succ (1+ε) pn).symm,
end

lemma twice_pos_int_gt_one (z: ℤ) (hpos: 0 < z) : (1:ℚ) < (((2 * z):ℤ):ℚ) :=
by { norm_cast, linarith }

theorem imo2013_q5
  (f: ℚ → ℝ)
  (H1:  ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
  (H2: ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y))
  (H_fixed_point: ∃ a, 1 < a ∧ f a = a)
  : ∀ x, 0 < x → f x = x :=
begin
  obtain ⟨a, ha1, hae⟩ := H_fixed_point,
  have H3: ∀x: ℚ, (0 < x → ∀ n: ℕ, 0 < n → ↑n * f x ≤ f (n * x)),
  {
    intros x hx n hn,
    cases n,
    { exfalso, exact nat.lt_asymm hn hn },
    induction n with pn hpn,
    { simp only [one_mul, nat.cast_one] },
    calc (↑pn + 1 + 1) * f x = ((pn : ℝ) + 1) * f x + 1 * f x : add_mul (↑pn + 1) 1 (f x)
        ... = (↑pn + 1) * f x + f x : by rw one_mul
        ... = (↑pn.succ) * f x + f x : by norm_cast
        ... ≤ f ((↑pn.succ) * x) + f x : add_le_add_right (hpn (nat.succ_pos pn)) (f x)
        ... ≤ f ((↑pn + 1) * x) + f x : by norm_cast
        ... ≤ f ((↑pn + 1) * x + x) : H2 ((↑pn + 1) * x) x (mul_pos (nat.cast_add_one_pos pn) hx) hx
        ... = f ((↑pn + 1) * x + 1 * x) : by rw one_mul
        ... = f ((↑pn + 1 + 1) * x) : congr_arg f (add_mul (↑pn + 1) 1 x).symm
  },
  have H4: (∀ n : ℕ, 0 < n → (n: ℝ) ≤ f n),
  {
    intros n hn,
    have hf1: 1 ≤ f 1,
    {
      have := (H1 a 1) (lt_trans zero_lt_one ha1) zero_lt_one,
      rw [mul_one, hae] at this,
      have haz := calc 0 < 1     : zero_lt_one
                     ... < (a:ℝ) : by {norm_cast, exact ha1},

      have h11 : ↑a * 1 ≤ ↑a * f 1 := by simpa only [mul_one],
      exact (mul_le_mul_left haz).mp h11,
    },

    calc (n: ℝ) = (n: ℝ) * 1   : by simp only [mul_one]
            ... ≤ (n: ℝ) * f 1 : (mul_le_mul_left (nat.cast_pos.mpr hn)).mpr hf1
            ... ≤ f (n * 1)    : H3 1 zero_lt_one n hn
            ... = f n          : by rw mul_one
  },
  have hqp: ∀ q: ℚ, 0 < q → 0 < f q,
  {
    intros q hq,
    have hqn : (q.num: ℚ) = q * (q.denom : ℚ) := rat.mul_denom_eq_num.symm,
    have hfqn : f q.num ≤ f q * f q.denom,
    {
      have := H1 q q.denom hq (nat.cast_pos.mpr q.pos),
      rwa hqn,
    },
    have hqd: (q.denom: ℝ) ≤ f q.denom := H4 q.denom q.pos,
    have hqnp: 0 < q.num := rat.num_pos_iff_pos.mpr hq,
    have hqna: ((int.nat_abs q.num):ℤ) = q.num := int.nat_abs_of_nonneg (le_of_lt hqnp),
    have hqfn': (q.num: ℝ) ≤ f q.num,
    {
      rw ←hqna at hqnp,
      have := H4 q.num.nat_abs (int.coe_nat_pos.mp hqnp),
      rw ←hqna,
      rwa [int.cast_coe_nat q.num.nat_abs],
    },
    have hqnz := calc (0:ℝ) < q.num : int.cast_pos.mpr hqnp
                        ... ≤ f q.num : hqfn',
    have hqdz :=
      calc (0:ℝ) < q.denom : nat.cast_pos.mpr q.pos
         ... ≤ f q.denom : hqd,
    nlinarith,
  },
  have hfx_gt_xm1 : (∀x:ℚ, 1 ≤ x → ((((x - 1): ℚ)):ℝ) < f x),
  {
     intros x hx,
     have hfe : ((⌊x⌋).nat_abs : ℤ) = ⌊x⌋,
     {
       have hzx := calc 0 ≤ 1 : zero_le_one
                      ... ≤ x: hx,
       exact int.nat_abs_of_nonneg (floor_nonneg.mpr hzx),
     },
     have hfe' : ((⌊x⌋).nat_abs : ℚ) = ⌊x⌋,
     {
       conv begin to_rhs, rw ← hfe end,
       simp only [int.cast_coe_nat],
     },
     have h_nab_abs_floor_pos : 0 < (⌊x⌋).nat_abs,
     {
       suffices: 0 < ⌊x⌋,
       { exact int.nat_abs_pos_of_ne_zero (ne_of_gt this), },
       have := calc 0 ≤ x - 1 : by linarith
                  ... < ⌊x⌋   : sub_one_lt_floor x,
       exact int.cast_pos.mp this,
     },
     have hx0 := calc (((x - 1):ℚ):ℝ)
                    < ⌊x⌋   : by norm_cast; exact sub_one_lt_floor x
                ... ≤ f ⌊x⌋ : begin have := H4 (⌊x⌋).nat_abs h_nab_abs_floor_pos,
                                    rw ←(rat.cast_coe_nat (⌊x⌋).nat_abs) at this,
                                    rw hfe' at this,
                                    rwa (rat.cast_coe_int ⌊x⌋) at this,
                               end,

     have ho: (⌊x⌋:ℚ) = x ∨ (⌊x⌋:ℚ) < x := eq_or_lt_of_le (floor_le x),
     cases ho,
     { rwa ho at hx0 },

     have hxmfx : 0 < (x - ⌊x⌋) := by linarith,
     have h0fx := calc (0:ℚ) < 1 : zero_lt_one
                         ... = (int.has_one.one : ℚ) : by simp only [int.cast_one]
                         ... ≤ ⌊x⌋ : int.cast_le.mpr (le_floor.mpr hx),

     calc (((x - 1):ℚ):ℝ) < f ⌊x⌋ : hx0
                  ... < f (x - ⌊x⌋) + f ⌊x⌋ : lt_add_of_pos_left (f ↑⌊x⌋) (hqp (x - ↑⌊x⌋) hxmfx)
                  ... ≤ f ((x - ⌊x⌋) + ⌊x⌋) : H2 (x - ⌊x⌋) ⌊x⌋ hxmfx h0fx
                  ... = f x : by simp only [sub_add_cancel]
  },
  have hfxn : (∀n:ℕ, 0 < n → ∀ x:ℚ, 1 < x → f (x^n) ≤ (f x)^n),
  {
    intros n hn x hx,
    induction n with pn hpn,
    { exfalso, exact nat.lt_asymm hn hn },
    cases pn,
    { simp only [pow_one] },
    have hpn' := hpn (nat.succ_pos pn),
    rw [pow_succ' x (nat.succ pn), pow_succ' (f x) (nat.succ pn)],
    have hxp := calc 0 < 1 : zero_lt_one
                   ... < x : hx,
    have hfnp: 0 < f x := hqp x hxp,
    calc f ((x ^ pn.succ) * x)
         ≤ f (x ^ pn.succ) * f x : H1 (x ^ pn.succ) x (pow_pos hxp pn.succ) hxp
     ... ≤ (f x) ^ pn.succ * f x : (mul_le_mul_right hfnp).mpr hpn'
  },
  have H5 : (∀x:ℚ, 1 < x → (x:ℝ) ≤ f x),
  {
    intros x hx,
    have hxnm1: (∀ n : ℕ, 0 < n → (x:ℝ)^n - 1 < (f x)^n),
    {
      intros n hn,
      calc (x:ℝ)^n - 1
           = (((x^n - 1):ℚ):ℝ) : by norm_cast
       ... < f (x^n) : hfx_gt_xm1 (x^n) (one_le_pow_of_one_le (le_of_lt hx) n)
       ... ≤ (f x)^n : hfxn n hn x hx
    },
    have hx': 1 < (x:ℝ) := by { norm_cast, exact hx },
    have hxp := calc 0 < 1 : zero_lt_one
                   ... < x : hx,

    exact le_of_all_pow_lt_succ' x (f x) hx' (hqp x hxp) hxnm1,
  },
  have h_fixed_point_of_pos_nat_pow : (∀n, 0 < n → f (a^n) = a^n),
  {
    intros n hn,
    have hh0: (a:ℝ)^n ≤ f (a^n),
    {
      have := H5 (a^n) (one_lt_pow ha1 (nat.succ_le_iff.mpr hn)),
      norm_cast,
      exact this,
    },
    have hh1: f (a^n) ≤ a^n := by { rw ← hae, exact hfxn n hn a ha1 },
    exact le_antisymm hh1 hh0
  },
  have h_fixed_point_of_gt_1: (∀x:ℚ, 1 < x → f x = x),
  {
    intros x hx,
    -- choose n such that 1 + x < a^n.
    have hbound: (∀m:ℕ, 1 + (m:ℚ) * (a - 1) ≤ a^m),
    {
      intros m,
      have haa: (1 + (a - 1)) = a := by ring,
      have := power_bound m (a - 1) (sub_pos.mpr ha1),
      rwa haa at this,
    },

    -- Choose n greater than x / (a - 1).
    obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (x / (a - 1))),
    have hN' := calc x / (a - 1) ≤ max 0 (x / (a - 1)) : le_max_right _ _
                             ... < N : hN,
    have h_big_enough :=
      calc (1:ℚ)
          = 1 + 0                           : rfl
      ... = (1 + N * (a - 1)) - N * (a - 1) : by ring
      ... ≤ a^N - N * (a - 1)               : sub_le_sub_right (hbound N) (↑N * (a - 1))
      ... < a^N - (x / (a - 1)) * (a - 1)   : sub_lt_sub_left
                                              ((mul_lt_mul_right (sub_pos.mpr ha1)).mpr hN') (a^N)
      ... = a^N - x                         : by field_simp [ne_of_gt (sub_pos.mpr ha1)],

    have h1 := calc (x:ℝ) + (((a^N - x):ℚ):ℝ)
                      ≤ f x + (((a^N - x):ℚ):ℝ) : add_le_add_right (H5 x hx) _
                  ... ≤ f x + f (a^N - x)       : add_le_add_left (H5 _ h_big_enough) _,

    have haNxp := calc (0:ℚ) < 1       : zero_lt_one
                         ... < a^N - x : h_big_enough,

    have hxp := calc (0:ℚ) < 1 : zero_lt_one
                       ... < x : hx,
    have hNp : 0 < N,
    {
      have hh:= calc (0:ℚ) ≤ max 0 (x / (a - 1)) : le_max_left 0 _
                       ... < N                   : hN,
      have : (0:ℚ) = ((0:ℕ):ℚ) := nat.cast_zero.symm,
      rw this at hh,
      norm_cast at hh,
      exact hh,
    },

    have h2 := calc f x + f (a^N - x)
            ≤ f (x + (a^N - x)) : H2 x (a^N - x) hxp haNxp
        ... = f (a^N) : by ring
        ... = a^N : h_fixed_point_of_pos_nat_pow N hNp
        ... = x + (a^N - x): by ring
        ... = x + (((a^N - x):ℚ):ℝ): by norm_cast,

    have heq := le_antisymm h1 h2,
    linarith [H5 x hx, H5 _ h_big_enough],
  },

  have h_fixed_point_of_pos_nat_mul : (∀n:ℕ, 0 < n → ∀x:ℚ, 0 < x → f (n * x) = n * f x),
  {
    intros n hn x hx,
    have h2: f (n * x) ≤ n * f x,
    {
      cases n,
      { exfalso, exact nat.lt_asymm hn hn },
      cases n,
      { simp only [one_mul, nat.cast_one] },
      have hfneq : f (n.succ.succ) = n.succ.succ,
      {
        have := h_fixed_point_of_gt_1 (n.succ.succ:ℚ) (nat.one_lt_cast.mpr (nat.succ_lt_succ (nat.succ_pos n))),
        rwa (rat.cast_coe_nat n.succ.succ) at this,
      },
      rw ← hfneq,
      exact H1 (n.succ.succ:ℚ) x (nat.cast_pos.mpr hn) hx,
    },
    exact le_antisymm h2 (H3 x hx n hn),
  },
  intros x hx,
  have hrat_expand: x = x.num / x.denom,
  { norm_cast, exact rat.num_denom.symm },

  have hxcnez: (x.denom:ℚ) ≠ (0:ℚ) := ne_of_gt (nat.cast_pos.mpr x.pos),
  have hxcnezr: (x.denom:ℝ) ≠ (0:ℝ) := ne_of_gt (nat.cast_pos.mpr x.pos),

  -- For the final calculation, we expand x as (2*x.num) / (2*x.denom), because
  -- we need the top of the fraction to be strictly greater than 1 in order
  -- to apply h_fixed_point_of_gt_1.

  let x2denom := 2 * x.denom,
  let x2num := 2 * x.num,

  have hx2num_gt_one : (1:ℚ) < x2num := twice_pos_int_gt_one x.num (rat.num_pos_iff_pos.mpr hx),

  have hx2pos := calc 0 < x.denom           : x.pos
                    ... < x.denom + x.denom : lt_add_of_pos_left x.denom x.pos
                    ... = 2 * x.denom       : by ring,

  have hx2cnez: (x2denom:ℚ) ≠ (0:ℚ) := by field_simp,
  have hx2cnezr: (x2denom:ℝ) ≠ (0:ℝ) := by field_simp,

  have hrat_expand2 := calc x = x.num / x.denom : hrat_expand
                          ... = x2num / x2denom : by field_simp; linarith,

  have h_denom_times_fx := calc
               (x2denom:ℝ) * f x
             = f (x2denom * x)
                    : (h_fixed_point_of_pos_nat_mul x2denom hx2pos x hx).symm
         ... = f (x2denom * (x2num / x2denom)) : by rw hrat_expand2
         ... = f ((x2denom * x2num) / x2denom) : by rw mul_div_assoc
         ... = f ((x2num * x2denom) / x2denom) : by rw mul_comm
         ... = f (x2num * (x2denom / x2denom)) : by rw ←mul_div_assoc
         ... = f (x2num * 1)                   : by rw (div_self hx2cnez)
         ... = f (x2num)                       : by rw mul_one,

  have h_fx2num_fixed : f x2num = x2num,
  { have hh := h_fixed_point_of_gt_1 x2num hx2num_gt_one,
    rwa (rat.cast_coe_int x2num) at hh,
  },

  calc f x = f x * 1                           : (mul_one (f x)).symm
       ... = f x * (x2denom / x2denom)         : by rw ←(div_self hx2cnezr)
       ... = (f x * x2denom) / x2denom         : mul_div_assoc' (f x) _ _
       ... = (x2denom * f x) / x2denom         : by rw mul_comm
       ... = f x2num / x2denom                 : by rw h_denom_times_fx
       ... = x2num / x2denom                   : by rw h_fx2num_fixed
       ... = ((((x2num:ℚ) / (x2denom:ℚ)):ℚ):ℝ) : by norm_cast
       ... = x                                 : by rw ←hrat_expand2
end
