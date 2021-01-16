import data.rat.basic
import data.rat.order
import data.real.basic

open_locale big_operators

lemma sum_range_le {n:ℕ} {f g: ℕ → ℝ} (h: ∀i:ℕ, i < n → f i ≤ g i )
      : (∑ (i : ℕ) in finset.range n, f i)
            ≤ (∑ (i : ℕ) in finset.range n, g i) :=
begin
  induction n with pn hpn,
  { simp only [finset.sum_empty, finset.range_zero],
  },
  rw (finset.sum_range_succ _ pn),
  rw (finset.sum_range_succ _ pn),
  have hfg := h pn (lt_add_one _),
  have hr: (∀i, i < pn → f i ≤ g i),
  {
    intros i hi,
    exact h i (nat.lt.step hi)
  },
  have hpn' := hpn hr,
  linarith,
end

lemma integer_subtraction_lemma1 {n m: ℤ} : (n - (m + 1) + 1) = n - m :=
begin
  ring
end

lemma simp_lemma_1 {x y: ℝ} {n:ℕ} : y * (x^0 * y^(n.succ - 1 - 0)) = y ^ (n+1) :=
begin
  simp only [one_mul, nat.succ_sub_succ_eq_sub, nat.sub_zero, pow_zero],
  exact (pow_succ y n).symm,
end

lemma factor_xn_m_yn
      (x : ℝ)
      (y:ℝ)
      (n: ℕ)
      :  x^n - y^n = (x - y) * (∑ (i:ℕ) in finset.range n, (x ^(i) * y ^(n - 1 -i))) :=
begin
  cases n,
  { simp only [finset.sum_empty, finset.range_zero, mul_zero, pow_zero, sub_self], },

  have hinner0: (∀i:ℕ, i ∈ finset.range n.succ → x * (x^i * y ^(n.succ - 1 -i))
                                                = x^(i+1) * y ^(n.succ - 1 -i)),
  {
    intros i _,
    calc x * (x^i * y ^(n.succ - 1 -i)) = (x * x^i) * y ^(n.succ - 1 -i) : (mul_assoc x _ _).symm
        ... = x^(i+1) * y ^(n.succ - 1 -i) : by rw ←(pow_succ x i),
  },

  have hxterm := calc x * (∑i in finset.range n.succ, (x ^i * y ^(n.succ - 1 - i))) =
    (∑i in finset.range n.succ, (x * (x ^i * y ^(n.succ - 1 -i))))
                : ((finset.range n.succ).sum_hom (has_mul.mul x)).symm
   ... = (∑i in finset.range n.succ, (x^(i+1) * y ^(n.succ - 1 - i))) : finset.sum_congr rfl hinner0
   ... = (x^(n+1) * y ^(n.succ - 1 - n))
         + (∑i in finset.range n, (x^(i+1) * y ^(n.succ - 1 - i))) : finset.sum_range_succ _ _
   ... = (x^(n+1) * y ^(n - n))
         + (∑i in finset.range n, (x^(i+1) * y ^(n - i))) : by rw [nat.succ_sub_one n]
   ... = x^(n+1)
         + (∑i in finset.range n, (x^(i+1) * y ^(n - i))) : by simp only [mul_one, nat.sub_self, pow_zero],

  have hinner2: (∀i:ℕ, i ∈ finset.range n →
       y * (x ^(i+1) * y^(n.succ - 1 -(i+1))) = x^(i + 1) * y^(n - i)),
  begin
    intros i hi,
    have hii : (i+1) ≤ n,
    {
      exact nat.succ_le_iff.mpr (finset.mem_range.mp hi)
    },

    calc y * (x ^(i+1) * y ^(n.succ - 1 -(i+1)))
        = (y * x ^(i+1)) * y ^(n.succ - 1 -(i+1)) : tactic.ring.mul_assoc_rev y _ _
    ... = (x ^(i+1) * y) * y ^(n.succ - 1 -(i+1)) : by rw mul_comm y _
    ... = x ^(i+1) * (y * y ^(n.succ - 1 -(i+1))) : mul_assoc _ y _
    ... = x ^(i+1) * y ^((n.succ - 1 -(i+1)) + 1) : by rw ←(pow_succ y (n.succ - 1 -(i+1)))
    ... = x ^(i+1) * y ^((n -(i+1)) + 1) : by simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero]
    ... = x ^(i+1) * y ^((((n -(i+1)) + 1):ℕ):ℤ) : by rw (fpow_coe_nat y _)
    ... = x ^(i+1) * y ^((((n -(i+1)):ℕ):ℤ) + (1:ℤ)) : by rw int.coe_nat_succ
    ... = x ^(i+1) * y ^(((n:ℤ) - (((i+1):ℕ):ℤ)) + (1:ℤ)) : by rw int.coe_nat_sub hii
    ... = x ^(i+1) * y ^(((n:ℤ) - ((i:ℤ)+(1:ℤ))) + (1:ℤ)) : by rw int.coe_nat_succ
    ... = x ^(i+1) * y ^((n:ℤ) - (i:ℤ)) : by rw integer_subtraction_lemma1
    ... = x ^(i+1) * y ^(((n - i):ℕ):ℤ) : by rw ←(int.coe_nat_sub (nat.le_of_succ_le hii))
    ... = x^(i + 1) * y^(n - i) : by rw ←(fpow_coe_nat y _)
  end,

  have hyterm := calc
      y * (∑i in finset.range n.succ, (x ^(i) * y ^(n.succ - 1 -i)))
       = ∑i in finset.range n.succ, y * (x ^(i) * y ^(n.succ - 1 -i))
            : ((finset.range (nat.succ n)).sum_hom (has_mul.mul y)).symm
    ... = (∑i in finset.range n, y * (x ^(i+1) * y ^(n.succ - 1 -(i+1)))) + y * (x^0 * y^(n.succ - 1 - 0))
        : finset.sum_range_succ' _ n
    ... = (∑i in finset.range n, y * (x ^(i+1) * y ^(n.succ - 1 -(i+1)))) + y^(n + 1)
        : by rw simp_lemma_1
    ... = (∑i in finset.range n, x^(i + 1) * y^(n - i)) + y^(n + 1)
        : by rw (finset.sum_congr rfl hinner2),

  symmetry,

  calc (x - y) * (∑i in finset.range n.succ, (x ^(i) * y ^(n.succ - 1 -i)))
      = x * (∑i in finset.range n.succ, (x ^(i) * y ^(n.succ - 1 -i))) -
        y * (∑i in finset.range n.succ, (x ^(i) * y ^(n.succ - 1 -i)))
         : sub_mul x y (∑ i in finset.range n.succ, x ^ i * y ^ (n.succ - 1 - i))
  ... = x^(n+1) + (∑i in finset.range n, (x^(i+1) * y ^(n - i))) -
        ((∑i in finset.range n, x^(i + 1) * y^(n - i)) + y^(n + 1))
      : by rw [hxterm, hyterm]
  ... = x^(n+1) - y^(n + 1) : by ring
end

lemma nth_power_gt
      (x:ℝ)
      (y:ℝ)
      (hx : 1 < x)
      (hy : 1 < y)
      (h: ∀n:ℕ, 0 < n → x^n - 1 < y^n)
      : (x ≤ y) :=
begin
   by_contra hxy,
   push_neg at hxy,
   have hxmy : 0 < x - y := sub_pos.mpr hxy,

   have hn: (∀ n:ℕ, 0 < n →  (x - y) * (n:ℝ) ≤ x^n - y^n),
   {
     intros n hn,
     have hterm : (∀i:ℕ, i < n → 1 ≤ x^i * y^(n - 1 - i)),
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
               : (mul_le_mul_left hxmy).mpr (sum_range_le hterm)
         ... = x^n - y^n : (factor_xn_m_yn x y n).symm,
   },

   -- choose n larger than 1 / (x - y)
   have hxyrp: 0 < 1/(x - y) := one_div_pos.mpr hxmy,
   obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - y)),
   have hNpr : (0:ℝ) < N := lt_trans hxyrp hN,
   have hNp : 0 < N,
   {
     -- there's gotta be a simpler way to do this...
     rw ←nat.cast_zero at hNpr,
     cases N,
     { linarith, },
     exact nat.succ_pos N
   },

   have hh := h N hNp,
   have := calc 1 = (x - y) * (1 / (x - y)) : by field_simp [ne_of_gt hxmy]
              ... < (x - y) * N : (mul_lt_mul_left hxmy).mpr hN
              ... ≤ x^N - y^N : hn N hNp,
   linarith,
end

lemma nth_power_gt'
      (x:ℝ)
      (y:ℝ)
      (hx : 1 < x)
      (hy : 0 < y)
      (h: ∀n:ℕ, 0 < n → x^n - 1 < y^n)
      : (x ≤ y) :=
begin
  have hy': 1 < y,
  {
    by_contra hy'',
    push_neg at hy'',
    -- hy'' :  y ≤ 1.

    let y' := (x + 1) / 2,
    have h_y'_lt_x: y' < x,
    {
      have hh: x + 1 < x * 2,
      {
        linarith
      },
      have hh': (x + 1)/2 < (x * 2) / 2,
      {
        linarith,
      },
      calc y' < (x * 2) / 2 : hh'
          ... = x : by linarith
    },
    have h1_lt_y' : 1 < y',
    {
      have hh': 1 * 2 / 2 < (x + 1) / 2,
      {
        linarith,
      },
      calc 1 = 1 * 2 / 2 : by linarith
         ... < y' : hh'
    },
    have h_y_lt_y' := calc y ≤ 1 : hy''
                         ... < y': h1_lt_y',
    have h_yn_lt_y'n : (∀n, 0<n → y^n < y'^n),
    {
      intros n hn,
      cases n,
      {linarith},
      induction n with pn hpn,
      {linarith},
      calc y ^ pn.succ.succ
              = y ^ pn.succ * y : pow_succ' y (nat.succ pn)
          ... < y ^ pn.succ * y' : (mul_lt_mul_left (pow_pos hy (nat.succ pn))).mpr h_y_lt_y'
          ... < y' ^ pn.succ * y' : (mul_lt_mul_right (lt_trans hy h_y_lt_y')).mpr (hpn (nat.succ_pos pn))
          ... = y' ^ pn.succ.succ : (pow_succ' y' (nat.succ pn)).symm
    },
    have hh: (∀ n, 0<n → x^n - 1 < y'^n),
    {
      intros n hn,
      calc x^n - 1 < y^n : h n hn
              ...  < y'^n : h_yn_lt_y'n n hn
    },
  -- then there exists y' such that 0 < y ≤ 1 < y' < x.
  -- and for all positive n , x^n - 1 < y^n < y'^n

    have := nth_power_gt x y' hx h1_lt_y' hh,
  -- so by nth_power_gt, x ≤ y'. contradiction.
    linarith,
  },
  exact nth_power_gt x y hx hy' h
end

lemma foo (a: ℤ) (ha: 0 < a) : 0 < a.nat_abs :=
begin
  cases a,
  {simp only [int.nat_abs_of_nat, int.nat_abs],
    have : (a:ℤ) = int.of_nat a,
    {
      exact int.coe_nat_eq a,
    },
    rw ← this at ha,
    exact int.coe_nat_pos.mp ha,
   },
  simp only [nat.succ_pos', int.nat_abs],
end

/-
Direct translation of solution found in https://www.imo-official.org/problems/IMO2013SL.pdf
-/

theorem imo2013Q5
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
    have haz := calc 0 < 1     : zero_lt_one
                   ... < (a:ℝ) : ha1r,

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
  have hfn': ∀x: ℚ, (0 < x → ∀ n: ℕ, 0 < n → ↑n * f x ≤ f (n * x)),
  {
    intros x hx n hn,
    cases n,
    { linarith }, -- hn: 0 < 0
    have := hfn x hx n,
    rwa [nat.cast_succ n],
  },
  have hn: (∀ n : ℕ, 0 < n → (n: ℝ) ≤ f n),
  {
    intros n hn,
    calc (n: ℝ) = (n: ℝ) * 1 : by simp only [mul_one]
                  ... ≤ (n: ℝ) * f 1 : (mul_le_mul_left (nat.cast_pos.mpr hn)).mpr hf1
                  ... ≤ f (n * 1) : hfn' 1 zero_lt_one n hn
                  ... = f n : by simp only [mul_one]
  },
  have hqp: ∀ q: ℚ, 0 < q → 0 < f q,
  {
    intros q hq,
    have hqn : (q.num: ℚ) = q * (q.denom : ℚ) := rat.mul_denom_eq_num.symm,
    have hfqn : f q.num ≤ f q * f q.denom,
    {
      have := f_i q q.denom hq (nat.cast_pos.mpr q.pos),
      rwa hqn,
    },
    have hqd: (q.denom: ℝ) ≤ f q.denom := hn q.denom q.pos,
    have hqnp: 0 < q.num := rat.num_pos_iff_pos.mpr hq,
    have hqna: ((int.nat_abs q.num):ℤ) = q.num := int.nat_abs_of_nonneg (le_of_lt hqnp),
    have hqfn': (q.num: ℝ) ≤ f q.num,
    {
      rw ←hqna at hqnp,
      have := hn q.num.nat_abs (int.coe_nat_pos.mp hqnp),
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

       have := int.nat_abs_of_nonneg (floor_nonneg.mpr hzx),
       conv begin
         to_rhs, rw ← this,
       end,
     },
     have hfe' : ((⌊x⌋).nat_abs : ℚ) = ⌊x⌋,
     {
       conv begin to_rhs, rw ← hfe end,
       simp only [int.cast_coe_nat],
     },
     have hnnna : 0 < (⌊x⌋).nat_abs,
     {
       suffices: 0 < ⌊x⌋,
       { exact foo ⌊x⌋ this, },
       have := calc 0 ≤ x - 1 : by linarith
            ... < ⌊x⌋ : sub_one_lt_floor x,
       exact int.cast_pos.mp this,
     },
     have hx0 := calc (((x - 1):ℚ):ℝ) < ⌊x⌋ : begin have h := sub_one_lt_floor x,
                                                    have h' : ((⌊x⌋ : ℚ):ℝ) = (⌊x⌋ : ℝ) := rat.cast_coe_int ⌊x⌋,
                                                    rw ← h',
                                                    exact rat.cast_lt.mpr h,
                                              end
                              ... ≤ f ⌊x⌋ : begin have := hn (⌊x⌋).nat_abs hnnna,
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

     calc (((x - 1):ℚ):ℝ) <  f ⌊x⌋ : hx0
                  ... < f (x - ⌊x⌋) + f ⌊x⌋ : lt_add_of_pos_left (f ↑⌊x⌋) (hqp (x - ↑⌊x⌋) hxmfx)
                  ... ≤ f ((x - ⌊x⌋) + ⌊x⌋) : f_ii (x - ⌊x⌋) ⌊x⌋ hxmfx h0fx
                  ... = f x : by simp only [sub_add_cancel]
  },
  have hfxn : (∀n:ℕ, 0 < n → ∀ x:ℚ, 1 < x → f (x^n) ≤ (f x)^n),
  {
    intros n hn x hx,
    induction n with pn hpn,
    {
      linarith,
    },
    cases pn,
    {
      simp only [pow_one],
    },
    have hpn' := hpn (nat.succ_pos pn),
    rw [pow_succ' x (nat.succ pn), pow_succ' (f x) (nat.succ pn)],
    have hxp := calc 0 < 1 : zero_lt_one
                 ... < x : hx,
    have hfnp: 0 < f x := hqp x hxp,
    calc f ((x ^ pn.succ) * x)
         ≤ f (x ^ pn.succ) * f x : f_i (x ^ pn.succ) x (pow_pos hxp pn.succ) hxp
     ... ≤ (f x) ^ pn.succ * f x : (mul_le_mul_right hfnp).mpr hpn'
  },
  have : (∀x:ℚ, 1 < x → (x:ℝ) ≤ f x),
  {
    intros x hx,
    have hxg1: 1 ≤ x := le_of_lt hx,
    have hxnm1: (∀ n : ℕ, 0 < n → (x:ℝ)^n - 1 < (f x)^n),
    {
      intros n hn,
      calc (x:ℝ)^n - 1
           = (((x^n - 1):ℚ):ℝ) : by norm_cast
       ... < f (x^n) : hfx_gt_xm1 (x^n) (one_le_pow_of_one_le hxg1 n)
       ... ≤ (f x)^n : hfxn n hn x hx
    },
    have hx': 1 < (x:ℝ),
    {
      norm_cast,
      exact hx
    },
    have hxp: 0 < x,
    {
      calc 0 < 1 : zero_lt_one
         ... < x : hx
    },

    exact nth_power_gt' x (f x) hx' (hqp x hxp) hxnm1,
  },
  sorry,
end

