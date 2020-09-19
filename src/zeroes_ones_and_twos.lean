import data.int.modeq
import data.nat.basic
import data.nat.modeq
import data.pnat.basic
import data.nat.digits
import data.nat.gcd

lemma mul_left_coprime_aux
  (base factor c d : ℕ)
  (hord : c ≤ d)
  (h_coprime : nat.coprime factor base)
  (h_equal : base * c ≡ base * d [MOD factor])
  : c ≡ d [MOD factor] :=
begin
  have hm : (base * c) ≤ (base * d) := nat.mul_le_mul_left base hord,
  have hd: (factor ∣ (base * d) - (base * c)) := (nat.modeq.modeq_iff_dvd' hm).mp h_equal,
  rw [←nat.mul_sub_left_distrib base d c] at hd,
  apply (nat.modeq.modeq_iff_dvd' hord).mpr,
  exact nat.coprime.dvd_of_dvd_mul_left h_coprime hd,
end

lemma mul_left_coprime
  (base factor c d : ℕ)
  (h_coprime : nat.coprime factor base)
  (h_equal : base * c ≡ base * d [MOD factor])
  : c ≡ d [MOD factor] :=
begin
  have hord: c ≤ d ∨ d ≤ c := nat.le_total,
  cases hord with hcd hdc,
  {
    exact mul_left_coprime_aux base factor c d hcd h_coprime h_equal,
  },
  {
   exact (mul_left_coprime_aux base factor d c hdc h_coprime h_equal.symm).symm,
  }
end

lemma coprime_power
  (base factor : ℕ)
  (k : ℕ)
  (h_coprime : nat.coprime factor base)
  : nat.coprime factor (base^k) :=
begin
  exact nat.coprime.pow_right k h_coprime
end

lemma pigeonhole (n : ℕ) (f : ℕ → fin n) :
  ∃ a b : ℕ, a ≠ b ∧ f a = f b :=
begin
  classical,
  by_contra hc,
  push_neg at hc,
  have hinj : function.injective f,
  { intros a b,
    contrapose,
    exact hc a b, },
  apply not_injective_infinite_fintype f hinj,
end

def iterate_pow (base factor : ℕ) (hfactor: factor > 0) : ℕ → fin factor :=
λn, ⟨(base ^ n) % factor, nat.mod_lt (base ^ n) hfactor ⟩

lemma exists_distinct_exponents
  (base factor : ℕ)
  (hf: 0 < factor)
  : ∃ m n : ℕ, (m ≠ n ∧ base^m ≡ base^n [MOD factor]) :=
begin
  let f := iterate_pow base factor hf,
  have he : ∃ a b : ℕ, a ≠ b ∧ f a = f b := pigeonhole factor f,
  obtain ⟨a, b, hab⟩ := he,
  cases hab,
  use a,
  use b,
  use hab_left,
  have : base ^ a % factor = base ^ b % factor,
  {
     have hval :(f a).val = (f b).val := congr_arg subtype.val hab_right,

     have havala: (f a).val = (base ^ a) % factor := rfl,
     rw ← havala,

     have havalb: (f b).val = (base ^ b) % factor := rfl,
     rw ← havalb,

     assumption,
  },
  unfold nat.modeq,
  assumption,
end

lemma exists_distinct_exponents_ordered
  (base factor : ℕ)
  (hf: 0 < factor)
  : ∃ m n : ℕ, (m < n ∧ base^m ≡ base^n [MOD factor]) :=
begin
  obtain ⟨a, b, haneb, hab⟩ := exists_distinct_exponents base factor hf,
  have ht := nat.lt_trichotomy a b,
  cases ht,
  {
    use a,
    use b,
    finish,
  },
  cases ht,
  {
    finish,
  },
  use b,
  use a,
  use ht,
  exact hab.symm,
end

lemma periodic
  (base factor : ℕ)
  (hf: 0 < factor)
  (h_coprime: nat.coprime base factor)
  : ∃k : ℕ+, (base^k.val) ≡ 1 [MOD factor] :=
begin
  obtain ⟨a, b, haneb, hab⟩ := exists_distinct_exponents_ordered base factor hf,
  have hst :(∃ k : ℕ, a + 1 + k = b) := nat.le.dest haneb,
  obtain ⟨k, hk⟩ := hst,
  use k + 1,
  { linarith },
  dsimp,
  rw ← hk at hab,
  clear haneb hk b,
  have hp: base ^ (a + 1 + k) = (base ^ a) * (base ^ (1 + k)),
  begin
      calc base ^ (a + 1 + k)
          = base ^ (a + (1 + k)) : by rw [add_assoc a 1 k]
      ... = base ^ a * base ^ (1 + k) : nat.pow_add base _ _,
  end,
  rw hp at hab,
  clear hp,
  have hp_coprime : nat.coprime (base^a) factor := nat.coprime.pow_left _ h_coprime,
  conv at hab begin
    congr,
    skip,
    rw ← (mul_one (base ^ a)),
    skip,
  end,
  have := (mul_left_coprime (base ^ a) factor 1 (base ^ (1 + k)) hp_coprime.symm hab).symm,
  rwa ←(add_comm 1 k),
end

@[simp]
def all_zero_or_one : list ℕ → Prop
| [] := true
| (0 :: ds) := all_zero_or_one ds
| (1 :: ds) := all_zero_or_one ds
| _ := false


lemma digits_lemma
  (base: ℕ)
  (h2: 2 ≤ base)
  (n: ℕ)
  (hn: 0 < n)
  : (digits base (base * n)) = 0 :: (digits base n) :=
begin
  have := digits_add base h2 0 n (nat.lt_of_succ_lt (nat.succ_le_iff.mp h2)) (or.inr hn),
  rwa (zero_add (base * n)) at this,
end

lemma times_base_still_all_zero_or_one
  (base: ℕ)
  (h2: 2 ≤ base)
  (n: ℕ)
  (hazoo : all_zero_or_one (digits base n))
  : all_zero_or_one (digits base (base * n)) :=
begin
  cases (nat.eq_zero_or_pos n) with hz hp,
  {
    rw hz,
    simp only [mul_zero, digits_zero]
  },

  rw (digits_lemma base h2 n hp),
  simpa,
end

lemma base_pow_still_all_zero_or_one
  (base: ℕ)
  (h2: 2 ≤ base)
  (k n: ℕ)
  (hazoo : all_zero_or_one (digits base n))
  : all_zero_or_one (digits base ((base ^ k) * n)) :=
begin
  induction k with pk hpk,
  { simpa },
  have := times_base_still_all_zero_or_one base h2 _ hpk,
  rwa [←(nat.add_one pk), nat.pow_succ base pk, mul_comm (base^pk) base, mul_assoc],
end

lemma times_base_plus_one_still_all_zero_or_one
  (base: ℕ)
  (h2: 2 ≤ base)
  (n: ℕ)
  (hazoo : all_zero_or_one (digits base n))
  : all_zero_or_one (digits base (1 + base * n)) :=
begin
  rw (digits_add base h2 1 n (nat.succ_le_iff.mp h2) (or.inl nat.one_pos)),
  simpa,
end

lemma base_pow_then_inc_still_all_zero_or_one
  (base: ℕ)
  (h2: 2 ≤ base)
  (k : ℕ)
  (n : ℕ)
  (hazoo : all_zero_or_one (digits base n))
  : all_zero_or_one (digits base ((base ^ (k + 1)) * n + 1)) :=
begin
  have hs := base_pow_still_all_zero_or_one base h2 k n hazoo,
  have hss := times_base_plus_one_still_all_zero_or_one base h2 _ hs,
  have hrw : 1 + base * (base ^ k * n) = base ^ (k + 1) * n + 1,
  {
    ring,
    have : base ^ k * base  = base ^ (k + 1) := (nat.pow_succ base k).symm,
    finish,
  },
  rwa ← hrw,
end

lemma nat_prev (n: ℕ) (hn: 0 < n) : (∃m:ℕ, n = m + 1) :=
begin
   cases n with j,
   {
      exfalso,
      exact nat.lt_asymm hn hn,
   },
   use j,
end

lemma exists_positive_mod
  (base factor : ℕ)
  (h2 : 2 ≤ base)
  (hf: 0 < factor)
  (h_coprime: nat.coprime base factor)
  (n: ℕ)
  : (∃k:ℕ, 0 < k ∧ k ≡ (n + 1) [MOD factor] ∧ all_zero_or_one (digits base k)) :=
begin
  induction n with np hnp,
  {
    use 1,
    use nat.modeq.refl 1,
    have hd := digits_add base h2 1 0 (nat.succ_le_iff.mp h2) (or.inl nat.one_pos),
    simp at hd,
    rw hd,
    simp
  },
  obtain ⟨kp, hkp⟩ := hnp,
  obtain ⟨kper, hkper⟩ := (periodic base factor hf h_coprime),
  have hper0: ∃ km: ℕ, kper.val = km + 1 := nat_prev kper.1 kper.2,
  obtain ⟨per0, hper01⟩ := hper0,
  use (base ^ (per0 + 1) * kp + 1),
  split,
  {
    exact (base ^ (per0 + 1) * kp).succ_pos,
  },
  split,
  {
    rw hper01 at hkper,
    refine nat.modeq.modeq_add _ rfl,
    have hme := nat.modeq.modeq_mul hkper hkp.2.1,
    simp only [one_mul] at hme,
    assumption,
  },
  have hr := base_pow_then_inc_still_all_zero_or_one base h2 per0 kp hkp.2.2,
  exact hr,
end

lemma nonzero_lemma (a b c : ℕ) (h: a = b * c) (ha: 0 < a) (hb: 0 < b) : 0 < c :=
begin
  have hc: c = 0 ∨ 0 < c := nat.eq_zero_or_pos c,
  cases hc,
  {
    rw hc at h,
    simp at h,
    finish,
  },
  assumption,
end

lemma zeroes_and_ones_coprime
  (base: ℕ)
  (h2: 2 ≤ base)
  (factor: ℕ)
  (hf: 0 < factor)
  (h_coprime: nat.coprime base factor)
  : ∃ k : ℕ+, all_zero_or_one (digits base (factor * k)) :=
begin
  obtain ⟨factor_prev, h_factor_prev⟩ := nat_prev factor hf,
  have hpm := exists_positive_mod base factor h2 hf h_coprime factor_prev,
  obtain ⟨n, hn⟩ := hpm,
  cases hn,
  cases hn_right,
  rw ← h_factor_prev at hn_right_left,
  have hff : factor ≡ (factor % factor) [MOD factor] := (nat.modeq.mod_modeq factor factor).symm,
  simp only [nat.mod_self] at hff,
  have hn0 : n ≡ 0 [MOD factor] := nat.modeq.trans hn_right_left hff,
  have hdvd : factor ∣ n := nat.modeq.modeq_zero_iff.mp hn0,
  obtain ⟨k, hk⟩ := exists_eq_mul_right_of_dvd hdvd,
  have hkp : 0 < k := nonzero_lemma n factor k hk hn_left hf,
  use ⟨ k, hkp ⟩,
  simp,
  rwa ← hk,
end

-- what if base and factor aren't coprime?
-- then there is r and s and t such that factor * r = t * base ^ s where t and base are coprime.

lemma unbounded_power
  (m n: ℕ)
  (hm: 2 ≤ m)
  : (∃k : ℕ, n < m ^ k) :=
begin
  induction n with np hnp,
  {
    use 0,
    simp,
  },
  obtain ⟨k, hk⟩ := hnp,
  use k + 1,

  obtain ⟨m0, hm0⟩ : (∃m0, 2 + m0 = m) := nat.le.dest hm,
  have hmm : m ^ k + 1 ≤ (m ^ k) * m :=
  begin
    conv begin
      congr,
      skip,
      congr,
      skip,
      rw ← hm0,
    end,
    clear hm0,
    have hol: 1 ≤ m^k := nat.one_le_of_lt hk,
    calc m ^ k + 1 ≤ m ^ k + m ^ k : add_le_add_left hol (m ^ k)
        ... ≤ m ^ k + m^k + m^k * m0 : nat.le.intro rfl
        ... = m ^ k * (2 + m0) : by ring
  end,

  calc np.succ = np + 1 : rfl
       ...     < m^k + 1 : nat.succ_lt_succ hk
       ...     ≤ m ^ k * m : hmm
       ...     = m ^ (k + 1) : (nat.pow_succ m k).symm,
end


def compute_largest_pow_factor (b: ℕ) (hb: 2 ≤ b) : ℕ → ℕ
| n :=
      if h0: n = 0 then 0 else
      if hd : b ∣ n
       then
         have n / b < n, from nat.div_lt_self (nat.pos_of_ne_zero h0) hb,
         1 + compute_largest_pow_factor (n / b)
       else 0

lemma largest_pow_factor
  (m n: ℕ)
  (hm: 2 ≤ m)
  : (∃k : ℕ, m ^ k ∣ (n + 2) ∧ (¬ m ^ (k + 1) ∣ (n + 2))) :=
begin
  revert n,
  suffices ht : ∀ (n n1 : ℕ), n1 ≤ n → ∃ (k : ℕ), m ^ k ∣ (n1 + 2) ∧ ¬m ^ (k + 1) ∣ (n1 + 2),
  {
    intro n,
    exact ht n n rfl.ge,
  },
  intro n,
  induction n with np hnp,
  {
    intros n1 hn1,
    have hn10 : n1 = 0 := le_zero_iff_eq.mp hn1,
    rw hn10,
    simp,
    -- depends on whether m = 2 or 2 < m...
    have hm2: 2 = m ∨ 2 < m := eq_or_lt_of_le hm,
    cases hm2,
    {
      rw ← hm2,
      use 1,
      simp,
      intro hb,
      have h112 : 1 + 1 = 2 := rfl,
      rw h112 at hb,
      have h222 : 2 < 2 ^ 2 := nat.lt_two_pow 2,
      have hdvd : (∃ k, 2 = 2 ^ 2 * k) := exists_eq_mul_right_of_dvd hb,
      obtain ⟨k, hk⟩ := hdvd,
      cases k,
      {
        finish
      },
      have h2222 : 2 ^ 2 ≤ 2 ^ 2 * k.succ,
      {
        calc 2 ^ 2 ≤ 2^2 * k +  2^2 : nat.le_add_left (2 ^ 2) (2 ^ 2 * k)
             ... = 2 ^ 2 * k.succ: by ring,
      },
      have h222 : 2 < 2 ^ 2 * k.succ,
      {
        calc 2 < 2 + 2 : nat.lt_of_sub_eq_succ rfl
            ... = 2 * 2 : (two_mul 2).symm
            ... = 2 ^ 2 : (nat.pow_two 2).symm
            ... ≤ 2 ^ 2 * k.succ : h2222
      },
      conv at h222 begin
        congr,
        rw hk,
        skip, skip
      end,
      exact nat.lt_asymm h222 h222
    },
    use 0,
    split,
    { simp only [nat.pow_zero, is_unit.dvd, nat.is_unit_iff] },
    simp only [nat.pow_one],
    intro h,
    obtain ⟨k, hk⟩ := exists_eq_mul_right_of_dvd h,
    cases k,
    {
      linarith,
    },
    rw hk at hm2,
    have hmm : m < m,
    {
      calc m ≤ m + m * k : nat.le.intro rfl
        ... = m * 1 + m * k : by conv begin to_lhs, congr, rw (mul_one m).symm, skip end
        ... = m * (1 + k) : (mul_add m 1 k).symm
        ... = m * (k.succ) : by rw ((nat.one_add k).symm)
        ... < m : hm2
    },
    exact nat.lt_asymm hmm hmm
  },
  intros n1 hn1,
  -- plug in something like ((n1 + 2) / m) - 2. ugh.
  -- 
  sorry,
end

lemma split_into_coprime
  (factor : ℕ)
  (hf: 0 < factor)
  : (∃ r s t : ℕ, 0 < r ∧ factor * r = t * 10 ^ s ∧ nat.coprime 10 t) :=
begin
  -- find largest power s2 of 2 that divides factor, pull it out, yielding m
  -- find largest power s5 of 5 that divides m, pull it out, yielding t.
  -- set r := 2^s5 * 5^s2.
  -- s:= s5 + s2
  sorry,
end

theorem part_one (n : ℕ) : ∃ k : ℕ+, all_zero_or_one (digits 10 (n * k)) :=
begin
  sorry
end
