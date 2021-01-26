import data.pnat.basic
import data.nat.parity
import algebra.big_operators.pi
import tactic.ring
import tactic.field_simp
import tactic.linarith
import tactic.omega

open_locale big_operators

/-!
# IMO 2013 Q1

Prove that for any pair of positive integers k and n, there exist k positive integers
m₁, m₂, ..., mₖ (not necessarily different) such that

  1 + (2ᵏ - 1)/ n = (1 + 1/m₁) * (1 + 1/m₂) * ... * (1 + 1/mₖ).

# Solution

Direct translation of solution found in https://www.imo-official.org/problems/IMO2013SL.pdf

We prove a slightly more general version where k does not need to be strictly positive.

-/

lemma zero_lt_2n_minus_one {n: ℕ} (h: 0 < n) : 0 < 2 * n - 1 :=
begin
  omega
end

lemma zero_lt_2n_minus_one_rat {n: ℕ} (h: 0 < n) : (0:ℚ) < 2 * n - 1 :=
begin
   norm_num,
   norm_cast,
   omega
end

lemma zero_lt_2n_minus_one_cast {n: ℕ} (h: 0 < n) : (((2 * n - 1):ℕ):ℚ) = 2 * (n:ℚ) - 1 :=
begin
  have : 1 ≤ 2 * n,
  { omega },
  have h' : (((2 * n - 1):ℕ):ℚ) = _  := nat.cast_sub this,
  rw h',
  norm_num,
end

lemma pow_two_le (n : ℕ) : 2 ≤ 2^n.succ :=
begin
calc (2:ℕ) = (2:ℕ) * 1 : (mul_one _).symm
               ... ≤ 2 * 2^n : mul_le_mul_left' (nat.one_le_pow' n 1) 2
               ... = 2 ^ n.succ : (pow_succ 2 n).symm
end

lemma arith_lemma_nat (pk n: ℕ) (hn: 0 < n) : 0 < 2 * n + 2^pk.succ - 2 :=
begin
  have := pow_two_le pk,
  omega
end


lemma arith_lemma (pk n: ℕ) (hn: 0 < n) : (2 * (n:ℚ) + 2^pk.succ - 2) ≠ 0 :=
begin
  suffices : 0 < (2 * (n:ℚ) + 2^pk.succ - 2), from (ne_of_lt this).symm,
  rw add_sub_assoc,
  have hp : 2 ≤ 2^pk.succ := pow_two_le pk,
  have : (2:ℚ) ≤ 2^pk.succ,
  { norm_cast,
    exact hp
  },

  have : 1 ≤ n := by omega,
  have hh: (1:ℚ) ≤ (n:ℚ) := nat.one_le_cast.mpr this,
  have hh' := arith_lemma_nat pk n hn,
  linarith
end

lemma nat_lemma_2 (pk n: ℕ) (hn: 0 < n) : 2 ≤ 2 * n + 2^pk.succ :=
begin
  have := pow_two_le pk,
  omega
end

theorem pnat_even_or_odd (n : ℕ+) : (∃t: ℕ+, n.val = 2 * t.val - 1) ∨ (∃t: ℕ+, n.val = 2 * t.val) :=
begin
  obtain heven | hodd  := nat.even_or_odd n.val,
  { right,
    obtain ⟨t', ht'⟩ := heven,
    have htp': 0 < t',
    { have := n.property,
      omega, },
    use ⟨t', htp'⟩,
    rw ht',
  },
  { left,
    obtain ⟨t', ht'⟩ := hodd,
    use ⟨t' + 1, nat.succ_pos t'⟩,
    rw ht',
    simp,
    omega }
end

theorem imo2013_q1 (n : ℕ+) (k : ℕ)
  : (∃m: ℕ → ℕ+, (1:ℚ) + ((2^k - 1): ℚ) / n =
         (∏ i in finset.range k, (1 + 1 / ((m i) : ℚ)))) :=
begin
  revert n,
  induction k with pk hpk,
  { intro n,
    use λ _, 1,
    simp only [finset.card_empty, add_zero, finset.prod_const, zero_div, finset.range_zero, pow_zero, sub_self] },
  intro n,

  have ht := pnat_even_or_odd n,
  cases ht,
  { obtain ⟨t, ht⟩ := ht,
    obtain ⟨pm, hpm⟩  := hpk t,
    let m := λi, if h : i < pk then pm i else ⟨2 * t.val - 1, zero_lt_2n_minus_one t.property⟩,
    have h_mi_eq_pmi : ∀ i : ℕ, i < pk → m i = pm i,
    { intros i hi,
      exact dif_pos hi },

    have h_mi_eq_pmi' : ∀ i : ℕ, i ∈ finset.range pk → (1:ℚ) + 1 / m i = 1 + 1 / pm i,
    { intros i hi,
      rw (h_mi_eq_pmi i (finset.mem_range.mp hi)),
    },

    use m,
    have h' : ∏ (i : ℕ) in finset.range pk, ((1:ℚ) + 1 / ↑(m i)) =
                ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(pm i)),
    {
      exact finset.prod_congr rfl h_mi_eq_pmi',
    },

    have hmpk' : (m pk) = ⟨2 * t.val - 1, _⟩ := dif_neg (irrefl pk),

    have hmpk : ((m pk):ℚ) = 2 * t.val - 1,
    { rw hmpk', simp },

    have hneq0 : ((2 * t.val - 1):ℚ) ≠ (0:ℚ) := ne_of_gt (zero_lt_2n_minus_one_rat t.property),

    have htneq0 : (2 * t.val:ℚ) ≠ (0:ℚ):= by norm_num,
    have h3: (n.val:ℚ) = 2 * (t.val:ℚ) - 1,
    {
      rw ht,
      rw (zero_lt_2n_minus_one_cast t.property),
    },

    calc (1:ℚ) + (2 ^ pk.succ - 1) / ↑n
        = (1:ℚ) + (2 ^ pk.succ - 1) / ↑(n.val) : by norm_cast
    ... =  (1:ℚ) + (2^pk.succ - 1) / (2 * t.val - 1) : by rw h3
    ... = (2 * t.val - 1) / (2 * t.val - 1) + (2^pk.succ - 1) / (2 * t.val - 1)
             : by { norm_num, exact (div_self hneq0).symm}
    ... = ((2 * t.val - 1) + (2^pk.succ - 1)) / (2 * t.val - 1) : div_add_div_same _ _ _
    ... = (2 * t.val - 2 + 2^pk.succ) / (2 * t.val - 1) : by ring
    ... = (2 * t.val - 2 + 2 * 2^pk) / (2 * t.val - 1) : by rw pow_succ
    ... = ((1:ℚ) + (2^pk - 1) / t.val) * (1 + 1 / (2 * t.val - 1)) : by { field_simp, ring }
    ... = (1 + (2^pk - 1) / (t:ℚ)) * (1 + 1 / (2 * t.val - 1)) : by norm_cast
    ... = (1 + 1 / (2 * t.val - 1)) * (1 + (2^pk - 1) / (t:ℚ)) : mul_comm _ _
    ... = (1 + 1 / (2 * t.val - 1)) * ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(pm i)) : by rw hpm
    ... = (1 + 1 / (2 * t.val - 1)) * ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(m i)) : by rw h'
    ... = (1 + 1 / ↑(m pk)) * ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(m i)) : by rw ← hmpk
    ... = ∏ (i : ℕ) in finset.range pk.succ, (1 + 1 / ↑(m i)) : (finset.prod_range_succ (λ (x : ℕ), (1:ℚ) + 1 / ↑(m x)) pk).symm
  },
  obtain ⟨t, ht⟩ := ht,
  obtain ⟨pm, hpm⟩  := hpk t,

  have h1: 0 < 2 * t.val + 2^pk.succ - 2 := arith_lemma_nat pk t.val t.property,

  let m := λi, if h : i < pk then pm i else ⟨2 * t.val + 2^pk.succ - 2, h1⟩,
  use m,

  have h_mi_eq_pmi : ∀ i : ℕ, i < pk → m i = pm i,
  { intros i hi,
    exact dif_pos hi },

  have h_mi_eq_pmi' : ∀ i : ℕ, i ∈ finset.range pk → (1:ℚ) + 1 / m i = 1 + 1 / pm i,
  { intros i hi,
    rw (h_mi_eq_pmi i (finset.mem_range.mp hi)),
  },
  have h' : ∏ (i : ℕ) in finset.range pk, ((1:ℚ) + 1 / ↑(m i)) =
                 ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(pm i)),
  {
    exact finset.prod_congr rfl h_mi_eq_pmi',
  },

  have hmpk' : (m pk) = ⟨2 * t.val + 2^pk.succ - 2, _⟩ := dif_neg (irrefl pk),

  have hmpk : ((m pk):ℚ) = 2 * t.val + 2^pk.succ - 2,
  { rw hmpk',
    norm_cast,
    simp,
    have : (2:ℕ) ≤ 2 * ↑t + 2 ^ pk.succ := nat_lemma_2 pk t.val t.property,
    rw (nat.cast_sub this),
    ring,
    simp,
  },

  have h'' : (2 * (t.val:ℚ) + 2^pk.succ - 2) ≠ 0 := arith_lemma pk t.val t.property,

  have h2: 2 * t.val + 2^pk.succ - 2 ≠ 0 := ne_of_gt h1,

  calc (1:ℚ) + (2 ^ pk.succ - 1) / ↑n
      = (1:ℚ) + (2 ^ pk.succ - 1) / ↑(n.val) : by norm_cast
  ... = (1:ℚ) + (2 ^ pk.succ - 1) / ↑(2*t.val) : by rw ht
  ... = (1 + 1 / (2 * t.val + 2^pk.succ - 2)) * (1 + (2 ^ pk.succ - 2) / (2 * ↑(t.val)))
             : by { field_simp, ring }
  ... = (1 + 1 / (2 * t.val + 2^pk.succ - 2)) * (1 + (2 * 2 ^ pk - 2) / (2 * ↑(t.val)))
             : by rw pow_succ
  ... = (1 + 1 / (2 * t.val + 2^pk.succ - 2)) * (1 + (2 ^ pk - 1) / (↑(t.val)))
             : by { field_simp, ring }
  ... = (1 + 1 / (2 * t.val + 2^pk.succ - 2)) * (1 + (2 ^ pk - 1) / (↑t))
             : by norm_cast
  ... = (1 + 1 / (2 * t.val + 2^pk.succ - 2)) * ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(pm i))
             : by rw hpm
  ... = (1 + 1 / (2 * t.val + 2^pk.succ - 2)) * ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(m i))
             : by rw h'
  ... = (1 + 1 / ↑(m pk)) * ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(m i)) : by rw ← hmpk

  ... = ∏ (i : ℕ) in finset.range pk.succ, (1 + 1 / ↑(m i)) : (finset.prod_range_succ (λ (x : ℕ), (1:ℚ) + 1 / ↑(m x)) pk).symm

end

