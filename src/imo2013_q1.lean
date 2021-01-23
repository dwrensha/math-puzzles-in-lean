import data.pnat.basic
import algebra.big_operators.pi
import tactic.ring
import tactic.field_simp

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

theorem imo2013_q1 (n : ℕ+) (k : ℕ)
  : (∃m: ℕ → ℕ+, (1:ℚ) + ((2^k - 1): ℚ) / n =
         (∏ i in finset.range k, (1 + 1 / ((m i) : ℚ)))) :=
begin
  cases k,
  { use λ _, 1,
    simp only [finset.card_empty, add_zero, finset.prod_const, zero_div, finset.range_zero, pow_zero, sub_self] },

  revert n,
  induction k with pk hpk,
  { intro n, use λ _, n, norm_num },
  intro n,

  have ht: (∃t: ℕ+, pk.succ.succ = 2 * t.1 - 1) ∨ (∃t: ℕ+, pk.succ.succ = 2 * t.1),
  { sorry },

  cases ht,
  { obtain ⟨t, ht⟩ := ht,
    obtain ⟨pm, hpm⟩  := hpk t,
    let m := λi, if h : i < pk.succ then pm i else ⟨2 * t.val - 1, sorry⟩,
    have h_mi_eq_pmi : ∀ i : ℕ, i < pk.succ → m i = pm i,
    { intros i hi,
      exact dif_pos hi },

    have h_mi_eq_pmi' : ∀ i : ℕ, i ∈ finset.range pk.succ → (1:ℚ) + 1 / m i = 1 + 1 / pm i,
    { intros i hi,
      rw (h_mi_eq_pmi i (finset.mem_range.mp hi)),
    },

    use m,
    have : ∏ (i : ℕ) in finset.range pk.succ.succ, ((1:ℚ) + 1 / ↑(m i)) =
                (1 + 1 / ↑(m pk.succ)) * ∏ (i : ℕ) in finset.range pk.succ, (1 + 1 / ↑(m i)),
    { exact finset.prod_range_succ (λ (x : ℕ), 1 + 1 / ↑(m x)) (nat.succ pk) },


    have h' :  ∏ (i : ℕ) in finset.range pk.succ, ((1:ℚ) + 1 / ↑(m i)) =
                 ∏ (i : ℕ) in finset.range pk.succ, (1 + 1 / ↑(pm i)),
    {
      exact finset.prod_congr rfl h_mi_eq_pmi',
    },
    have h'' : (1:ℚ) + (2^pk.succ.succ - 1) / (2 * t - 1) = ((1:ℚ) + (2^pk.succ - 1) / t) * (1 + 1 / (2 * t - 1)),
    {
      sorry
    },

    have hneq0 : ((2 * t.val - 1):ℚ) ≠ (0:ℚ),
    { have : 0 < t.val := t.property,
      sorry
    },

    have htneq0 : (2 * t.val:ℚ) ≠ (0:ℚ):= by norm_num,

    have h''' := calc (1:ℚ) + (2^pk.succ.succ - 1) / (2 * t.val - 1)
        = (2 * t.val - 1) / (2 * t.val - 1) + (2^pk.succ.succ - 1) / (2 * t.val - 1)
             : by { norm_num, exact (div_self hneq0).symm}
    ... = ((2 * t.val - 1) + (2^pk.succ.succ - 1)) / (2 * t.val - 1) : div_add_div_same _ _ _
    ... = (2 * t.val - 2 + 2^pk.succ.succ) / (2 * t.val - 1) : by ring
    ... = (2 * t.val - 2 + 2 * 2^pk.succ) / (2 * t.val - 1) : by rw pow_succ
    ... = 2 * (t.val - 1 +  2^pk.succ) / (2 * t.val - 1) : by ring
    ... = 1 * (2 * (t.val - 1 +  2^pk.succ) / (2 * t.val - 1)) : (one_mul _).symm
    ... = ((2 * t.val) / (2 * t.val)) * (2 * (t.val - 1 +  2^pk.succ) / (2 * t.val - 1)) : by rw (div_self htneq0)
    ... = ((2 * (t.val - 1 +  2^pk.succ)) / (2 * t.val)) * ((2 * t.val) / (2 * t.val - 1)) : by ring
    ... = ((2 * (t.val - 1 +  2^pk.succ)) / (2 * t.val)) * (1 + 1 / (2 * t.val - 1)) : by field_simp
    ... = ((t.val - 1 +  2^pk.succ) / t.val) * (1 + 1 / (2 * t.val - 1)) : sorry,

    sorry,
  },
  obtain ⟨t, ht⟩ := ht,
  sorry,

end
