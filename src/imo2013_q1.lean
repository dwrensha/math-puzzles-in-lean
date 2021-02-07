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

lemma two_le_pos_pow_two (n : ℕ) : 2 ≤ 2^n.succ :=
calc (2:ℕ) = 2^1 : (pow_one 2).symm
       ... ≤ 2^n.succ : nat.pow_le_pow_of_le_right zero_lt_two ((1:ℕ).le_add_left n)

lemma arith_lemma_nat (pk n: ℕ) : 0 < 2 * n + 2^pk.succ :=
begin
  have := two_le_pos_pow_two pk,
  omega
end


lemma arith_lemma (pk n: ℕ) : (2 * (n:ℚ) + 2^pk.succ) ≠ 0 :=
begin
  suffices : 0 < (2 * (n:ℚ) + 2^pk.succ), from (ne_of_lt this).symm,
  have : (0:ℚ) ≤ n := nat.cast_nonneg n,
  have hp : 2 ≤ 2^pk.succ := two_le_pos_pow_two pk,
  have : (2:ℚ) ≤ 2^pk.succ := by { norm_cast, exact hp },
  linarith,
end

theorem pnat_even_or_odd (n : ℕ+) : (∃t: ℕ, (n:ℕ) = 2 * t + 1) ∨ (∃t: ℕ, (n:ℕ) = 2 * (t + 1)) :=
begin
  obtain heven | hodd  := nat.even_or_odd n.val,
  { right,
    obtain ⟨t', ht'⟩ := heven,
    have htp': 0 < t',
    { have := n.property, omega },
    cases t',
    { exfalso, exact nat.lt_asymm htp' htp' },
    exact ⟨t', ht'⟩
  },
  { left,
    exact hodd,
  }
end

def next_m (m : ℕ → ℕ+) (k : ℕ) (mk : ℕ+) : ℕ → ℕ+
| i := if h: i < k then m i else mk

lemma next_m_prev_eq (m : ℕ → ℕ+) (k: ℕ) (mk : ℕ+) (i: ℕ) (hi: i ∈ finset.range k) :
      (1:ℚ) + 1 / m i = 1 + 1 / (next_m m k mk i) :=
begin
  unfold next_m,
  have h2: ite (i < k) (m i : ℚ) mk = (m i:ℚ) := if_pos (finset.mem_range.mp hi),
  rw [ite_cast, h2],
end

theorem imo2013_q1 (n : ℕ+) (k : ℕ) :
    (∃m : ℕ → ℕ+, (1:ℚ) + (2^k - 1) / n = (∏ i in finset.range k, (1 + 1 / (m i)))) :=
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
    let tp: ℕ+ := ⟨t + 1, nat.succ_pos t⟩,
    obtain ⟨pm, hpm⟩ := hpk tp,
    let m := λi, if i < pk then pm i else ⟨2 * t + 1, nat.succ_pos _⟩,
    use m,

    have h' : ∏ (i : ℕ) in finset.range pk, ((1:ℚ) + 1 / ↑(m i)) =
              ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(pm i)),
    { suffices : ∀ i : ℕ, i ∈ finset.range pk → (1:ℚ) + 1 / m i = 1 + 1 / pm i,
      from finset.prod_congr rfl this,
      intros i hi,
      simp [finset.mem_range.mp hi] },

    have hmpk : ((m pk):ℚ) = 2 * t + 1,
    { have : (m pk) = ⟨2 * t + 1, _⟩ := dif_neg (irrefl pk),
      rw this,
      simp },

    have hneq0 : (2 * (t : ℚ) + 1) ≠ 0 := by { norm_cast, apply (2 * t).succ_ne_zero },

    calc (1:ℚ) + (2 ^ pk.succ - 1) / ↑n
        = 1 + (2^pk.succ - 1) / ((2 * t + 1) : ℕ) : by rw [coe_coe n, ht]
    ... = 1 + (2 * 2^pk - 1) / ((2 * t + 1) : ℕ) : by rw pow_succ
    ... = (1 + 1 / (2 * t + 1)) * (1 + (2^pk - 1) / (t + 1))
             : by { field_simp [nat.cast_add_one_ne_zero t], ring }
    ... = (1 + 1 / (2 * t + 1)) * (1 + (2^pk - 1) / tp) : by { norm_cast }
    ... = (1 + 1 / ↑(m pk)) * ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(m i)) : by rw [hpm, h', ←hmpk]
    ... = ∏ (i : ℕ) in finset.range pk.succ, (1 + 1 / ↑(m i)) : (finset.prod_range_succ _ pk).symm },

  { obtain ⟨t, ht⟩ := ht,
    let tp: ℕ+ := ⟨t + 1, nat.succ_pos t⟩,
    obtain ⟨pm, hpm⟩ := hpk tp,

    have h1: 0 < 2 * t + 2^pk.succ := arith_lemma_nat pk t,

    let m := λi, if i < pk then pm i else ⟨2 * t + 2^pk.succ, h1⟩,
    use m,

    have h' : ∏ (i : ℕ) in finset.range pk, ((1:ℚ) + 1 / ↑(m i)) =
              ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(pm i)),
    { suffices : ∀ i : ℕ, i ∈ finset.range pk → (1:ℚ) + 1 / m i = 1 + 1 / pm i,
      from finset.prod_congr rfl this,
      intros i hi,
      simp [finset.mem_range.mp hi] },

    have hmpk' : (m pk) = ⟨2 * t + 2^pk.succ, _⟩ := dif_neg (irrefl pk),

    have hmpk : ((m pk):ℚ) = 2 * t + 2^pk.succ,
    { rw hmpk',
      norm_cast },

    have h2: 2 * t + 2^pk.succ ≠ 0 := ne_of_gt h1,
    have h'' : (2 * (t:ℚ) + 2^pk.succ) ≠ 0 := arith_lemma pk t,

    calc (1:ℚ) + (2 ^ pk.succ - 1) / ↑n
        = 1 + (2 ^ pk.succ - 1) / ((2 * (t + 1)):ℕ) : by rw [coe_coe n, ht]
    ... = (1 + 1 / (2 * t + 2^pk.succ)) * (1 + (2 ^ pk.succ - 2) / (2 * (↑t + 1)))
               : by { field_simp[nat.cast_add_one_ne_zero t], ring }
    ... = (1 + 1 / (2 * t + 2^pk.succ)) * (1 + (2 * 2 ^ pk - 2) / (2 * (↑t + 1)))
               : by rw pow_succ
    ... = (1 + 1 / (2 * t + 2^pk.succ)) * (1 + (2 ^ pk - 1) / (↑t + 1))
               : by { field_simp[nat.cast_add_one_ne_zero t], ring }
    ... = (1 + 1 / (2 * t + 2^pk.succ)) * (1 + (2 ^ pk - 1) / tp) : by norm_cast
    ... = (1 + 1 / ↑(m pk)) * ∏ (i : ℕ) in finset.range pk, (1 + 1 / ↑(m i)) : by rw [hpm, h', ←hmpk]
    ... = ∏ (i : ℕ) in finset.range pk.succ, (1 + 1 / ↑(m i)) : (finset.prod_range_succ _ pk).symm }
end
