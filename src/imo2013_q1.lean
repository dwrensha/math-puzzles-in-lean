import data.pnat.basic
import algebra.big_operators.pi

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
  induction k with kp hkp,
  {
    use λ _, 1,
    simp only [finset.card_empty, add_zero, finset.prod_const, zero_div, finset.range_zero, pow_zero, sub_self],
  },
  obtain ⟨mp, hmp⟩ := hkp,
  have ht: (∃t: ℕ+, n.1 = 2 * t.1 - 1) ∨ (∃t: ℕ+, n.1 = 2 * t.1),
  { sorry },
  cases ht,
  {
    obtain ⟨t, ht⟩ := ht,
    use (λi: ℕ, if hi: i < kp then mp i else ⟨2 * t.val - 1, sorry⟩),
    sorry,
  },
  obtain ⟨t, ht⟩ := ht,
  sorry,
end
