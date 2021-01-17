import data.pnat.basic
import algebra.big_operators.pi

open_locale big_operators

/-
Direct translation of solution found in https://www.imo-official.org/problems/IMO2013SL.pdf
-/

theorem imo2013_q1
  (n: ℕ+)
  (k: ℕ):
  (∃m: fin k → ℕ+, 1 + ((2^k - 1): ℚ) / n =
          ∏ (i: fin k), (1 + 1 / ((m i) : ℚ))) :=
begin
  induction k with kp hkp,
  {
    use λ _, 1,
    simp only [finset.card_fin, add_zero, finset.prod_const, zero_div, pow_zero, sub_self],
  },
  obtain ⟨mp, hmp⟩ := hkp,
  have ht: (∃t: ℕ+, n.1 = 2 * t.1 - 1) ∨ (∃t: ℕ+, n.1 = 2 * t.1),
  { sorry },
  cases ht,
  {
    obtain ⟨t, ht⟩ := ht,
    use (λi: fin kp.succ, if hi: i.val < kp then mp ⟨i.val, hi⟩ else ⟨2 * t.val - 1, sorry⟩),
    sorry,
  },
  obtain ⟨t, ht⟩ := ht,
  sorry,
end
