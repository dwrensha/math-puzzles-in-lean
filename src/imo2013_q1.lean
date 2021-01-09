import data.pnat.basic
import algebra.big_operators.pi

open_locale big_operators

/-
Direct translation of solution found in https://www.imo-official.org/problems/IMO2013SL.pdf
-/

theorem imo2013Q1
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
  sorry,
end
