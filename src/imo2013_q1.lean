import data.pnat.basic
import algebra.big_operators.pi

open_locale big_operators

/-
Direct translation of solution found in https://www.imo-official.org/problems/IMO2013SL.pdf
-/

theorem imo2013Q1
  (n k: ℕ+) :
  (∃m: fin k → ℕ+, 1 + ((2^k.1 - 1): ℚ) / n =
          ∏ (i: fin k), (1 + 1 / ((m i) : ℚ))) :=
begin
  induction k with kp hkp,
  sorry
end
