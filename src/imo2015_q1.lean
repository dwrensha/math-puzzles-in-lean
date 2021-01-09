import data.pnat.basic
import algebra.big_operators.pi

open_locale big_operators

/-
Direct translation of solution found in https://www.imo-official.org/problems/IMO2013SL.pdf
-/

theorem imo2013Q1
  (n k: ℕ+) :
  (∃s: finset ℕ, s.card = k ∧
                 (∃m: ℕ → ℕ+, 1 + ((2^k.1 - 1): ℚ) / n =
                              ∏ (i: ℕ) in s, (1 + 1 / ((m i) : ℚ)))) :=
begin
  sorry
end
