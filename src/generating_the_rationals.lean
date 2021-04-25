import algebra.big_operators.basic
import data.finset.basic
import data.nat.parity
import data.rat.basic
import data.rat.order
import data.set.intervals.basic

import tactic.field_simp

/-
  A set S contains 0 and 1, and the mean of every finite nonempty subset of S.
  Prove that S contains all of the rational numbers in the unit interval.
-/

open_locale big_operators

lemma contains_dyadics
  (S : set ℚ)
  (h0 : (0 : ℚ) ∈ S)
  (h1 : (1 : ℚ) ∈ S)
  (hm : ∀s: finset {q // q ∈ S}, (∑i in s, i.val / finset.card s) ∈ S)
  (m n : ℕ)
  (hmn : m ≤ 2^n) :
  (m : ℚ) / 2^n ∈ S :=
begin
  revert m,
  induction n with pn hpn,
  { intros m hmn,
    rw pow_zero at hmn,
    cases m,
    { simpa },
    { simpa [nat.le_zero_iff.mp (nat.succ_le_succ_iff.mp hmn)] } },
  {
    intros m hmn,
    obtain ⟨t, ht : m = 2 * t⟩ | ⟨t, ht : m = 2 * t + 1⟩ := m.even_or_odd,
    { rw ht, sorry },
    { sorry
    },
  },
end

theorem generating_the_rationals
  (S : set ℚ)
  (h0 : (0 : ℚ) ∈ S)
  (h1 : (1 : ℚ) ∈ S)
  (hm : ∀s: finset {q // q ∈ S}, (∑i in s, i.val / finset.card s) ∈ S) :
  set.Icc 0 1 ⊆ S :=
begin
  sorry
end
