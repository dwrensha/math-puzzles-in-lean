import algebra.big_operators.basic
import data.finset.basic
import data.rat.basic
import data.rat.order
import data.set.intervals.basic

/-
  A set S contains 0 and 1, and the mean of every finite nonempty subset of S.
  Prove that S contains all of the rational numbers in the unit interval.
-/

open_locale big_operators

theorem generating_the_rationals
  (S : set ℚ)
  (h0 : (0 : ℚ) ∈ S)
  (h1 : (1 : ℚ) ∈ S)
  (hm : ∀s: finset {q // q ∈ S}, (∑i in s, i.val / finset.card s) ∈ S) :
  set.Icc 0 1 ⊆ S :=
begin
  sorry
end
