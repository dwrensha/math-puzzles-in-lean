import data.finset.basic
import data.set.intervals.basic
import data.real.basic data.nat.basic

open_locale big_operators

#print set.Icc

#print finset

variables {k : Type}

def unit_interval: Type := @subtype ℝ (set.Icc 0 1)

structure subinterval :=
(lower_bound: unit_interval)
(upper_bound: unit_interval)
(well_formed: lower_bound.val ≤ upper_bound.val)


theorem intervals_and_distances
  (intervals: finset subinterval)
  (h: ∀ d: unit_interval, (∃ a b : ℝ, d.val = b - a /- ∧ (∃i ∈ intervals, i.val < 0  ) -/))
  : (1 : ℝ) / intervals.card ≤ (∑ i in intervals, (i.upper_bound.val - i.lower_bound.val)) :=
begin
  sorry
end

