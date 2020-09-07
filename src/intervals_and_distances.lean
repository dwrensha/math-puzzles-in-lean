import data.fintype.basic
import data.set.intervals.basic
import data.real.basic data.nat.basic

open_locale big_operators

#print set.Icc

#print finset

variables {k : Type}

def unit_interval: Type := @subtype ℝ (set.Icc 0 1)

structure sub_interval :=
(lower_bound: unit_interval)
(upper_bound: unit_interval)
(well_formed: lower_bound.val ≤ upper_bound.val)


theorem intervals_and_distances [fintype k]
  (intervals: k → sub_interval)
  (h: ∀ d: unit_interval, (∃ a b : ℝ, d.val = b - a) )
  : (1 : ℝ) <  (∑ i, ((intervals i).upper_bound.val - (intervals i).lower_bound.val))  :=
begin
  sorry
end

