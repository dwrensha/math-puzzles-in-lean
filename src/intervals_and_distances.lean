import data.finset.basic
import data.fintype.basic
import data.set.intervals.basic
import data.real.basic data.nat.basic

open_locale big_operators

/-
  Let S be the union of k disjoint, closed intervals in the unit interval [0,1].
  Suppose S has the property that for every real number d in [0,1], there are two
  points in S at distance d. Prove that the sum of the lengths of the intervals
  in S is at least 1/k.
-/

def unit_interval: Type := @subtype ℝ (set.Icc 0 1)

structure subinterval :=
(lower_bound: unit_interval)
(upper_bound: unit_interval)
(well_formed: lower_bound.val ≤ upper_bound.val)

def in_subinterval (x: ℝ) (s: subinterval) : Prop :=
  s.lower_bound.val ≤ x ∧ x ≤ s.upper_bound.val

def subinterval_length (s: subinterval) : ℝ := s.upper_bound.val - s.lower_bound.val

theorem intervals_and_distances
  (all_intervals: ℕ → subinterval)
  (interval_indexes: finset ℕ)
  (h: ∀ d: unit_interval,
        (∃ a b : ℝ,
          d.val = b - a
          ∧ (∃i ∈ interval_indexes, in_subinterval a (all_intervals i))
          ∧ (∃j ∈ interval_indexes, in_subinterval b (all_intervals j))))
  : (1 : ℝ) / interval_indexes.card ≤
       (∑ i in interval_indexes, subinterval_length (all_intervals i)) :=
begin
  sorry
end



