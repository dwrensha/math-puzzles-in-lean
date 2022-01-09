import data.real.basic
import data.set.intervals.basic

/-
(from http://www.mit.edu/~erst/puzzles/)

Q. Can the unit square [0, 1] x [0, 1] be colored with three colors so that any
pair of points with the same color have a distance between them of at most one?

A. No.

-/

def unit_square := set.Icc (0 : ℝ) (1 : ℝ) × set.Icc (0 : ℝ) (1 : ℝ)

def within_distance_one (p1 p2 : unit_square) : Prop :=
(p1.fst.val - p2.fst.val) ^ 2 + (p1.snd.val - p2.snd.val) ^ 2 ≤ 1

theorem square_three_coloring
  (f : unit_square → fin 3)
  (h : ∀ p₁ p₂ : unit_square, f p₁ = f p₂ → within_distance_one p₁ p₂)
  : false :=
begin
  -- It suffices to consider just the boundary of the square...
  sorry
end
