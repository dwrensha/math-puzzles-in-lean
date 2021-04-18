import analysis.normed_space.inner_product
import geometry.euclidean.basic

/-
Bulgarian Mathematical Olympiad 1998, Problem 2

A convex quadrilateral ABCD has AD = CD and ∠DAB = ∠ABC < 90°.
The line through D and the midpoint of BC intersects line AB
in point E. Prove that ∠BEC = ∠DAC. (Note: The problem is valid
without the assumption ∠ABC < 90°.)

-/

open_locale euclidean_geometry

theorem bulgaria1998_q2
    (A B C D E M: euclidean_space ℝ (fin 2))
    (H1 : ∥A - D∥ = ∥C - D∥)
    (H2 : ∠ B E C = ∠ D A C)
    (H3 : M = midpoint ℝ B C) :
    ∠ B E C = ∠ D A C :=
begin
  sorry
end
