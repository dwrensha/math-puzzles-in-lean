import analysis.normed_space.inner_product
import geometry.euclidean.basic
import geometry.euclidean.triangle

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
    (H1 : dist D A = dist D C)
    (H2 : ∠ D A B = ∠ A B C)
    (H3 : M = midpoint ℝ B C) :
    ∠ B E C = ∠ D A C :=
begin
  let x := ∠ D A C,
  have : ∠ D A C = ∠ D C A := euclidean_geometry.angle_eq_angle_of_dist_eq H1,
  let y := ∠ C A B,
  have : ∠ A B C = x + y,
  {
    rw ← H2,
    sorry, -- hm... might need the acuteness assumption, actually.
  },
  sorry
end
