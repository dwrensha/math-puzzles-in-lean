import analysis.convex.basic
import analysis.normed_space.inner_product
import geometry.euclidean.basic
import geometry.euclidean.triangle

/-
Polish Mathematical Olympiad 1998, Problem 5

Points D, E lie on side AB of the triangle ABC and satisfy

    (AD/DB) * (AE/EB) = (AC/CB)².

Prove that ∠ACD = ∠BCE.

-/

open_locale euclidean_geometry

theorem poland1998_q5
    (A B C D E: euclidean_space ℝ (fin 2))
--  TODO: something like (ht : triangle A B C)
    (hd : D ∈ segment A B)
    (he : E ∈ segment A B)
    (hr : (dist A D / dist D B) * (dist A E / dist E B) = (dist A C / dist C B)^2) :
    ∠ A C D = ∠ B C E :=
begin
  sorry
end

