import data.nat.basic
import data.real.basic
import order.basic

/- IMO 2007 Problem 1

Given a sequence a₁, a₂, ... aₙ of real numbers. For each i (1≤i≤n) define

                 dᵢ = max { aⱼ : 1≤j≤i } - min { aⱼ : i≤j≤n }

and let

                 d = max { dᵢ : 1≤i≤n }.

(a) Prove that for arbitrary real numbers x₁ ≤ x₂ ≤ ... ≤ xₙ,

                 max { |xᵢ - aᵢ| : 1≤i≤n } ≥ d/2.       (1)

(b) Show that there exists a sequence x₁ ≤ x₂ ≤ ... ≤ xₙ of real numbers
such that we have equality in (1).

-/


theorem imo2007_q1
  (n : ℕ)
  (a : fin n → ℝ)
  (di : fin n → ℝ)
  (hdi : ∀i: fin n, true ) -- {{ a j // 1 ≤ j ∧ j ≤ i }}
  (d : ℝ)
  /- TODO define constraints on d-/
  : (∀ x: fin n → ℝ, monotone x → true )
    ∧ (∃ x: fin n → ℝ, monotone x → true) :=
begin
 sorry
end
