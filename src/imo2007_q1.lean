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
  (a b c d: fin n → ℝ)
  (hb : ∀i: fin n, is_greatest {x : ℝ | ∃ j : fin n, j ≤ i ∧ x = a j } (b i))
  (hc : ∀i: fin n, is_least {x : ℝ | ∃ j : fin n, i ≤ j ∧ x = a j } (c i))
  (hd : ∀i: fin n, d i = b i - c i )
  (dm : ℝ)
  (hdm : is_greatest {x : ℝ | ∃ i : fin n, x = d i} dm)
  : (∀ x: fin n → ℝ, monotone x → ∃ i : fin n, dm / 2 ≤ abs (x i - a i) )
    ∧ (∃ x: fin n → ℝ, monotone x ∧
         ∃ i : fin n, dm / 2 = abs (x i - a i)
        ∧ ∀ i : fin n, abs (x i - a i) ≤ dm / 2) :=
begin
  obtain ⟨⟨q, hq⟩, hqq⟩ := hdm,
  obtain ⟨⟨p, hp⟩, hpp⟩ := hb q,
  obtain ⟨⟨r, hr⟩, hrr⟩ := hc q,
  have hdi := hd q,
  split,
  { intros x x_mono,
    sorry,
  },
  {
    sorry
  },
end
