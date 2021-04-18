import data.nat.basic
import data.real.basic
import order.basic

import tactic.gptf

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

lemma lemma_1 {x y z: ℝ} (h: z ≤ x + y) : z / 2 ≤ x ∨ z / 2 ≤ y :=
begin
  by_contra H,
  push_neg at H,
  obtain ⟨h1, h2⟩ := H,
  linarith,
end

noncomputable def xx_aux {n: ℕ} (d : ℝ) (a: fin n → ℝ) : ∀ i, i < n → ℝ
 | 0 h := a ⟨0, h⟩ - d/2
 | (nat.succ k) h := max (xx_aux k (nat.lt_of_succ_lt h)) (a ⟨nat.succ k, h⟩ - d / 2)

noncomputable def xx {n: ℕ} (d : ℝ) (a: fin n → ℝ) (i : fin n) : ℝ := xx_aux d a i.1 i.2

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
  obtain ⟨⟨p, hp, hp1⟩, hpp⟩ := hb q,
  obtain ⟨⟨r, hr, hr1⟩, hrr⟩ := hc q,
  have hpr := le_trans hp hr,
  have hdi := hd q,
  split,
  { intros x x_mono,

    have h0 : 0 ≤ x r - x p := sub_nonneg.mpr (x_mono hpr),

    have h1 := calc dm
         = a p - a r : by {sorry}
     ... ≤ (a p - a r) + (x r - x p) : le_add_of_nonneg_right h0
     ... = (a p - x p) + (x r - a r) : by ring,

    obtain hpm | hrm := lemma_1 h1,
    { use p,
      calc dm / 2 ≤ a p - x p : hpm
              ... ≤ abs (a p - x p) : le_abs_self _
              ... = abs (x p - a p) : abs_sub _ _ },
    { use r,
      calc dm / 2 ≤ x r - a r : hrm
              ... ≤ abs (x r - a r) : le_abs_self _ }
  },
  {
    use xx dm a,
    split,
    { sorry },
    { sorry },
  },
end
