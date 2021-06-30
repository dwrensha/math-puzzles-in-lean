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

lemma lemma_1 {x y z: ℝ} (h: z ≤ x + y) : z / 2 ≤ x ∨ z / 2 ≤ y :=
begin
  by_contra H,
  push_neg at H,
  obtain ⟨h1, h2⟩ := H,
  linarith,
end

noncomputable def xx_seq (a: ℕ → ℝ) : ℕ → ℝ
 | 0 := a 0
 | m@(nat.succ k) := max (xx_seq k) (a m)

lemma xx_seq_monotone (a: ℕ → ℝ) : monotone (xx_seq a) :=
begin
  have h: ∀ n, xx_seq a n ≤ xx_seq a (nat.succ n),
  {
    intro n,
    unfold xx_seq,
    exact le_max_left (xx_seq a n) (a (nat.succ n)),
  },
  exact monotone_of_monotone_nat h,
end

lemma monotone_fin_of_nat {n : ℕ} (f: ℕ → ℝ) (h : monotone f) : monotone (λ m: fin n, f m.val) :=
begin
  intros m1 m2 hm,
  exact h hm,
end

noncomputable def x_seq' {n : ℕ} (d: ℝ) (a: fin n → ℝ) : ℕ → ℝ :=
xx_seq (λm, if h: m < n then (a ⟨m, h⟩ - d/2) else 0)

noncomputable def x_seq {n : ℕ} (d : ℝ) (a: fin n → ℝ) : fin n → ℝ :=
λ m, x_seq' d a m.val

lemma x_seq_monotone {n : ℕ} (d : ℝ) (a : fin n → ℝ) : monotone (x_seq d a) :=
begin
  exact monotone_fin_of_nat (x_seq' d a) (xx_seq_monotone _),
end

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
         (∃ i : fin n, dm / 2 = abs (x i - a i))
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
              ... = abs (x p - a p) : abs_sub_comm _ _ },
    { use r,
      calc dm / 2 ≤ x r - a r : hrm
              ... ≤ abs (x r - a r) : le_abs_self _ }
  },
  {
    use x_seq dm a,
    split,
    { exact x_seq_monotone dm a, },
    { split,
      { sorry },
      { sorry },
    },
  },
end

