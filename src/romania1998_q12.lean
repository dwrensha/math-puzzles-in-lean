import data.rat.basic
import data.real.basic
import data.complex.exponential
import topology.metric_space.basic

/-
Romanian Mathematical Olympiad 1998, Problem 12

Find all functions u : ℝ → ℝ for which there exists a strictly monotonic
function f : ℝ → ℝ such that

  ∀ x,y ∈ ℝ, f(x + y) = f(x)u(y) + f(y)

-/

lemma abs_pos' {x y : ℝ} (hy : x ≠ y) : 0 < |x - y| :=
begin
  obtain h1 | h2 | h3 := lt_trichotomy x y,
  { -- x < y
    simp only [abs_pos, ne.def],
    linarith,},
  { -- x = y,
    rw[h2] at hy,
    exfalso,
    exact hy rfl },
  { simp only [abs_pos, ne.def],
    linarith }
end

lemma extend_function
   (f₁ : ℝ → ℝ)
   (f₂ : ℝ → ℝ)
   (h_cont : continuous f₁)
   (h_mono : monotone f₂)
   (h : ∀ x : ℚ, f₁ x = f₂ x) :
   ∀ x : ℝ, f₁ x = f₂ x :=
begin
  -- suppose not.
  by_contra hn,
  push_neg at hn,

  -- then there is y such that f₁ y ≠ f₂ y
  obtain ⟨y, hy⟩ := hn,

  let ε : ℝ := |f₁ y - f₂ y|,

  -- then find a δ such that for all z, |z-y| < δ implies that
  -- |f₁ z - f₁ y| < ε.

  have h_cont' := metric.continuous_iff'.mp h_cont y ε (abs_pos' hy),
  have h_cont2 := filter.eventually_iff.mp h_cont',
  obtain ⟨s, hs, hs', hs''⟩ := mem_nhds_iff.mp h_cont2,

  obtain ⟨δ, hδ0, hδ⟩ := metric.is_open_iff.mp hs' y hs'',
  have := hδ.trans hs,

--  have : ∃δ : ℝ, ∀ z, dist z y < δ → dist (f₁ y) (f₁ y) < ε,
--  { sorry,},

  -- if f₂(y) > f₁(y), then choose such a z:ℚ that's greater than y
  -- otherwise, choose such a z:ℚ that's less than y

  obtain h1 | h2 | h3 := lt_trichotomy (f₁ y) (f₂ y),
  {  -- pick a rational point greater than y that's in the ball s,
    sorry
  },
  { exact hy h2,},
  {  -- pick a rational point less than y that's in the ball s,
    sorry,
  }

  -- in either case, we end up contradicting h_mono.


  -- alternatively, f1 has a unique continuous extension on R

end

lemma exp_strict_mono' (k x y : ℝ) (hkp: 0 < k) (h : x < y) :
  real.exp(k * x) < real.exp(k * y) :=
begin
  finish,
end

lemma exp_strict_anti' (k x y : ℝ) (hkp: k < 0) (h : x < y) :
  real.exp(k * y) < real.exp(k * x) :=
begin
  finish
end

example (p : Prop) (h : ¬ ¬ p) : p :=
begin
  exact not_not.mp h
end

lemma romania1998_q12_mp (u : ℝ → ℝ) :
    (∃ f : ℝ → ℝ, (strict_mono f ∨ strict_anti f)
        ∧ ∀ x y : ℝ, f (x + y) = f x * u y + f y) →
    (∃ k : ℝ, ∀ x : ℝ, u x = real.exp (k * x)) :=
begin
  intro h,
  obtain ⟨f, hm, hf⟩ := h,
  -- First, letting y = 0, we obtain f(x) = f(x)u(0) + f(0) for all x ∈ ℝ,
  have hy0 : ∀ x : ℝ, f x = f x * u 0 + f 0,
  { intro x, have := hf x 0, rw [ add_zero] at this, exact this },

  -- thus u(0) ≠ 1 would imply f(x) = f(0) / (1 - u(0)) for all x,
  have h0 : (u 0 ≠ 1) → ∀ x : ℝ, f x = f 0 / (1 - u 0),
  { intros hu0 x,
    have hy0x := hy0 x,
    have hy0x1 := calc f 0
         = f x - f x * u 0 : (sub_eq_of_eq_add' (hy0 x)).symm
     ... = f x * (1 - u 0) : by { ring },
    rw[hy0x1],
    have : 1 - u 0 ≠ 0,
    { intro hz,
      exact hu0 (by linarith) },
    field_simp },

  -- which implies that f is constant, which we know is not the case
  have h0' : (u 0 ≠ 1) → false,
  { intros hu0,
    have hu0' := h0 hu0,
    cases hm;
    { have hu00 := hu0' 0,
      have hu01 := hu0' 1,
      have hm0 := @hm 0 1 (by norm_num),
      linarith } },

  -- so we must have u(0) = 1
  have h00 : u 0 = 1 := not_not.mp h0',
  clear h0 h0',
  rw [h00] at hy0,

  -- and f(0) = 0.
  have hf0 : f 0 = 0 := by { have := hy0 0, linarith },

  -- Then f(x) ≠ 0 for all x ≠ 0.
  have hfx0 : ∀ x, x ≠ 0 → f x ≠ 0,
  { intros x hx,
    cases hm with hm1 hm2,
    { obtain h1 | h2 | h3 := lt_trichotomy x 0,
      { rw [←hf0],
        exact ne_of_lt (hm1 h1)},
      { exfalso, exact hx h2},
      { rw [←hf0],
        exact (ne_of_lt (hm1 h3)).symm }},
    { obtain h1 | h2 | h3 := lt_trichotomy x 0,
      { have := hm2 h1,
        rw [hf0] at this,
        exact (ne_of_lt this).symm},
      { exfalso, exact hx h2},
      { have := hm2 h3,
        rw [hf0] at this,
        exact (ne_of_lt this) }}},

  -- Next, we have
  -- f(x)u(y) + f(y) = f (x + y) = f(x) + f(y)u(x)
  have h1 : ∀ x y : ℝ, f x * u y + f y = f x + f y * u x,
  { intros x y,
    rw[(hf x y).symm, add_comm],
    linarith[hf y x] },

  -- so f(x)(u(y) - 1) = f(y)(u(x) - 1) for all x,y ∈ ℝ.
  have h2 : ∀ x y : ℝ, f x * (u y - 1) = f y * (u x - 1) := by
  { intros x y, have := h1 x y, linarith },

  -- Thus for any x ≠ 0, y ≠ 0, we have (u(x) - 1) / f(x) = (u(y) - 1) / f(y).
  have h3 : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → (u x - 1) / f x =  (u y - 1) / f y,
  { intros x y hx hy,
    have hx1 := hfx0 x hx,
    have hy1 := hfx0 y hy,
    have := h2 x y,
    field_simp,
    linarith },

  -- So there exists C ∈ ℝ such that (u(x) - 1) / f(x) = C for all x ≠ 0.
  have h4: ∃ C : ℝ, ∀ x : ℝ, x ≠ 0 → (u x - 1) / f x = C,
  { use (u 1 - 1) / f 1,
    intros x hx,
    exact h3 x 1 hx one_ne_zero },
  obtain ⟨C, hC⟩ := h4,

  -- So u(x) = 1 + C f(x) for x ≠ 0;
  have h5 : ∀ x : ℝ, x ≠ 0 → u x = 1 + C * f x,
  { intros x hx,
    have hc1 := hC x hx,
    have hx1 := hfx0 x hx,
    field_simp at hc1,
    linarith },

  -- since u(0) = 1, f(0) = 0, this equation also holds for x = 0.
  have h6 : ∀ x : ℝ, u x = 1 + C * f x,
  { intro x,
    cases em (x = 0) with hz hnz,
    { rw [hz, hf0, h00], ring},
    { exact h5 x hnz } },

  -- If C = 0, then u(x) = 1 for all x and we are done.
  cases em (C = 0) with hCz hCnz,
  { use 0,
    intro x,
    rw [zero_mul, real.exp_zero],
    have := h6 x,
    rwa[hCz, zero_mul, add_zero] at this},

  -- Otherwise, observe
  --     u(x + y) = 1 + C f(x + y)
  --              = 1 + C f(x) u(y) + f(y)
  --              = u(y) + C f(x) u(y)
  --              = u(x) u(y)
  -- for all x,y ∈ ℝ.
  have h7 : ∀ x y : ℝ, u (x + y) = u x * u y,
  { intros x y,
    calc u (x + y) = 1 + C * f (x + y) : h6 (x + y)
              ...  = 1 + C * (f x * u y  + f y) : by {rw [hf x y]}
              ...  = u y + C * f x * u y : by { rw[h6 y], ring}
              ...  = u y * (1 + C * f x) : by ring
              ...  = u y * u x : by rw [h6 x]
              ...  = u x * u y : mul_comm (u y) (u x) },

  -- Thus u(nx) = u(x)ⁿ for all n ∈ ℤ, x ∈ ℝ.
  have h8 : ∀ n : ℕ, ∀ x : ℝ, u (n * x) = (u x) ^ n,
  { intro n,
    induction n with pn hpn,
    { intro x,
      simp only [algebra_map.coe_zero, zero_mul, pow_zero],
      exact h00, },
    { intro x,
      have hp1: ↑(pn.succ) * x = ↑pn * x + x,
      { have : ↑pn * x + x = (↑pn + 1) * x := by ring,
        rw[this, nat.cast_succ] },
      rw[hp1],
      rw[h7 (↑pn * x) x],
      rw[hpn x],
      rw[pow_succ, mul_comm] } },

  have h9 : ∀ n : ℤ, ∀ x : ℝ, u (n * x) = (u x) ^ n,
  { intros n x,
    cases n,
    { simp only [int.of_nat_eq_coe, int.cast_coe_nat, zpow_coe_nat],
      exact h8 n x,},
    { sorry },
  },


  -- Since u(x) = 1 + C f(x) for all x, u is strictly monotonic, and u(-x) = 1 / u(x)
  -- for all x, so u(x) > 0 for all x as u(0) = 1.

  -- Let eᵏ = u(1); then u(n) = eᵏⁿ for all n ∈ ℕ and u(p/q) = (u(p))^(1/q) = e^(k(p/q))
  -- for all p ∈ ℤ, q ∈ ℕ, so u(x) = e^(kx) for all x ∈ ℚ.
  -- Since u in monotonic and the rationals are dense in ℝ, we have u(x) = e^(kx) for all x ∈ ℝ.
  -- Therefore all solutions of the form u(x) = e^(kx), k ∈ ℝ.
  sorry,
end

lemma romania1998_q12_mpr (u : ℝ → ℝ) :
 (∃ k : ℝ, ∀ x : ℝ, u x = real.exp (k * x)) →
    (∃ f : ℝ → ℝ, (strict_mono f ∨ strict_anti f)
        ∧ ∀ x y : ℝ, f (x + y) = f x * u y + f y)
     :=
begin
  intro h,
  obtain ⟨k, hk⟩ := h,
  cases classical.em (k = 0) with hkz hknz,
  { -- k = 0
    use id,
    split,
    { left, exact strict_mono_id},
    { intros x y,
      rw [hk y, hkz, zero_mul, real.exp_zero, mul_one, id.def, id.def, id.def] }},
   { -- k ≠ 0
     let f : ℝ → ℝ := λ x, real.exp (k * x) - 1,
     have hfm : (strict_mono f ∨ strict_anti f),
     { cases classical.em (0 < k) with hkp hkn,
       { left,
         intros x y hxy,
         have := exp_strict_mono' k x y hkp hxy,
         exact sub_lt_sub_right this 1 },
       { right,
         intros x y hxy,
         have hkn' : k < 0, {
              simp only [not_lt] at *,
              exact ne.lt_of_le hknz hkn,
         },
         have := exp_strict_anti' k x y hkn' hxy,
         exact sub_lt_sub_right this 1 }
     },
     use f,
     use hfm,
     intros x y,
     rw [hk y],
     calc real.exp (k * (x + y)) - 1
             = real.exp (k * x + k * y) - 1 : by {rw[mul_add]}
         ... = real.exp (k * x) * real.exp (k * y) - 1 : by {rw[real.exp_add]}
         ... = (real.exp (k * x) - 1) * real.exp (k * y) +
                  (real.exp (k * y) - 1) : by ring
   }
end

theorem romania1998_q12 (u : ℝ → ℝ) :
  (∃ f : ℝ → ℝ, (strict_mono f ∨ strict_anti f)
        ∧ ∀ x y : ℝ, f (x + y) = f x * u y + f y) ↔
  (∃ k : ℝ, ∀ x : ℝ, u x = real.exp (k * x)) :=
⟨romania1998_q12_mp u, romania1998_q12_mpr u⟩
