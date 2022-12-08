import data.rat.basic
import data.real.basic
import data.complex.exponential
import analysis.special_functions.pow
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
   (u : ℝ → ℝ)
   (f : ℝ → ℝ)
   (u_mono : monotone u)
   (f_cont : continuous f)
   (h : ∀ x : ℚ, u x = f x) :
   ∀ x : ℝ, u x = f x :=
begin
  -- suppose not.
  by_contra hn,
  push_neg at hn,

  -- then there is y such that f₁ y ≠ f₂ y
  obtain ⟨y, hy⟩ := hn,

--  let ε : ℝ := |f₁ y - f₂ y|,

  -- then find a δ such that for all z, |z-y| < δ implies that
  -- |f₁ z - f₁ y| < ε.

--  have h_cont' := metric.continuous_iff'.mp h_cont y ε (abs_pos' hy),
--  have h_cont2 := filter.eventually_iff.mp h_cont',
--  obtain ⟨s, hs, hs', hs''⟩ := mem_nhds_iff.mp h_cont2,

--  obtain ⟨δ, hδ0, hδ⟩ := metric.is_open_iff.mp hs' y hs'',
--  have := hδ.trans hs,

--  have : ∃δ : ℝ, ∀ z, dist z y < δ → dist (f₁ y) (f₁ y) < ε,
--  { sorry,},

  -- if f₂(y) > f₁(y), then choose such a z:ℚ that's greater than y
  -- otherwise, choose such a z:ℚ that's less than y

--  obtain h1 | h2 | h3 := lt_trichotomy (f₁ y) (f₂ y),
--  {  -- pick a rational point greater than y that's in the ball s,
--    sorry
--  },
--  { exact hy h2,},
--  {  -- pick a rational point less than y that's in the ball s,
--    sorry,
--  }

  -- in either case, we end up contradicting h_mono.

  sorry,
end

lemma int_dichotomy (z : ℤ) : ∃ n : ℕ, (n:ℤ) = z ∨ -(n:ℤ) = z :=
begin
  cases z,
  { use z, left, simp only [int.of_nat_eq_coe]},
  { use z + 1, right, refl },
end

lemma exp_characterization
    (u : ℝ → ℝ)
    (hu : ∀ x y : ℝ, u (x + y) = u x * u y)
    (hu0 : u 0 = 1)
    (hm : strict_mono u ∨ strict_anti u) :
    (∃ k : ℝ, ∀ x : ℝ, u x = real.exp (k * x)) :=
begin
  -- Thus u(nx) = u(x)ⁿ for all n ∈ ℤ, x ∈ ℝ.
  have h8 : ∀ n : ℕ, ∀ x : ℝ, u (n * x) = (u x) ^ n,
  { intro n,
    induction n with pn hpn,
    { intro x,
      simp only [algebra_map.coe_zero, zero_mul, pow_zero],
      exact hu0, },
    { intro x,
      have hp1: ↑(pn.succ) * x = ↑pn * x + x,
      { have : ↑pn * x + x = (↑pn + 1) * x := by ring,
        rw[this, nat.cast_succ] },
      rw[hp1],
      rw[hu (↑pn * x) x],
      rw[hpn x],
      rw[pow_succ, mul_comm] } },

  have h8'' : ∀ x, (u x) * u (-x) = 1,
  { intro x,
    have := hu x (-x),
    rw[add_right_neg] at this,
    rw[← this],
    exact hu0 },

  have hunz : ∀ x, 0 < u x,
  { intro x,
    by_contra H, push_neg at H,
    have H1 := one_div_nonpos.mpr H,
    obtain h1 | h2 | h3 := lt_trichotomy x 0,
    { have h10 := h8'' x,
      have hx0 : 0 < -x := by linarith,
      cases hm; nlinarith [hm hx0, hm h1]},
    { rw [h2,hu0] at H, linarith},
    { have h10 := h8'' x,
      have hx0 : -x < 0 := by linarith,
      cases hm; nlinarith [hm hx0, hm h3]}},

  have h8' : ∀ x, u (-x) = 1 / (u x),
  { intro x,
    have := (ne_of_lt (hunz x)).symm,
    field_simp,
    rw[mul_comm],
    exact h8'' x },

  have h9 : ∀ z : ℤ, ∀ x : ℝ, u (z * x) = (u x) ^ z,
  { intros z x,
    obtain ⟨n, hn⟩ := int_dichotomy z,
    cases hn,
    { rw[←hn],
      norm_cast,
      exact h8 _ _ },
    { have h10:= h8 n x,
      rw[←hn],
      have h11: ↑-((↑n):ℤ) * x = - (n * x) := by norm_num,
      rw[h11, h8' _],
      have := hunz (↑n * x),
      have : u (↑ n * x) ≠ (0:ℝ) := by linarith,
      field_simp,
      rw[←h10],
      field_simp}},

  -- Let eᵏ = u(1);
  have hek : ∃ k, real.exp k = u 1,
  { use real.log (u 1), exact real.exp_log (hunz 1)},
  obtain ⟨k,hk⟩ := hek,

  -- then u(n) = eᵏⁿ for all n ∈ ℕ
  have hnexp : ∀ n : ℕ, u n = real.exp (k * n),
  { intro n,
    have h10 := h9 n 1,
    rw[←hk, mul_one] at h10,
    norm_cast at h10,
    rw[h10, mul_comm],
    exact (real.exp_nat_mul _ _).symm },

  -- and u(p/q) = (u(p))^(1/q) = e^(k(p/q))
  -- for all p ∈ ℤ, q ∈ ℕ, so u(x) = e^(kx) for all x ∈ ℚ.

  have hzexp : ∀ z : ℤ, u z = real.exp (k * z),
  { intro z,
    obtain ⟨n, hn⟩ := int_dichotomy z,
    cases hn,
    { rw[←hn],
      norm_cast,
      exact hnexp n},
    { rw[←hn],
      have := h9 (-↑n) 1,
      rw[mul_one] at this,
      rw[this, ←hk],
      rw [real.exp_mul],
      norm_cast }},

  have hp : ∀ p : ℕ, 0 < p → ∀ x : ℝ, u (x / p) = (u x) ^ (1 / (p:ℝ)),
  { intros p hp x,
    cases p,
    { exfalso, exact nat.lt_asymm hp hp},
    have h12: ∀ n : ℕ, (u (x / p.succ))^n = u (x * n / p.succ),
    { intro n,
      induction n with pn hpn,
      { simp[hu0.symm] },
      { have h10: x * ↑(pn.succ) / ↑(p.succ) = x * ↑pn / ↑(p.succ) + x / ↑(p.succ),
        { field_simp, ring },
        rw[h10],
        have h11 := hu (x * ↑pn / ↑(p.succ)) (x / ↑(p.succ)),
        rw[h11, ← hpn],
        exact pow_succ' _ _}},
        replace h12 := h12 p.succ,
        have h13 : x * ↑(p.succ) / ↑(p.succ) = x,
        { have : (p.succ : ℝ) ≠ 0 := ne_zero.ne _,
          exact (div_eq_iff this).mpr rfl },
        rw[h13] at h12,
        rw[← h12],
        have h14: u (x / ↑(p.succ)) ^ p.succ = u (x / ↑(p.succ)) ^ (p.succ:ℝ) := by norm_cast,
        rw[h14],
        have h15 := le_of_lt (hunz (x / ↑(p.succ))),
        rw[←real.rpow_mul h15 _],
        have : ((p:ℝ) + 1) ≠ 0 := by { norm_cast, exact ne_of_gt hp },
        field_simp},

  have hq : ∀ q : ℚ, u q = real.exp (k * q),
  { intro q,
    rw[rat.cast_def q],
    rw[hp q.denom q.pos q.num],
    rw[hzexp q.num],
    rw[←real.exp_mul],
    ring_nf},

  use k,

  -- Since u in monotonic and the rationals are dense in ℝ, we have u(x) = e^(kx) for all x ∈ ℝ.
  -- Therefore all solutions of the form u(x) = e^(kx), k ∈ ℝ.
  let f := λ x, real.exp (k * x),
  have hf : ∀ q : ℚ, u q = f q,
  { intro q, exact hq q },

  have h20 : continuous (real.exp) := real.continuous_exp,
  have h21 : continuous (λ x : ℝ, k * x) := continuous_mul_left k,
  have hfm : continuous f := continuous.comp h20 h21,

  cases hm,
  { have hmu : monotone u := strict_mono.monotone hm,
    exact extend_function u f hmu hfm hf },
  {sorry}
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

  have hum : (strict_mono u ∨ strict_anti u),
  { cases hm,
    { obtain h1 | h2 | h3 := lt_trichotomy C 0,
      { right, intros x y hxy, nlinarith[hm hxy, h6 x, h6 y] },
      { rw[h2] at hCnz, exfalso, apply hCnz, refl},
      { left, intros x y hxy, nlinarith[hm hxy, h6 x, h6 y] }},
    { obtain h1 | h2 | h3 := lt_trichotomy C 0,
      { left, intros x y hxy, nlinarith[hm hxy, h6 x, h6 y] },
      { rw[h2] at hCnz, exfalso, apply hCnz, refl},
      { right, intros x y hxy, nlinarith[hm hxy, h6 x, h6 y] }}},

  exact exp_characterization u h7 h00 hum
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
