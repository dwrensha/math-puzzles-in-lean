import data.int.basic
import data.int.modeq
import data.zmod.basic

import tactic.ring

/-
Indian Mathematical Olympiad 1998, problem 1

(a) Show that the product of two numbers of the form a² + 3b² is again of that form.
(b) If an integer n is such that 7n is of the form a² + 3b², prove that n is also of that form.
-/

theorem india1998_q1a (a₁ a₂ b₁ b₂ : ℤ) :
  (∃ a₃ b₃, (a₁^2 + 3 * b₁^2) * (a₂^2 + 3 * b₂^2) = (a₃^2 + 3 * b₃^2)) :=
⟨a₁ * a₂ + 3 * b₁ * b₂,
 a₁ * b₂ - b₁ * a₂,
 by ring⟩

lemma lemma1 (a: ℤ) : ((a : zmod 7).val : ℤ) = a % 7 :=
begin
  obtain (hp : 0 ≤ a) | (hn : a < 0) := le_or_lt 0 a,
  { obtain ⟨A, hA⟩ := int.eq_coe_of_zero_le hp,
    simp [hA, zmod.val_nat_cast A] },
  { have hnn : a = - (- a) := eq_neg_of_eq_neg rfl,
    let neg_one : ℤ := -1,
    rw [neg_eq_neg_one_mul (-a)] at hnn,
    have h2 : ((( neg_one * -a ) : ℤ) : zmod 7) = ((neg_one : ℤ) : zmod 7) * ((-a : ℤ) : zmod 7) := by norm_cast,
    have h5 : 0 ≤ -a := le_of_lt (neg_pos.mpr hn),
    obtain ⟨A, hA⟩ := int.eq_coe_of_zero_le h5,
    have h3: ((neg_one: zmod 7) * (A: zmod 7)).val = ((neg_one : zmod 7).val * (A: zmod 7).val) % 7 :=
        zmod.val_mul _ _,
    have h6: (A : zmod 7) = ((A : ℤ) : zmod 7) := by norm_cast,
    have h7: (-1 : zmod 7).val = 6 := by ring,
    have h8 : ((6 : ℕ) : ℤ) = (-1 : ℤ) % 7 := by norm_cast,
    have h9 : (((-1 : ℤ) % 7) * (↑A % 7)) % 7 = ((-1 : ℤ) * (↑A)) % 7 := (int.mul_mod _ _ 7).symm,
    rw [hnn,h2,hA,←h6,h3],
    simp [zmod.val_nat_cast, h7, h8, h9] },
end

theorem india1998_q1b (n a b: ℤ) (hn : a^2 + 3 * b^2 = 7 * n) :
  (∃ a b : ℤ, a^2 + 3 * b^2 = n) :=
begin
  let az : zmod 7 := a,
  let bz : zmod 7 := b,

  have h1 : (((a^2 + 3 * b^2) : ℤ) : zmod 7) = (((7 * n) : ℤ) : zmod 7) := congr_arg coe hn,
  have h2 : (((a^2 + 3 * b^2) : ℤ) : zmod 7) = ((a^2 : ℤ) : zmod 7) + (((3 * b^2) : ℤ) : zmod 7) :=
    int.cast_add _ _,
  have h3 : ((a^2 : ℤ) : zmod 7) = az^2 := int.cast_pow a 2,
  have h4 : (((3 * b^2) : ℤ) : zmod 7) = ((3:ℤ):zmod 7) * (((b^2) : ℤ) : zmod 7) := int.cast_mul 3 (b ^ 2),
  have h5 : ((b^2 : ℤ) : zmod 7) = bz^2 := int.cast_pow b 2,
  have h6 : ((3:ℤ):zmod 7) = (3 : zmod 7) := rfl,
  have h7' : ((7 : ℤ) : zmod 7) = 0 := rfl,
  have h7 : (((7 * n) : ℤ) : zmod 7) = 0 := by {rw [int.cast_mul, h7'], exact zero_mul _},
  rw [h2,h3,h4,h5,h6,h7] at h1,
  clear h2 h3 h4 h5 h6 h7,

  have h8: (3:zmod 7) = -4 := by ring,
  rw [h8] at h1,

  have h9: az ^ 2 + (-4) * bz ^ 2 + 4 * bz^2 = 0 + 4 * bz^2 := congr_fun (congr_arg has_add.add h1) _,
  rw [neg_mul_eq_neg_mul_symm, neg_add_cancel_right, fin.zero_add] at h9,

  have h10 : 4 * bz^2 = (2 * bz) ^ 2 := by ring,
  rw [h10] at h9,
  haveI : fact (nat.prime 7) := ⟨by norm_num⟩,

  obtain (hep : az = 2 * bz) | (hen : az = - (2 * bz)) := eq_or_eq_neg_of_sq_eq_sq _ _ h9,
  { have h11: (2 * az + 3 * bz) = 0,
    { rw [hep], ring_nf,
      have h12: (7 : zmod 7) = 0 := rfl,
      rw [h12],
      simp },
    have h13: 7 ∣ (2 * a + 3 * b),
    { have h50 : (2 * az + 3 * bz).val = (0 : zmod 7).val := congr_arg zmod.val h11,
      have h51 : (2 * az + 3 * bz).val = ((2 * az).val + (3 * bz).val) % 7 := zmod.val_add _ _,
      have h52 : (2 * az).val = (2 : zmod 7).val * az.val % 7 := zmod.val_mul _ _,
      have h53 : (3 * bz).val = (3 : zmod 7).val * bz.val % 7 := zmod.val_mul _ _,
      rw [h51, h52, h53] at h50,
      simp at h50,
      have h51 : (2 * az.val + 3 * bz.val) % 7 = 0 := h50,
      have h52 : ((2 * (az.val:ℤ) + 3 * (bz.val:ℤ))) % 7 = 0,
      { norm_cast,
        exact h51},
      rw [lemma1 a, lemma1 b] at h52,
      simp at h52,
      rw [←int.mod_add_div a 7, ←int.mod_add_div b 7],
      have h53 : 2 * (a % 7 + 7 * (a / 7)) + 3 * (b % 7 + 7 * (b / 7)) =
              2 * (a % 7) + 3 * (b % 7) + 7 * (2 * (a / 7) + 3 * (b / 7)) := by ring,
      rw [h53],
      have h54 : 7 ∣ 7 * (2 * (a / 7) + 3 * (b / 7)) := dvd.intro _ rfl,
      exact dvd_add h52 h54 },
    have h14 : (∃ m1, 2 * a + 3 * b = 7 * m1) := exists_eq_mul_right_of_dvd h13,
    obtain ⟨m1, hm1⟩ := h14,

    have h15: (az + (- 2) * bz) = 0,
    { rw [hep], ring_nf, simp },
    have h16: 7 ∣ (a + (-2) * b),
    { have h50 : (az + (-2) * bz).val = (0 : zmod 7).val := congr_arg zmod.val h15,
      have h51 : (az + (-2) * bz).val = (az.val + ((-2) * bz).val) % 7 := zmod.val_add _ _,
      have h53 : ((-2) * bz).val = (-2 : zmod 7).val * bz.val % 7 := zmod.val_mul _ _,
      rw [h51, h53] at h50,
      simp at h50,
      have h51 : (az.val + 5 * bz.val) % 7 = 0 := h50,
      have h52 : (((az.val:ℤ) + 5 * (bz.val:ℤ))) % 7 = 0,
      { norm_cast,
        exact h51},
      rw [lemma1 a, lemma1 b] at h52,

      have h52' : 7 ∣ a % 7 + 5 * (b % 7) := int.dvd_of_mod_eq_zero h52,
      rw [←int.mod_add_div a 7, ←int.mod_add_div b 7],
      have h53 : a % 7 + 7 * (a / 7) + (-2) * (b % 7 + 7 * (b / 7)) =
              a % 7 + 5 * (b % 7) + 7 * (a / 7 - 2 * (b / 7) - (b % 7)) := by ring,
      rw [h53],
      have h54 : 7 ∣ 7 * (a / 7 - 2 * (b / 7) - (b % 7)) := dvd.intro _ rfl,
      exact dvd_add h52' h54 },
    have h17 : (∃ m2, a + (-2) * b = 7 * m2) := exists_eq_mul_right_of_dvd h16,
    obtain ⟨m2, hm2⟩ := h17,

    use m1,
    use m2,
    have h20 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * n,
    { rw [←hm1, ←hm2],
      ring_nf,
      have h21 : (2 * a + 3 * b) ^ 2 + 3 * (a - 2 * b) ^ 2 = 7 * (a ^2 + 3 * b^2) := by ring,
      have h18: 7 * (a ^ 2 + 3 * b ^ 2) = 7 * (7 * n) := congr_arg (has_mul.mul 7) hn,
      rw [h21, h18],
      ring },

    have h21 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * (m1 ^ 2 + 3 * m2 ^ 2) := by ring,

    rw[h21] at h20,
    have h22 : (7:ℤ) * 7 ≠ 0 := by norm_num,
    exact (mul_right_inj' h22).mp h20 },

  { have h11: (2 * az + (-3) * bz) = 0,
    { rw [hen], ring_nf,
      simp, ring_nf,
      have h12: (7 : zmod 7) = 0 := rfl,
      rw [h12], simp},

    have h13: 7 ∣ (2 * a + (-3) * b),
    { have h50 : (2 * az + (-3) * bz).val = (0 : zmod 7).val := congr_arg zmod.val h11,
      have h51 : (2 * az + (-3) * bz).val = ((2 * az).val + ((-3) * bz).val) % 7 := zmod.val_add _ _,
      have h52 : (2 * az).val = (2 : zmod 7).val * az.val % 7 := zmod.val_mul _ _,
      have h53 : ((-3) * bz).val = (-3 : zmod 7).val * bz.val % 7 := zmod.val_mul _ _,
      rw [h51, h52, h53] at h50,
      simp at h50,
      have h51 : (2 * az.val + 4 * bz.val) % 7 = 0 := h50,
      have h52 : ((2 * (az.val:ℤ) + 4 * (bz.val:ℤ))) % 7 = 0,
      { norm_cast,
        exact h51},
      rw [lemma1 a, lemma1 b] at h52,
      simp at h52,
      rw [←int.mod_add_div a 7, ←int.mod_add_div b 7],
      have h53 : 2 * (a % 7 + 7 * (a / 7)) + (-3) * (b % 7 + 7 * (b / 7)) =
               2 * (a % 7) + 4 * (b % 7) + 7 * (2 * (a / 7) + (-3) * (b / 7) - (b % 7) ) := by ring,
      rw [h53],
      have h54 : 7 ∣ 7 * (2 * (a / 7) + (-3) * (b / 7) - b % 7) := dvd.intro _ rfl,
      exact dvd_add h52 h54 },

    have h14 : (∃ m1, 2 * a + (-3) * b = 7 * m1) := exists_eq_mul_right_of_dvd h13,
    obtain ⟨m1, hm1⟩ := h14,

    have h15: (az + 2 * bz) = 0,
    { rw [hen], ring_nf },
    have h16: 7 ∣ (a + 2 * b),
    { have h50 : (az + 2 * bz).val = (0 : zmod 7).val := congr_arg zmod.val h15,
      have h51 : (az + 2 * bz).val = (az.val + (2 * bz).val) % 7 := zmod.val_add _ _,
      have h53 : (2 * bz).val = (2 : zmod 7).val * bz.val % 7 := zmod.val_mul _ _,
      rw [h51, h53] at h50,
      simp at h50,
      have h51 : (az.val + 2 * bz.val) % 7 = 0 := h50,
      have h52 : (((az.val:ℤ) + 2 * (bz.val:ℤ))) % 7 = 0,
      { norm_cast,
        exact h51},
      rw [lemma1 a, lemma1 b] at h52,
      --rw [int.add_mod] at h52,
      have h52' : 7 ∣ a % 7 + 2 * (b % 7) := int.dvd_of_mod_eq_zero h52,
      rw [←int.mod_add_div a 7, ←int.mod_add_div b 7],
      have h53 : a % 7 + 7 * (a / 7) + 2 * (b % 7 + 7 * (b / 7)) =
              a % 7 + 2 * (b % 7) + 7 * (a / 7 + 2 * (b / 7)) := by ring,
      rw [h53],
      have h54 : 7 ∣ 7 * (a / 7 + 2 * (b / 7)) := dvd.intro _ rfl,
      exact dvd_add h52' h54,
    },

    have h17 : (∃ m2, a + 2 * b = 7 * m2) := exists_eq_mul_right_of_dvd h16,
    obtain ⟨m2, hm2⟩ := h17,

    use m1,
    use m2,

    have h20 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * n,
    { rw [←hm1, ←hm2],
      ring_nf,
      have h21 : (2 * a - 3 * b) ^ 2 + 3 * (a + 2 * b) ^ 2 = 7 * (a ^2 + 3 * b^2) := by ring,
      have h18: 7 * (a ^ 2 + 3 * b ^ 2) = 7 * (7 * n) := congr_arg (has_mul.mul 7) hn,
      rw [h21, h18],
      ring },

    have h21 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * (m1 ^ 2 + 3 * m2 ^ 2) := by ring,

    rw[h21] at h20,
    have h22 : (7:ℤ) * 7 ≠ 0 := by norm_num,
    exact (mul_right_inj' h22).mp h20 },
end

