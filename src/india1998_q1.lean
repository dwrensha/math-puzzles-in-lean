import data.int.basic
import data.zmod.basic

import tactic.ring

/-
Indian Mathematical Olympiad 1998, problem 1

(a) Show that the product of two numbers of the form a² + 3b² is again of that form.
(b) If an integer n is such that 7n is of the form a² + 3b², prove that n is also of that form.
-/

theorem india1998_q1a (a1 a2 b1 b2 : ℤ) :
  (∃ a3 b3, (a1^2 + 3 * b1^2) * (a2^2 + 3 * b2^2) = (a3^2 + 3 * b3^2)) :=
begin
  use (a1 * a2 + 3 * b1 * b2),
  use (a1 * b2 - b1 * a2),
  ring,
end

lemma foo (a: ℤ) : ((a : zmod 7).val : ℤ) = a % 7 :=
begin
  have h7 : 7 ≠ 0 := by norm_num,
--  have h8 : (a : zmod 7).val = a % 7,
--  have := zmod.val_nat_cast a,
  sorry,
end

theorem india1998_q1b (n a b: ℤ) (hn : a^2 + 3 * b^2 = 7 * n) :
  (∃ a b : ℤ, a^2 + 3 * b^2 = n) :=
begin
  let az : zmod 7 := a,
  let bz : zmod 7 := b,

  have haz : (az.val : ℤ) = a % 7 := sorry,

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
       sorry, },
    have h14 : (∃ m1, 2 * a + 3 * b = 7 * m1) := exists_eq_mul_right_of_dvd h13,
    obtain ⟨m1, hm1⟩ := h14,

    have h15: (az - 2 * bz) = 0,
    { rw [hep], ring_nf, simp },
    have h16: 7 ∣ (a - 2 * b) := sorry,
    have h17 : (∃ m2, a - 2 * b = 7 * m2) := exists_eq_mul_right_of_dvd h16,
    obtain ⟨m2, hm2⟩ := h17,

    use m1,
    use m2,
    have h20 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * n,
    { rw [←hm1, ←hm2],
      ring_nf,
      have h18: 7 * (a ^ 2 + 3 * b ^ 2) = 7 * (7 * n) := congr_arg (has_mul.mul 7) hn,
      have h19 : 7 * (a ^ 2 + 3 * b ^ 2) = 7 * a^2 + 21 * b^2 := by ring,
      rw [←h19, h18],
      ring },

    have h21 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * (m1 ^ 2 + 3 * m2 ^ 2) := by ring,

    rw[h21] at h20,
    have h22 : (7:ℤ) * 7 ≠ 0 := by norm_num,
    exact (mul_right_inj' h22).mp h20 },
  {sorry},
end

