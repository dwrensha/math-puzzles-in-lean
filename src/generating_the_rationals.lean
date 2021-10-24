import algebra.order.archimedean
import algebra.big_operators.basic
import data.finset.basic
import data.nat.parity
import data.rat.basic
import data.rat.order
import data.set.intervals.basic
import logic.function.basic

import tactic.field_simp
import tactic.linarith

/-
  A set S contains 0 and 1, and the mean of every finite nonempty subset of S.
  Prove that S contains all of the rational numbers in the unit interval.
-/

open_locale big_operators

lemma contains_dyadics
  (S : set ℚ)
  (h0 : (0 : ℚ) ∈ S)
  (h1 : (1 : ℚ) ∈ S)
  (hm : ∀s: finset {q // q ∈ S}, (∑i in s, i.val / finset.card s) ∈ S)
  (m n : ℕ)
  (hmn : m ≤ 2^n) :
  (m : ℚ) / 2^n ∈ S :=
begin
  revert m,
  induction n with pn hpn,
  { intros m hmn,
    rw pow_zero at hmn,
    cases m,
    { simpa },
    { simpa [nat.le_zero_iff.mp (nat.succ_le_succ_iff.mp hmn)] } },
  {
    intros m hmn,
    obtain ⟨t, ht : m = 2 * t⟩ | ⟨t, ht : m = 2 * t + 1⟩ := m.even_or_odd,
    { -- m is even. reduces to smaller exponent
      rw ht,
      have h2 : ↑(2 * t) / 2 ^ pn.succ = ((t : ℕ) : ℚ) / 2 ^ pn :=
        by {field_simp[pow_succ], ring },
      rw h2,
      have h3 : t ≤ 2 ^ pn := by { rw [ht, pow_succ] at hmn, linarith },
      exact hpn t h3 },
    { -- m is odd. need to take midpoint
      -- m = 2 * t + 1 =  (t  + (t + 1))
      -- so m / 2^pn.succ = (t / 2^pn + (t + 1)/2^pn) / 2
      have h3 : t + 1 ≤ 2 ^ pn := by { rw [ht, pow_succ] at hmn, linarith},
      have h4 : t ≤ 2 ^ pn := nat.le_of_succ_le h3,

      let t1 : ℚ := t / 2^pn,
      let t2 : ℚ := ((t + 1):ℕ)/2^pn,

      have h5 : (m:ℚ) / 2 ^ pn.succ = (t1 + t2) / 2 := by { field_simp[pow_succ, ht], ring },
      rw h5,

      have h6 : t1 ∈ S := hpn t h4,
      have h7 : t2 ∈ S := hpn (t+1) h3,

      let ps' : finset {q // q ∈ S} := {⟨t1, h6⟩},
      let ps : finset {q // q ∈ S} := insert ⟨t2, h7⟩ ps',

      have hnotmem: (⟨t2, h7⟩ : {q // q ∈ S}) ∉ ps',
      { have hne : t2 ≠ t1 := by field_simp,
        have : ps'.card = 1 := finset.card_singleton _,
        simp [this],
        solve_by_elim },

      have hcard : ps.card = 2,
      { have hinsertcard := finset.card_insert_of_not_mem hnotmem,
        rwa [finset.card_singleton] at hinsertcard },

      have hmean := hm ps,
      rw hcard at hmean,
      norm_cast at hmean,

      have hsum2 : ∑ (i : {q // q ∈ S}) in ps, i.val/2 =
                  t2/2 + ∑ (i : {q // q ∈ S}) in ps', i.val/2 := finset.sum_insert hnotmem,

      have hsum1 : ∑ (i : {q // q ∈ S}) in ps', i.val / 2 = t1/2,
      { simp only [finset.sum_singleton, subtype.coe_mk] },

      rw [hsum2, hsum1] at hmean,
      have : t2 / 2 + t1 /2 = (t1 + t2) / 2 := by { field_simp, ring },
      rwa this at hmean,
    },
  },
end

lemma dyadic_sum (q : ℚ) (n k : ℕ) :
  (∑i in finset.range (2 * k), ((q - (2 * k - 1) / 2 ^ n.succ) + i / 2 ^ n)) = 2 * k * q :=
begin
  induction k with pk hpk,
  { simp },
  { have h1 : 2 * pk.succ = (2 * pk).succ.succ := rfl,
    rw [h1, finset.sum_range_succ, finset.sum_range_succ],
    have h2 : ∀ i ∈ finset.range (2 * pk),
      (q - (2 * ↑(pk.succ) - 1) / 2 ^ n.succ + ↑i / 2 ^ n) =
      (q - (2 * ↑pk - 1) / 2 ^ n.succ + ↑i / 2 ^ n - 1 / 2^n),
    { intros i hi,
      have h3: ((2:ℚ) * ↑(pk.succ) - 1) = (2 * ↑pk - 1) + 2,
      { rw [nat.cast_succ], ring, },
      have h4 : ((2:ℚ) * ↑pk - 1 + 2) / 2 ^ n.succ =
                ((2:ℚ) * ↑pk - 1) / 2 ^ n.succ + 2 / 2^n.succ := add_div (2 * ↑pk - 1) 2 (2 ^ nat.succ n),

      have h5 : (2:ℚ) / 2^n.succ = 1 / 2^n,
      { field_simp, exact (pow_succ 2 n).symm },

      rw [h3, h4, h5],
      ring },

    sorry,
  },
end

lemma dyadic_summand_injective (q : ℚ) (n k : ℕ) :
  function.injective (λ i : ℕ, (q - (2 * k - 1) / 2 ^ n.succ) + i / 2 ^ n) :=
begin
  intros i1 i2 h,
  simp only [add_right_inj] at h,
  have h1 : (0:ℚ) < 2^n := pow_pos zero_lt_two _,
  have h2 : 2^n ≠ (0:ℚ) := ne_of_gt h1,
  have h3 : (i1:ℚ)  = ↑i2 / 2 ^ n * 2^n := (div_eq_iff h2).mp h,
  field_simp at h3,
  assumption
end

lemma exists_pow_denom_lt_both (x y z : ℚ) (xpos : 0 < x) (ypos : 0 < y) :
  (∃ n : ℕ, z / 2^n < x ∧ z / 2 ^n < y) :=
begin
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (z / min x y) one_lt_two,
  use n,
  have hm : 0 < min x y := lt_min xpos ypos,
  have h1 : z < 2 ^ n * min x y := (div_lt_iff hm).mp hn,
  have h2 : (0:ℚ) < 2^n := pow_pos zero_lt_two _,
  rw mul_comm at h1,
  have h3 : z / 2 ^ n < min x y := (div_lt_iff h2).mpr h1,
  split,
  { exact gt_of_ge_of_gt (min_le_left x y) h3 },
  { exact gt_of_ge_of_gt (min_le_right x y) h3 },
end

theorem generating_the_rationals
  (S : set ℚ)
  (h0 : (0 : ℚ) ∈ S)
  (h1 : (1 : ℚ) ∈ S)
  (hm : ∀s: finset {q // q ∈ S}, (∑i in s, i.val / finset.card s) ∈ S) :
  set.Icc 0 1 ⊆ S :=
begin
  intros q hq,
  obtain ⟨hq0, hq1⟩ := hq,

  -- First deal with the endpoints.

  obtain (heq0 : 0 = q) | (hgt0 : 0 < q) := or.comm.mp (lt_or_eq_of_le hq0),
  { rwa ←heq0 },
  clear hq0,

  obtain (heq1 : q = 1) | (hlt1 : q < 1) := or.comm.mp (lt_or_eq_of_le hq1),
  { rwa heq1 },
  clear hq1,

  -- Now find dyadics a b such that 0 < a < q < b < 1.

  obtain ⟨na, hna⟩ := pow_unbounded_of_one_lt (1/q) one_lt_two,
  let a : ℚ := 1 / 2^na,
  have ha0 : 0 < a := by norm_num,
  have haq : a < q := (one_div_lt hgt0 (by norm_num)).mp hna,

  obtain ⟨nb, hnb⟩ := pow_unbounded_of_one_lt (1/(1-q)) one_lt_two,
  let b : ℚ := 1 - 1 / 2^nb,
  have hb1 : b < 1 := by norm_num,
  have haq : q < b,
  { have hbb : 0 < (1 - q) := sub_pos.mpr hlt1,
    have hbb': 1 < (1 - q) * 2 ^ nb := (div_lt_iff' hbb).mp hnb,
    rw mul_comm at hbb',
    have := (div_lt_iff' (by norm_num)).mpr hbb',
    exact lt_sub.mp this,
  },

  -- if we could pick an element more than once,
  -- we would choose (q - a).num * (b - q).denom copies of a
  -- and (b - q).num * (q - a).denom copies of b.

  let ka : ℕ := (q - a).num.nat_abs * (b - q).denom,
  let kb : ℕ := (b - q).num.nat_abs * (q - a).denom,

  -- choose Na such that (2 * ka - 1) / 2 ^ n.succ < min ((b - a) / 2) (1 - b)

  have h3 : 0 < 1 - b := by linarith,
  have h4 : 0 < (b - a) / 2 := by linarith,

  obtain ⟨Na, hNa1, hNa2⟩ := exists_pow_denom_lt_both ((b - a) / 2) (1 - b) (2 * (ka:ℚ) - 1) h4 h3,
  obtain ⟨Nb, hNb1, hNb2⟩ := exists_pow_denom_lt_both ((b - a) / 2) (1 - b) (2 * (kb:ℚ) - 1) h4 h3,
  clear h3 h4,

  have h5 := dyadic_sum a Na ka,
  have h6 := dyadic_sum b Nb kb,

  let ta : ℕ ↪ ℚ := ⟨_, dyadic_summand_injective a Na ka⟩,
  let tb : ℕ ↪ ℚ := ⟨_, dyadic_summand_injective b Nb kb⟩,

  have hta := finset.sum_map (finset.range (2 * ka)) ta id,
  have htb := finset.sum_map (finset.range (2 * kb)) tb id,

  dsimp at hta,
  rw ←hta at h5,

  dsimp at htb,
  rw ←htb at h6,

  have h7: disjoint (finset.map ta (finset.range (2 * ka)))
                    (finset.map tb (finset.range (2 * kb))),
  { sorry, },

  let s := (finset.map ta (finset.range (2 * ka))) ∪ (finset.map tb (finset.range (2 * kb))),
  have h8 : s.sum id = (finset.map ta (finset.range (2 * ka))).sum id +
               (finset.map tb (finset.range (2 * kb))).sum id := finset.sum_union h7,
  rw [h5, h6] at h8,

  have h9 : s.card = 2 * ↑ka + 2 * ↑kb := sorry,

  have hra : ∀ r ∈ (finset.map ta (finset.range (2 * ka))), q ∈ S,
  {
     intros r hr,
     -- use contains_dyadics ...
     sorry,
  },

  have hrb : ∀ r ∈ (finset.map tb (finset.range (2 * kb))), q ∈ S,
  {
     intros r hr,
     -- use contains_dyadics ...
     sorry,
  },

  have hrs : ∀ r ∈ s, q ∈ S,
  { intros r hr,
    obtain ha | hb := finset.mem_union.mp hr,
    { exact hra r ha },
    { exact hrb r hb } },

  -- hm... maybe we actually want `ta : ℕ ↪ {q // q ∈ S}`

  sorry
end
