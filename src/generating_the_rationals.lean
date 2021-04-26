import algebra.big_operators.basic
import data.finset.basic
import data.nat.parity
import data.rat.basic
import data.rat.order
import data.set.intervals.basic

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
        solve_by_elim
      },

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

theorem generating_the_rationals
  (S : set ℚ)
  (h0 : (0 : ℚ) ∈ S)
  (h1 : (1 : ℚ) ∈ S)
  (hm : ∀s: finset {q // q ∈ S}, (∑i in s, i.val / finset.card s) ∈ S) :
  set.Icc 0 1 ⊆ S :=
begin
  sorry
end
