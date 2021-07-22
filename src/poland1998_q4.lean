import data.nat.basic
import data.nat.modeq
import data.zmod.basic
import data.int.basic


import tactic.linarith
import tactic.omega
import tactic.norm_num

/-
Polish Mathematical Olympiad 1998, Problem 4

Prove that the sequence {a_n} defined by a_1 = 1 and

     a_n = a_{n - 1} + a_{⌊n/2⌋}        n = 2,3,4,...

contains infinitely many integers divisible by 7.

-/

lemma lemma1 (n : ℕ) (npos : 0 < n) : 2 * (n - 1) + 1 = 2 * n - 1 :=
begin
  cases n,
  { exfalso, exact lt_asymm npos npos },
  { finish, },
end

lemma lemma2 (n : ℕ) : (2 * n + 1) / 2 = n :=
begin
  have h1 : ¬ 2 ∣ 2 * n + 1,
  { intro h,
    have h1: 2 ∣ 2 * n := dvd.intro n rfl,
    have : 2 ∣ 1 := (nat.dvd_add_right h1).mp h,
    rw nat.dvd_one at this,
    exact nat.succ_succ_ne_one 0 this },
  have h2 := nat.succ_div_of_not_dvd h1,
  rw [h2],
  exact nat.mul_div_right n zero_lt_two,
end

lemma lemma3
  (a' : ℕ+ → zmod 7)
  (N0 : ℕ+)
  (k : zmod 7)
  (hk : k ≠ 0)
  (hN : ∀ i : ℕ, i < 7 → a' ⟨N0.val + i, nat.add_pos_left N0.pos i⟩ = a' N0 + k * i) :
  (∃ i : ℕ, i < 7 ∧ a' ⟨N0.val + i, nat.add_pos_left N0.pos i⟩ = 0) :=
begin
  haveI hp : fact (nat.prime 7) := ⟨by norm_num⟩,
  let ii := - (a' N0) / k,
  use ii.val,
  split,
  { exact zmod.val_lt ii },
  { have := hN ii.val (zmod.val_lt ii),
    rw [this],
    field_simp,
    ring },
end

lemma can_get_a_later_one_zmod
  (a' : ℕ+ → zmod 7)
  (h1 : a' 1 = 1)
  (ha : ∀ (n : ℕ+) (h2: 2 ≤ n),
         a' n = a' ⟨n.val - 1, nat.lt_pred_iff.mpr h2⟩ +
               a' ⟨n.val / 2, nat.div_pos h2 zero_lt_two⟩) :
  (∀ N : ℕ+, a' N = 0 → (∃ M : ℕ+, N < M ∧ a' M = 0)) :=
begin
/-
  intros n hn,

  -- a (2 * n - 1), a (2 * n), and a (2 * n + 1) are all equivalent mod 7.

  let n1 : ℕ+ := ⟨2 * (n.val - 1) + 1, nat.succ_pos _⟩,

  have hn1v : n1.val = 2 * n.val - 1 := lemma1 n.val n.pos,
  have hn2: 2 ≤ (n1:ℕ) + 1 := add_le_add_right (pnat.pos n1) 1,
  have hn3: 2 ≤ (n1:ℕ) + 2 := le_add_self,

  let an1 := a n1,
  let := a (n1 + 1),

  have hn1 : (n1 + 1).val = 2 * n.val,
  { have hnpos : 0 < n.val := n.pos,
    have hrw : (n1 + 1).val = 2 * (n.val - 1) + 1 + 1 := rfl,
    rw [hrw],
    cases n.val,
    { exfalso, exact lt_asymm hnpos hnpos },
    { refl } },

  have ha1 : a (n1 + 1) = an1 + a n,
  { have haa := ha (n1 + 1) hn2,
    have h2n1 : 2 * n.val / 2 = n.val := by norm_num,
    have h2n1' : ((n1 + 1).val : ℕ ) / 2 = n.val := by { rw [hn1, h2n1] },
    simp_rw [haa, h2n1', hn1, ← hn1v],
    congr,
    { simp only [subtype.coe_eta, subtype.val_eq_coe] } },

  have hn1' : (n1 + 2).val = 2 * n.val + 1,
  { have hnpos : 0 < n.val := n.pos,
    have hrw : (n1 + 2).val = 2 * (n.val - 1) + 1 + 1 + 1 := rfl,
    rw [hrw],
    cases n.val,
    { exfalso, exact lt_asymm hnpos hnpos },
    { refl } },

  have ha2 : a (n1 + 2) = a (n1 + 1) +  a n,
  { have haa := ha (n1 + 2) hn3,
    have h1 : (2 * n.val + 1) / 2 = n.val := lemma2 n.val,
    have hn1v' : 2 * n.val + 1 - 1 = n1.val + 1,
    { have hrw : n1.val + 1 = 2 * (n.val - 1) + 1 + 1 := rfl,
      rw [hrw],
      have hnpos : 0 < n.val := n.pos,
      cases n.val,
      { exfalso, exact lt_asymm hnpos hnpos },
      { refl } },
    simp_rw [haa, hn1', h1],
    congr,
    { rw hn1v', simp },
    { ext, simp } },

  -- then the seven elements beginning with a (4 * n - 3) will all have different
  -- residues mod 7.

  let n4 := 4 * n - 3,
  -- a (n4 + 1) = a n4 + a n1
  -- a (n4 + 2) = a (n4 + 1) + a n1
  -- a (n4 + 3) = a (n4 + 2) + a (n1 + 1)
  -- a (n4 + 4) = a (n4 + 3) + a (n1 + 1)
  -- a (n4 + 5) = a (n4 + 4) + a (n1 + 2)
  -- a (n4 + 6) = a (n4 + 5) + a (n1 + 2)

-/
  sorry
end

def aa : ℕ → ℤ
| 0 := 1 -- unused dummy value
| 1 := 1
| (nat.succ n) :=
           have hp : n < n.succ, from lt_add_one n,
           have h2 : (n.succ / 2) < n.succ, from nat.div_lt_self' n 0,
           aa n + aa (n.succ / 2)


lemma can_get_a_later_one
  (a : ℕ+ → ℤ)
  (h1 : a 1 = 1)
  (ha : ∀ (n : ℕ+) (h2: 2 ≤ n),
         a n = a ⟨n.val - 1, nat.lt_pred_iff.mpr h2⟩ +
               a ⟨n.val / 2, nat.div_pos h2 zero_lt_two⟩) :
  (∀ N : ℕ+, 7 ∣ a N → (∃ M : ℕ+, N < M ∧ 7 ∣ a M)) :=
begin

  sorry
end

lemma strengthen
  {P : ℕ+ → Prop}
  (h : ∀ N : ℕ+, P N → (∃ M : ℕ+, N < M ∧ P M))
  (he : ∃ N : ℕ+, P N) :
  (∀ N : ℕ+, ∃ M : ℕ+, N < M ∧ P M) :=
begin
  obtain ⟨N0, hn0⟩ := he,
  intro N,
  refine pnat.rec_on N _ _,
  { obtain (hlt : 1 < N0) |  (hlte : N0 ≤ 1) := lt_or_ge 1 N0,
    { exact ⟨N0, hlt, hn0⟩},
    { have heq : N0 = 1 := eq_bot_iff.mpr hlte,
      rw [←heq],
      exact h N0 hn0 } },
  { intros pn hpn,
    obtain ⟨m, hm, hmp⟩ := hpn,
    obtain (hlt : pn + 1 < m) |  (hlte : m ≤ pn + 1) := lt_or_ge (pn + 1) m,
    { exact ⟨m, hlt, hmp⟩ },
    { have heq : m = pn + 1,
      { have h1 : pn.val < m.val := hm,
        have h2 : m.val ≤ pn.val + 1 := hlte,
        have h3 : (m.val:ℕ) = pn.val + 1 := by linarith,
        exact pnat.eq h3 },
      rw ← heq,
      exact h m hmp } }
end

theorem poland1998_q4
  (a : ℕ+ → ℤ)
  (h1 : a 1 = 1)
  (ha : ∀ (n : ℕ+) (h2: 2 ≤ n),
         a n = a ⟨n.val - 1, nat.lt_pred_iff.mpr h2⟩ +
               a ⟨n.val / 2, nat.div_pos h2 zero_lt_two⟩) :
  (∀ N : ℕ+, ∃ M : ℕ+, N < M ∧ 7 ∣ a M) :=
begin
  have h2 : a 2 = 2 := by { have h := ha 2 rfl.le, norm_num at h, rwa [h1] at h },
  have h3 : a 3 = 3 := by { have h := ha 3 (by norm_num), norm_num at h, rwa [h2, h1] at h },
  have h4 : a 4 = 5 := by { have h := ha 4 (by norm_num), norm_num at h, rwa [h3, h2] at h },
  have h5 : a 5 = 7 := by { have h := ha 5 (by norm_num), norm_num at h, rwa [h4, h2] at h },
  have he: 7 ∣ a 5 := by rw [h5],

  have hf := can_get_a_later_one a h1 ha,
  exact strengthen hf ⟨5, he⟩,
end
