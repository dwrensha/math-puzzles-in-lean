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

def a : ℕ → ℕ
| 0 := 1 -- unused dummy value
| 1 := 1
| (nat.succ n) :=
           have hp : n < n.succ := lt_add_one n,
           have h2 : (n.succ / 2) < n.succ := nat.div_lt_self' n 0,
           a n + a (n.succ / 2)

lemma a_1_is_1 : a 1 = 1 := by simp [a]
lemma a_2_is_2 : a 2 = 2 := by simp [a]

lemma a_5_is_7 : a 5 = 7 :=
begin
  have h3 : a 3 = 3 := by { simp[a], norm_num, rw [a_1_is_1] },
  have h4 : a 4 = 5 := by { simp[a], norm_num, rw [a_1_is_1, a_2_is_2] },
  have h5 : a 5 = 7 := by { simp[a], norm_num, rw [a_1_is_1, a_2_is_2] },
  exact h5
end

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


def a' : ℕ → zmod 7
| n := ⟨(a n) % 7, nat.mod_lt _ (by norm_num)⟩

lemma a'_5_is_0 : a' 5 = 0 :=
begin
  simp [a',a],
  norm_num,
  simp_rw [a_1_is_1, a_2_is_2],
  ring_nf,
end

lemma lemma3
  (N0 : ℕ)
  (k : zmod 7)
  (hk : k ≠ 0)
  (hN : ∀ i : ℕ, i < 7 → a' (N0 + i) = a' N0 + k * i) :
  (∃ i : ℕ, i < 7 ∧ a' (N0 + i) = 0) :=
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

lemma can_get_a_later_one_zmod :
  (∀ N : ℕ, a' N = 0 → (∃ M : ℕ, N < M ∧ a' M = 0)) :=
begin
  intros n hn,

  obtain (hlt : n < 2) | (hlte : 2 ≤ n) := lt_or_ge n 2,
  { use 5,
    split,
    { calc n < 2 : hlt
         ... < 5 : by norm_num },
    {exact a'_5_is_0} },


  
--  let n1 : ℕ := ⟨2 * (n - 1) + 1, nat.succ_pos _⟩,


/-


  -- a (2 * n - 1), a (2 * n), and a (2 * n + 1) are all equivalent mod 7.



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

lemma can_get_a_later_one :
  (∀ N : ℕ, 7 ∣ a N → (∃ M : ℕ, N < M ∧ 7 ∣ a M)) :=
begin
  intros n hn,
  have ha' : a' n = 0,
  { have : a' n = ⟨a n % 7, nat.mod_lt _ (by norm_num)⟩ := by simp[a'],
    rw [this],
    congr,
    exact nat.mod_eq_zero_of_dvd hn, },
  obtain ⟨m, hmgt, hm7⟩ := can_get_a_later_one_zmod n ha',
  use m,
  use hmgt,
  unfold a' at hm7,
  have : a m % 7 = 0,
  { injections_and_clear,
    assumption, },
  exact nat.dvd_of_mod_eq_zero this
end

lemma strengthen
  {P : ℕ → Prop}
  (h : ∀ N : ℕ, P N → (∃ M : ℕ, N < M ∧ P M))
  (he : ∃ N : ℕ, P N) :
  (∀ N : ℕ, ∃ M : ℕ, N < M ∧ P M) :=
begin
  obtain ⟨N0, hn0⟩ := he,
  intro N,
  refine nat.rec_on N _ _,
  { obtain (hlt : 0 < N0) | (hlte : N0 ≤ 0) := lt_or_ge 0 N0,
    { exact ⟨N0, hlt, hn0⟩},
    { have heq : N0 = 0 := eq_bot_iff.mpr hlte,
      rw [heq] at hn0,
      exact h 0 hn0 } },
  { intros pn hpn,
    obtain ⟨m, hm, hmp⟩ := hpn,
    obtain (hlt : pn + 1 < m) |  (hlte : m ≤ pn + 1) := lt_or_ge (pn + 1) m,
    { exact ⟨m, hlt, hmp⟩ },
    { have heq : m = pn + 1,
      { have h1 : pn < m := hm,
        have h2 : m ≤ pn + 1 := hlte,
        have h3 : m = pn + 1 := by linarith,
        exact h3 },
      rw [heq] at hmp,
      exact h (pn.succ) hmp } }
end

theorem poland1998_q4 : (∀ N : ℕ, ∃ M : ℕ, N < M ∧ 7 ∣ a M) :=
begin
  have he: 7 ∣ a 5 := by rw [a_5_is_7],
  exact strengthen can_get_a_later_one ⟨5, he⟩,
end
