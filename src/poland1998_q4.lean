import data.nat.basic
import data.nat.modeq
import data.zmod.basic
import data.int.basic


import tactic.linarith
import tactic.field_simp
import tactic.norm_num
import tactic.interval_cases

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

lemma a_recurrence (n : ℕ) (hn : 2 ≤ n) :
  a n = a (n - 1) + a (n / 2) :=
begin
  cases n,
  { linarith },
  cases n,
  { linarith },
  simp [a],
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

lemma a'_recurrence (n : ℕ) (hn : 2 ≤ n) :
  a' n = a' (n - 1) + a' (n / 2) :=
begin
  ext,
  have : (a' n).val = (a' (n - 1) + a' (n / 2)).val,
  { rw [zmod.val_add],
    simp_rw [a', a_recurrence n hn],
    rw [zmod.val],
    simp },
  exact this,
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

lemma lemma6 (n : ℕ) : (4 * (n - 1) + 1 + 3) / 2 = (2 * (n - 1) + 1 + 1) :=
begin
  have : (4 * (n - 1) + 1 + 3) = 2 * (2 * (n - 1) + 1 + 1) := by linarith,
  finish
end

lemma lemma6' (n : ℕ) : (4 * (n - 1) + 1 + 4) / 2 = (2 * (n - 1) + 1 + 1) :=
begin
  have h1 : (4 * (n - 1) + 1 + 4) = 2 * (2 * (n - 1) + 1 + 1) + 1 := by linarith,
  rw [h1],
  exact lemma2 (2 * (n - 1) + 1 + 1),
end

lemma lemma7 (n : ℕ) : (4 * (n - 1) + 1 + 5) / 2 = (2 * (n - 1) + 1 + 2) :=
begin
  have : (4 * (n - 1) + 1 + 5) = 2 * (2 * (n - 1) + 1 + 2) := by linarith,
  finish
end

lemma lemma7' (n : ℕ) : (4 * (n - 1) + 1 + 6) / 2 = (2 * (n - 1) + 1 + 2) :=
begin
  have h1 : (4 * (n - 1) + 1 + 6) = 2 * (2 * (n - 1) + 1 + 2) + 1 := by linarith,
  rw [h1],
  exact lemma2 (2 * (n - 1) + 1 + 2),
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

  let n1 : ℕ := 2 * (n - 1) + 1,

  -- a' (2 * n - 1), a' (2 * n), and a' (2 * n + 1) are all equal

  have npos := calc 0 < 2 : by norm_num
                  ... ≤ n : hlte,
  have hn1v : n1 = 2 * n - 1 := lemma1 n npos,
  have hn2: 2 ≤ n1 + 1,
  { have : 1 ≤ n1 := le_add_self,
    exact nat.succ_le_succ this },

  have hn3: 2 ≤ n1 + 2 := le_add_self,

  let an1 := a' n1,

  have hn1 : (n1 + 1) = 2 * n,
  { have hrw : (n1 + 1) = 2 * (n - 1) + 1 + 1 := rfl,
    rw [hrw],
    cases n,
    { exfalso, exact lt_asymm npos npos },
    { refl } },

  have ha1 : a' (n1 + 1) = an1 + a' n,
  { have haa : a' (n1 + 1) = a' n1 + a' (n1.succ / 2) := a'_recurrence (n1 + 1) hn2,
    have h2n1 : 2 * n / 2 = n := by norm_num,
    have h2n1' : (n1 + 1) / 2 = n := by { rw [hn1, h2n1] },
    rw [haa, h2n1'] },

  have hn1' : n1 + 2 = 2 * n + 1,
  { have hrw : (n1 + 2) = 2 * (n - 1) + 1 + 1 + 1 := rfl,
    rw [hrw],
    cases n,
    { exfalso, exact lt_asymm npos npos },
    { refl } },

  have ha2 : a' (n1 + 2) = a' (n1 + 1) +  a' n,
  { have haa : a' (n1 + 2) = a' (n1 + 1) + a' (n1.succ.succ / 2) := a'_recurrence (n1 + 2) hn3,
    have h1 : (2 * n + 1) / 2 = n := lemma2 n,
    have hn1v' : 2 * n = n1 + 1,
    { have hrw : n1 + 1 = 2 * (n - 1) + 1 + 1 := rfl,
      rw [hrw],
      cases n,
      { exfalso, exact lt_asymm npos npos },
      { refl } },
    rw [haa],
    congr,
    have : n1.succ.succ = (n1 + 1 + 1) := rfl,
    rw this,
    rw [← hn1v', h1] },

  have ha1' : a' (n1 + 1) = a' n1,
  { rw [hn] at ha1,
    simp at ha1,
    exact ha1 },

  have ha2' : a' (n1 + 2) = a' n1,
  { rw [hn, ha1'] at ha2,
    simp at ha2,
    exact ha2 },

  clear ha1 ha2,

  have : ∀ i, i ≤ 2 → a' (n1 + i) = a' n1,
  { intros i hi,
    interval_cases i,
    { exact ha1' },
    { exact ha2' } },

  -- then the seven elements beginning with a (4 * n - 3) will all have different
  -- residues mod 7.

/-

  let n4 := 4 * n - 3,
  -- a (n4 + 1) = a n4 + a n1
  -- a (n4 + 2) = a (n4 + 1) + a n1
  -- a (n4 + 3) = a (n4 + 2) + a (n1 + 1)
  -- a (n4 + 4) = a (n4 + 3) + a (n1 + 1)
  -- a (n4 + 5) = a (n4 + 4) + a (n1 + 2)
  -- a (n4 + 6) = a (n4 + 5) + a (n1 + 2)

-/

  -- n2 = 4 * n - 3
  --   = 4 * (n - 1) + 1
  let n2: ℕ := 4 * (n - 1) + 1,

  have hii : ∀ i, i < 6 → a' (n2 + i + 1) = a' (n2 + i) + a' n1,
  { intros i hi,
    have hn2ge2 : 2 ≤ n2 + i + 1 := by linarith,
    have hr := a'_recurrence (n2 + i + 1) hn2ge2,
    interval_cases i,
    { suffices : (n2 + 1) / 2 = n1, by { rwa [this] at hr },
      have : (4 * (n - 1) + 1 + 1) = 2 * (2 * (n - 1) + 1) := by ring,
      simp only [this, nat.succ_pos', nat.mul_div_right], },
    { suffices hn1 : (n2 + 2) / 2 = n1, by { rwa [hn1] at hr },
      have h1 : (4 * (n - 1) + 1 + 2) = 2 * (2 * (n - 1) + 1) + 1 := by ring,
      rw [h1],
      exact lemma2 (2 * (n - 1) + 1)},
    { have hn1 : (n2 + 3) / 2 = n1 + 1 := lemma6 n,
      rw [hn1, ha1'] at hr,
      exact hr},
    { have hn1 : (n2 + 4) / 2 = n1 + 1 := lemma6' n,
      rw [hn1, ha1'] at hr,
      exact hr},
    { have hn1 : (n2 + 5) / 2 = n1 + 2 := lemma7 n,
      rw [hn1, ha2'] at hr,
      exact hr},
    { have hn1 : (n2 + 6) / 2 = n1 + 2 := lemma7' n,
      rw [hn1, ha2'] at hr,
      exact hr} },

  have hik : ∀ i, i < 7 → a' (n2 + i) = a' n2 + a' n1 * i,
  { intros i,
    induction i with p hp,
    { intro, simp, },
    { intro hpi7,
      have hpi6 : p < 6 := nat.succ_lt_succ_iff.mp hpi7,
      have hinc := hii p hpi6,
      have hadd : n2 + p + 1 = n2 + p.succ := rfl,
      have hi6 : p < 7 := nat.lt.step hpi6,
      have hpp := hp hi6,
      have hp1: (p.succ : zmod 7) = (p : zmod 7) + 1 := by norm_cast,
      rw [←hadd, hinc, hpp, hp1],
      ring_nf} },

  obtain (haez : a' n1 = 0) | (hanez : ¬ a' n1 = 0) := em (a' n1 = 0),
  { use n1,
    split,
    { linarith },
    { exact haez }},

  { have := lemma3 n2 (a' n1) hanez hik,
    obtain ⟨ii, hii7, hia'⟩ := this,
    use (n2 + ii),
    split,
    { linarith },
    { assumption } }
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
