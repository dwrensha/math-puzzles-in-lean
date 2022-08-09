import data.finset.basic
import data.nat.basic

import algebra.big_operators

open_locale big_operators

/-!
# IMO 2018 Q3

An anti-Pascal triangle is an equilateral triangular array of numbers such that,
except for the numbers in the bottom row, each number is the absolute value
of the difference of the two numbers immediately below it. For example,
the following array is an anti-Pascal triangle with four rows
which contains every integer from 1 to 10:

                  4
                2   6
              5   7   1
            8   3  10   9

Does there exist an anti-Pascal triangle with 2018 rows which contains every
integer from 1 to 1 + 2 + ... + 2018?

# Solution
No.

-/


structure coords := mk ::
(row : ℕ) (col : ℕ)

def left_child (c : coords) : coords :=
⟨c.row.succ, c.col⟩

lemma left_child_row (c : coords) : (left_child c).row = c.row.succ := rfl
lemma left_child_col (c : coords) : (left_child c).col = c.col := rfl

def right_child (c : coords) : coords :=
⟨c.row.succ, c.col.succ⟩

lemma right_child_row (c : coords) : (right_child c).row = c.row.succ := rfl
lemma right_child_col (c : coords) : (right_child c).col = c.col.succ := rfl

/--
antipascal triangle with n rows
-/
structure antipascal_triangle (n : ℕ) := mk ::
  (v : coords → ℕ)
  (antipascal : ∀ x : coords,
                   x.row.succ < n →
                   x.col ≤ x.row →
                   v x + v (left_child x) = v (right_child x) ∨
                   v x + v (right_child x) = v (left_child x))

/--
  Given an antipascal triangle and a point c in it, construct the subtriangle
  rooted at c.
-/
def subtriangle
   {n : ℕ}
   (t : antipascal_triangle n)
   (c : coords)
   (hcr : c.row < n)
   (hcc : c.col ≤ c.row) : antipascal_triangle (n - c.row) :=
{
  v := (λ x, t.v ⟨x.row + c.row, x.col + c.col⟩),
  antipascal :=
    begin
      intros x hxr hxc,
      have hh : x.row.succ + c.row < n := lt_tsub_iff_right.mp hxr,
      rw [nat.succ_add] at hh,
      have := t.antipascal ⟨x.row + c.row, x.col + c.col⟩ hh (add_le_add hxc hcc),
      cases this with hl hr,
      { left,
        rw[left_child, right_child] at hl,
        rw[left_child, nat.succ_add, right_child, nat.succ_add, nat.succ_add],
        exact hl },
      { right,
        rw[left_child, right_child] at hr,
        rw[left_child, nat.succ_add, right_child, nat.succ_add, nat.succ_add],
        exact hr },
    end
}

structure a_and_b := mk ::
(a : coords) (b : coords)

def a_and_b_seqs {n : ℕ} (t : antipascal_triangle n) : ℕ → a_and_b
| 0 := ⟨⟨0,0⟩, ⟨0,0⟩⟩
| (nat.succ m) :=
  let b := (a_and_b_seqs m).b
  in if t.v b + t.v (left_child b) = t.v (right_child b)
     then ⟨left_child b, right_child b⟩
     else ⟨right_child b, left_child b⟩

lemma a_and_b_invariant {n : ℕ} (t : antipascal_triangle n) (m : ℕ) :
  (let b := (a_and_b_seqs t m).b in
   ((a_and_b_seqs t m.succ) = ⟨left_child b, right_child b⟩ ∧
    (b.row.succ < n → b.col ≤ b.row → t.v b + t.v (left_child b) = t.v (right_child b))) ∨
    ((a_and_b_seqs t m.succ) = ⟨right_child b, left_child b⟩) ∧
     (b.row.succ < n → b.col ≤ b.row → t.v b + t.v (right_child b) = t.v (left_child b))) :=
begin
  cases classical.em (t.v (a_and_b_seqs t m).b +
                     t.v (left_child (a_and_b_seqs t m).b) =
                     t.v (right_child (a_and_b_seqs t m).b)) with hl hr,
  { simp only [a_and_b_seqs, left_child, right_child],
    finish },
  { simp only [a_and_b_seqs, left_child, right_child, hr],
    right,
    split,
    { finish },
    { intros h1 h2,
      have := t.antipascal (a_and_b_seqs t m).b h1 h2,
      finish },
  },
end

lemma a_and_b_row_is_m {n : ℕ} (t : antipascal_triangle n) (m : ℕ) :
    (a_and_b_seqs t m).a.row = m ∧ (a_and_b_seqs t m).b.row = m :=
begin
  induction m with m' ih,
  { simp[a_and_b_seqs] },
  cases ih with ih1 ih2,
  cases a_and_b_invariant t m' with hl hr,
  { simp[hl,left_child, right_child, ih2] },
  { simp[hr,left_child, right_child, ih2] }
end

lemma a_and_b_within_triangle {n : ℕ} (t : antipascal_triangle n) (m : ℕ) (hm : m < n) :
  (a_and_b_seqs t m).a.col ≤ (a_and_b_seqs t m).a.row ∧
  (a_and_b_seqs t m).b.col ≤ (a_and_b_seqs t m).b.row :=
begin
  induction m with m' ih,
  { simp[a_and_b_seqs] },
  { obtain ⟨iha,ihb⟩ := ih (nat.lt_of_succ_lt hm),
    cases (a_and_b_invariant t m') with hl hr,
    { rw[hl.1],
      rw[left_child_col, left_child_row, right_child_col, right_child_row],
      split,
      { exact nat.le_succ_of_le ihb },
      { exact nat.succ_le_succ ihb } },
    { rw[hr.1],
      rw[left_child_col, left_child_row, right_child_col, right_child_row],
      split,
      { exact nat.succ_le_succ ihb },
      { exact nat.le_succ_of_le ihb }} }
end

lemma sum_of_a {n : ℕ} (t : antipascal_triangle n) (m : ℕ) (hm : m < n) :
  (∑i in finset.range m.succ, t.v (a_and_b_seqs t i).a) = t.v (a_and_b_seqs t m).b :=
begin
  induction m with m' ih,
  { simp only [nat.nat_zero_eq_zero, finset.sum_singleton, finset.range_one, a_and_b_seqs] },
  rw [finset.sum_range_succ, ih (nat.lt_of_succ_lt hm)],
  obtain ⟨hra, hrb⟩ := a_and_b_row_is_m t m',
  obtain ⟨haw, hbw⟩ := a_and_b_within_triangle t m' (nat.lt_of_succ_lt hm),
  cases a_and_b_invariant t m' with hl hr,
  { finish },
  { finish },
end

theorem imo2018_q3 (t : antipascal_triangle 2018)
  (h_contains_all : ∀ n ≤ (∑(i:ℕ) in finset.range 2018, i + 1),
    ∃ r < 2018, ∃ c ≤ r, t.v ⟨r,c⟩ = n) :
  false :=
begin
sorry
end
