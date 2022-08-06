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

def right_child (c : coords) : coords :=
⟨c.row.succ, c.col.succ⟩

lemma right_child_row (c : coords) : (right_child c).row = c.row.succ := rfl

/--
antipascal triangle with n rows
-/
structure antipascal_triangle (n : ℕ) := mk ::
(f : coords → ℕ)
(antipascal : ∀ x: coords, x.row.succ < n → x.col ≤ x.row →
  f x + f (left_child x) = f (right_child x) ∨
  f x + f (right_child x) = f (left_child x))

structure a_and_b := mk ::
(a : coords) (b : coords)

def a_and_b_seqs {n : ℕ} (t : antipascal_triangle n) : ℕ → a_and_b
| 0 := ⟨⟨0,0⟩, ⟨0,0⟩⟩
| (nat.succ m) :=
  let b := (a_and_b_seqs m).b
  in if hm : m.succ < n
     then if t.f b + t.f (left_child b) = t.f (right_child b)
          then ⟨left_child b, right_child b⟩
          else ⟨right_child b, left_child b⟩
     else ⟨left_child b, right_child b⟩ -- outside relevant region, can choose anything


lemma a_and_b_row_is_m {n : ℕ} (t : antipascal_triangle n) (m : ℕ) :
    (a_and_b_seqs t m).a.row = m ∧ (a_and_b_seqs t m).b.row = m :=
begin
  induction m with m' ih,
  { simp[a_and_b_seqs] },
  cases ih with ih1 ih2,
  cases classical.em (m'.succ<n) with hm' hmnot',
  { simp[a_and_b_seqs, hm'],
    cases classical.em (t.f (a_and_b_seqs t m').b +
              t.f (left_child (a_and_b_seqs t m').b) =
                 t.f (right_child (a_and_b_seqs t m').b)) with hc hcnot,
    { simp[hc],
      split,
      {nth_rewrite 1 [← ih2], refl},
      {nth_rewrite 1 [← ih2], refl},
    },
    { simp[hcnot],
      split,
      {nth_rewrite 1 [← ih2], refl},
      {nth_rewrite 1 [← ih2], refl}},
  },
  { have hp : a_and_b_seqs t m'.succ =
          ⟨left_child (a_and_b_seqs t m').b, right_child (a_and_b_seqs t m').b⟩,
    { simp[a_and_b_seqs, hmnot']},
    rw[hp],
    dsimp,
    split,
    { nth_rewrite 1 [← ih2], refl},
    { nth_rewrite 1 [← ih2], refl},
  },
end

lemma b_within_triangle {n : ℕ} (t : antipascal_triangle n) (m : ℕ) (hm : m < n) :
  (a_and_b_seqs t m).b.col ≤ (a_and_b_seqs t m).b.row :=
begin
  induction m with pm hpm,
  { unfold a_and_b_seqs },
  unfold a_and_b_seqs,
  have h' := hpm (nat.lt_of_succ_lt hm),
  have := t.antipascal (a_and_b_seqs t pm).b _ h',
  sorry,
  sorry,
end

lemma sum_of_a {n : ℕ} (t : antipascal_triangle n) (m : ℕ) (hm : m < n) :
  (∑(i:ℕ) in finset.range m.succ, t.f (a_and_b_seqs t i).a) = t.f (a_and_b_seqs t m).b :=
begin
  induction m with pm hpm,
  { simp only [nat.nat_zero_eq_zero, finset.sum_singleton, finset.range_one],
    unfold a_and_b_seqs,
  },
  rw [finset.sum_range_succ, hpm (nat.lt_of_succ_lt hm)],
  have := b_within_triangle t pm (nat.lt_of_succ_lt hm),
--  t.antipascal
  sorry
end

theorem imo2018_q3 (t : antipascal_triangle 2018)
  (h_contains_all : ∀ n ≤ (∑(i:ℕ) in finset.range 2018, i + 1),
    ∃ r < 2018, ∃ c < r, t.f ⟨r,c⟩ = n) :
  false :=
begin
sorry
end
