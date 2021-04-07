import tactic.norm_num

/-
Bulgarian Mathematical Olympiad 1998, Problem 1

Find the least natural number n (n ≥ 3) with the following property:
for any coloring in 2 colors of n distinct collinear points A_1, A_2, ..., A_n,
there exist three points A_i, A_j, A_{2j - i}, 1 ≤ i < 2j - i ≤ n, which are colored
the same color.

Solution: 9

-/


def coloring_has_desired_points (n: ℕ) (hn: 2 < n) (f: fin n → fin 2) : Prop :=
  ∃ i j : fin n,
  (∃ c : fin 2,
  (i < j ∧ 2 * j.val ≤ n + i.val ∧ f i = c ∧ f j = c ∧ f (⟨2, hn⟩  * j - i) = c))


theorem bulgaria1998_q1a (f: fin 9 → fin 2) : coloring_has_desired_points 9 (by norm_num) f :=
begin
  sorry
end


theorem bulgaria1998_q1b :
  ∃ f: fin 8 → fin 2, (¬ coloring_has_desired_points 8 (by norm_num) f) :=
begin
  sorry
end
