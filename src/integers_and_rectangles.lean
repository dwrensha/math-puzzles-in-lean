import data.real.basic

/-
 A large rectangle in the plane is partitioned into smaller rectangles, each of which has either integer
height or integer width (or both). Prove that the large rectangle also has this property.
-/

structure point := mk ::
(x : ℝ) (y : ℝ)

structure rect := mk ::
(bottom_left : point)
(top_right : point)
(positive_width : 0 < top_right.x - bottom_left.x)
(positive_height : 0 < top_right.y - bottom_left.y)

def rect_width (r : rect) : ℝ := r.top_right.x - r.bottom_left.x
def rect_height (r : rect) : ℝ := r.top_right.y - r.bottom_left.y

def rect_contains_point (r : rect) (p : point) : Prop :=
  r.bottom_left.x ≤ p.x ∧ p.x < r.top_right.x ∧
  r.bottom_left.y ≤ p.y ∧ p.y < r.top_right.y

def rects_intersect (r1 : rect) (r2 : rect) : Prop :=
  ∃ p : point, rect_contains_point r1 p ∧ rect_contains_point r2 p

theorem integers_and_rectangles
  (big_rect : rect)
  (n : ℕ)
  (small_rects : fin n → rect)
  (h_cover : ∀ p : point, rect_contains_point big_rect p →
             ∃ m : fin n, rect_contains_point (small_rects m) p)
  (h_no_overlap : ∀ m1 m2 : fin n, m1 ≠ m2 →
                  ¬ rects_intersect (small_rects m1) (small_rects m2))
  (h_integer_sides : ∀ m : fin n,
                     ∃ k : ℕ, rect_width (small_rects m) = k ∨
                              rect_height (small_rects m) = k) :
  ∃k : ℕ, rect_width big_rect = k ∨ rect_height big_rect = k :=
begin
  sorry
end
