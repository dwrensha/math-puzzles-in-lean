import algebra.ring.basic

/-
Bulgarian Mathematical Olympiad 1998, Problem 8

The polynomials Pₙ(x,y) for n = 1, 2, ... are defined by P₁(x,y) = 1 and

  Pₙ₊₁(x,y) = (x + y - 1)(y + 1)Pₙ(x,y+2) + (y - y²)Pₙ(x,y)

Prove that Pₙ(x,y) = Pₙ(y,x) for all x,y,n.

-/

variables {R : Type} [ring R]

def P : ℕ → R → R → R
| 0 _ _ := 1
| (n+1) x y := (x + y - 1) * (y + 1) * P n x (y + 1) + (y - y^2) * P n x y

theorem bulgaria1998_q8 (n : ℕ) (x y : R) : P n x y = P n y x :=
begin
  sorry
end

