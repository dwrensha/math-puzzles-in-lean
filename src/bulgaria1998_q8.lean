import algebra.ring.basic
import data.rat.basic
import tactic.ring

/-
Bulgarian Mathematical Olympiad 1998, Problem 8

The polynomials Pₙ(x,y) for n = 1, 2, ... are defined by P₁(x,y) = 1 and

  Pₙ₊₁(x,y) = (x + y - 1)(y + 1)Pₙ(x,y+2) + (y - y²)Pₙ(x,y)

Prove that Pₙ(x,y) = Pₙ(y,x) for all x,y,n.

-/

variables {R : Type} [comm_ring R]

def P : ℕ → R → R → R
| 0 _ _ := 1
| (n+1) x y := (x + y - 1) * (y + 1) * P n x (y + 2) + (y - y^2) * P n x y

/- helper function
   Sₙ₋₁(x,y) = [(x + y)² - 1](y + 1)(x + 1)Pₙ₋₁(y+2, x+2).
-/
def S : ℕ → R → R → R
| n x y := ((x + y)^2 - 1) * (y + 1) * (x + 1) * P n (y + 2) (x + 2)

/- helper function
   Tₙ₋₁(x,y) = (y - y²)(x - x²)Pₙ₋₁(y, x).
-/
def T : ℕ → R → R → R
| n x y := (y - y^2) * (x - x^2) * P n y x

/- helper function
   Uₙ₋₁(x,y) = (x + y - 1) [(y + 1)(x - x²)Pₙ₋₁(y + 2, x)
                           + (x + 1)(y - y²) Pₙ₋₁(y, x + 2)]
-/
def U : ℕ → R → R → R
| n x y := (x + y - 1) *((y + 1)*(x - x^2) * P n (y + 2) x
                           + (x + 1) * (y - y^2) * P n y (x + 2))

theorem bulgaria1998_q8 (n : ℕ) (x y : R) : P n x y = P n y x :=
begin
  -- We induct on n. For n = 1,2 the result is evident.
  -- So we take n > 1 and suppose that the result is true for
  -- Pₙ₋₁(x,y) and Pₙ₋₂(x,y).
  revert x y,
  induction n using nat.strong_induction_on with n ih,
  cases n, { intros, refl },
  cases n,
  { intros, unfold P, ring },
  -- in the informal proof at this point, we're trying to
  -- prove the end result at n+1.
  -- In our formal version, that corresponds to proving the result for
  -- n.succ.succ

  /- We have
     Pₙ₊₁(x,y) = (x + y - 1)(y + 1)Pₙ(x,y+2) + (y - y²)Pₙ(x,y)
               = (x + y - 1)(y + 1)Pₙ(y+2,x) + (y - y²)Pₙ(y,x)
  -/

  have ih1 := ih n.succ (lt_add_one (nat.succ n)),
  have h1 : ∀ x y : R, P n.succ.succ x y =
             (x + y - 1) * (y + 1) * (P n.succ (y + 2) x) +
                 (y - y^2) * (P n.succ y x),
  { intros x y,
    calc P (n.succ.succ) x y
               = (x + y - 1) * (y + 1) * (P n.succ x (y + 2)) +
                   (y - y^2) * (P n.succ x y) : rfl
           ... = (x + y - 1) * (y + 1) * (P n.succ (y + 2) x) +
                   (y - y^2) * (P n.succ y x) : by {rw[ih1 x y,ih1 x (y+2)]} },

  have h2 : ∀ x y : R, (x + y - 1) * (y + 1) * P n.succ (y + 2) x
      = S n x y + (x + y - 1)* (y + 1) * (x - x^2)* P n (y+2) x,
  {intros x y, unfold S P, ring},

  have h_s_symm : ∀ m : ℕ, m < n.succ.succ → ∀ x y : R, S m x y = S m y x,
  { intros m hm x y, unfold S, rw[ih m hm (x + 2) (y + 2)], ring },

  have h4 : ∀ x y : R, (y - y^2) * P n.succ y x =
            (y - y^2) * (x + y -1) * (x + 1) * P n y (x + 2) + T n x y,
  { intros x y, unfold T P, ring },

  have h_t_symm : ∀ m : ℕ, m < n.succ.succ → ∀ x y : R, T m x y = T m y x,
  { intros m hm x y, unfold T, rw[ih m hm x y], ring },

  have h_u_symm : ∀ m : ℕ, m < n.succ.succ → ∀ x y : R, U m x y = U m y x,
  { intros m hm x y, unfold U, rw[ih m hm (y+2) x, ih m hm (x+2) y], ring },

  have h7 : forall x y : R, P n.succ.succ x y = S n x y + T n x y + U n x y,
  { intros x y, rw[h1 x y, h2 x y, h4 x y], unfold U, ring,},

  have h9 : n < n.succ.succ := nat.lt.step (lt_add_one n),

  intros x y,
  calc P n.succ.succ x y = S n x y + T n x y + U n x y : h7 x y
                     ... = S n y x + T n x y + U n x y : by rw[h_s_symm n h9 x y]
                     ... = S n y x + T n y x + U n x y : by rw[h_t_symm n h9 x y]
                     ... = S n y x + T n y x + U n y x : by rw[h_u_symm n h9 x y]
                     ... = P n.succ.succ y x : (h7 y x).symm
end
