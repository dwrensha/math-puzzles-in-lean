import data.real.basic data.nat.basic

-- first, let's define what it means for a function to be "convex"...

-- f (tx_1 + (1-t)x2) ≤ t f(x1) + (1 - t) f(x2)

def is_convex (f: ℝ → ℝ) : Prop :=
  ∀ t: ℝ, ((0 ≤ t) && (t ≤ 1)) →
    ∀ x1 x2 : ℝ, f (t * x1 + (1 - t) * x2) ≤ t * f x1 + (1 - t) * f x2



def sum_first_n (f: ℕ → ℝ) : ℕ → ℝ
| 0 := f 0
| (nat.succ n) := (f (nat.succ n)) + (sum_first_n n)

def sum_seq { n : ℕ } (f: fin n → ℝ) : ℝ :=
  let f' := λ m : ℕ, if h: m < n then f ⟨m, h⟩ else 0 in
  sum_first_n f' n


def is_weight {n : ℕ} (a : fin n → ℝ) : Prop :=
  (sum_seq a = 1) ∧ ∀ i : fin n, a i > 0

theorem jensen_inequality {n: ℕ} (f: ℝ → ℝ) (a: fin n → ℝ) (ha : is_weight a) (hf : is_convex f):
  ∀ x : fin n → ℝ,
    (f (sum_seq (λ i : fin n, (a i) * (x i)))) ≤
    (sum_seq (λ i : fin n, (a i) * f (x i)))
:=
begin
  revert a,
  induction n with pn ih,
     intro a,
     sorry,
  sorry,
end
