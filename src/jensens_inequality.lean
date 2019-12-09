import data.real.basic

-- first, let's define what it means for a function to be "convex"...

-- f (tx_1 + (1-t)x2) ≤ t f(x1) + (1 - t) f(x2)

def is_convex (f: ℝ → ℝ) : Prop :=
  ∀ t: ℝ, ((0 ≤ t) && (t ≤ 1)) →
    ∀ x1 x2 : ℝ, f (t * x1 + (1 - t) * x2) ≤ t * f x1 + (1 - t) * f x2
