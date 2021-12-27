import data.stream.defs

import tactic.basic
import tactic.push_neg
import tactic.rcases
import tactic.suggest

/-

Suppose each (finite) word is either "decent" or "indecent". Given an infinite
sequence of characters, can you always break it into finite words so that all
of them except perhaps the first one belong to the same class?

Answer: yes.

-/

variable {α : Type}

def break_into_words :
   (stream ℕ) × -- word lengths
   (stream α) → -- original sequence
   (stream (list α)) -- sequence of words
 := @stream.corec
     (stream ℕ × stream α)
     (list α)
     (λ ⟨lengths, seq⟩, stream.take (lengths.head) seq)
     (λ ⟨lengths, seq⟩,
          ⟨lengths.tail,
           stream.drop (lengths.head) seq⟩)

-- #eval (stream.take 10 (break_into_words ⟨id, id⟩))

def all_same_class
  (b : stream (list α))
  (is_decent : list α → Prop) : Prop :=
 stream.all is_decent b ∨ stream.all (λ w ,¬is_decent w) b

def all_prefixes
  (p : list α → Prop)
  (a : stream α) : Prop :=
stream.all p (stream.inits a)

theorem kolmogorov_puzzle
  (is_decent : list α → Prop)
  (a : stream α)
  : (∃ (b : stream ℕ),
     (stream.all (λ x, 0 < x) b ∧
      all_same_class
       (stream.tail $ break_into_words ⟨b, a⟩) is_decent)) :=
begin
  let p : Prop :=
     (∃ (n : ℕ), ∀ (k : ℕ), n < k →
         ¬ all_prefixes is_decent (stream.drop k a)),

  have h := classical.em p,
  cases h with h hnot,
  { sorry },
  { push_neg at hnot,
    obtain ⟨c : stream ℕ,
            hc : ∀ (x : ℕ), x < c x ∧ all_prefixes is_decent (stream.drop (c x) a)⟩
      := classical.axiom_of_choice hnot,
    sorry,
  },

end
