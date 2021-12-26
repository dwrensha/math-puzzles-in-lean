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

variable {A : Type}

def break_into_words :
   (stream ℕ) × -- word lengths
   (stream A) → -- original sequence
   (stream (list A)) -- sequence of words
 := @stream.corec
     (stream ℕ × stream A)
     (list A)
     (λ ⟨lengths, seq⟩, stream.take (lengths.head) seq)
     (λ ⟨lengths, seq⟩,
          ⟨lengths.tail,
           stream.drop (lengths.head) seq⟩)

-- #eval (stream.take 10 (break_into_words ⟨id, id⟩))

def all_same_class
  (b : stream (list A))
  (is_decent : list A → Prop) : Prop :=
 stream.all is_decent b ∨ stream.all (λ w ,¬is_decent w) b

def prefix_decent
  (is_decent : list A → Prop)
  (a : stream A) : Prop :=
stream.all is_decent (stream.inits a)

theorem kolmogorov_puzzle
  (A : Type)
  (is_decent : list A → Prop)
  (a : stream A)
  : (∃ (b : stream ℕ),
     (stream.all (λ x, 0 < x) b ∧
      all_same_class
       (stream.tail $ break_into_words ⟨b, a⟩) is_decent)) :=
begin
  let p : Prop :=
     (∃ (n : ℕ), ∀ (k : ℕ), n < k →
         ¬ prefix_decent is_decent (stream.drop k a)),

  have h := classical.em p,
  cases h with h hnot,
  { sorry },
  {
    push_neg at hnot,
    obtain ⟨b : stream ℕ, hb⟩ := classical.axiom_of_choice hnot,
    use b,
    sorry
  },

end
