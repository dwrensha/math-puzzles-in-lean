import data.stream.defs

import tactic.basic
import tactic.push_neg
import tactic.rcases
import tactic.suggest

/-

Puzzle referenced from this tweet: https://twitter.com/sigfpe/status/1474173467016589323

From the book _Out of their Minds: The Lives and Discoveries of 15 Great Computer Scientists_
by Dennis Shasha and Cathy Lazere.


Problem: Suppose each (finite) word is either "decent" or "indecent". Given an infinite
sequence of characters, can you always break it into finite words so that all of them
except perhaps the first one belong to the same class?

Answer: yes.

-/

variable {α : Type}

def break_into_words :
   (stream ℕ) → -- word lengths
   (stream α) → -- original sequence
   (stream (list α)) -- sequence of words
 := function.curry
     (stream.corec
       (λ ⟨lengths, a'⟩, stream.take (lengths.head) a')
       (λ ⟨lengths, a'⟩, ⟨lengths.tail, stream.drop (lengths.head) a'⟩))

-- #eval (stream.take 10 (break_into_words ⟨id, id⟩))

def all_same_class
  (is_decent : list α → Prop)
  (b : stream (list α))
  : Prop :=
 stream.all is_decent b ∨ stream.all (λ w ,¬is_decent w) b

def all_prefixes
  (p : list α → Prop)
  (a : stream α) : Prop :=
stream.all p (stream.inits a)

noncomputable def choose_decent_words
    (is_decent : list α → Prop)
    (a : stream α)
    (hnot: ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
            all_prefixes is_decent (stream.drop (n + k) a))
     : stream ℕ :=
stream.corec (λ acc, classical.some (hnot acc))
             (λ acc, acc + classical.some (hnot acc))
             0

lemma check_decent_words
  (is_decent : list α → Prop)
  (a : stream α)
  (hnot: ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
           all_prefixes is_decent (stream.drop (n + k) a))
  : stream.all is_decent (break_into_words (choose_decent_words is_decent a hnot) a).tail :=
begin
  intro n,
--  have h : ((break_into_words (unravel is_decent a hnot) a).tail.nth n) =
  sorry
end

theorem kolmogorov_puzzle
  (is_decent : list α → Prop)
  (a : stream α)
  : (∃ (b : stream ℕ),
     (stream.all (λ x, 0 < x) b ∧
      all_same_class is_decent
       (stream.tail $ break_into_words b a))) :=
begin
  let p : Prop :=
     (∃ (n : ℕ), ∀ (k : ℕ), 0 < k →
         ¬ all_prefixes is_decent (stream.drop (n + k) a)),

  have h := classical.em p,
  cases h with h hnot,
  { sorry },
  { push_neg at hnot,
    use choose_decent_words is_decent a hnot,
    split,
    { intro n,
      exact (classical.some_spec (hnot _)).1 },
    { left,
      exact check_decent_words is_decent a hnot }
  },

end
