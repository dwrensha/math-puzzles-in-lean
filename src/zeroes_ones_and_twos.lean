import data.nat.basic
import data.nat.digits


def all_zero_or_one : list ℕ → Prop
| [] := true
| (0 :: ds) := all_zero_or_one ds
| (1 :: ds) := all_zero_or_one ds
| _ := false

theorem part_one (n : ℕ) : ∃ k : ℕ, all_zero_or_one (digits 10 (n * k)) :=
begin
  sorry
end
