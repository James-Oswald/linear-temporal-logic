
import data.nat.modeq

example (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
begin
  #check (nat.mod_eq_of_lt (lt_add_one 2))
  --cases (nat.mod_eq_of_lt (lt_add_one 2)) with h0 h1,
  --cases () with h1 h2,
  sorry
end