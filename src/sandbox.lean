
import tactic.linarith
import data.nat.modeq

example (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
begin
  nat.modlt
end

example : ∀ n : ℕ, n.pred < n.succ :=
begin
  intro n,
  induction n,
  finish,
  simp,
  rw nat.succ_eq_add_one,
  rw nat.succ_eq_add_one,
  have H := nat.lt_succ_self n_n,
  have H2 := nat.lt_add_right n_n (n_n+1) 1 H,
  exact H2,
end

/-
example : ∀ n : ℕ, n - 4 < n + 1 :=
begin
  intro n,
  induction n,
  finish,
  have H2 := nat.lt_add_right

end
-/

lemma l1 : ∀(n : nat), n ≠ 0 → nat.succ n ≠ 0 := begin
  finish,
end

example : ∀ (n a b : nat), a ≠ 0 ∧ b ≠ 0  → n - a < n + b :=
begin
  intros n a b H,
  cases H with l r,
  cases n,
  cases a,
  cases b,{
    exfalso,
    simp at l,
    exact l,
  },{
    exfalso,
    simp at l,
    exact l,
  },{
    by_contra,
    simp at h,
    finish,
  },{

  }
  
  /-
  induction n,
  induction a,
  induction b,
  {
    exfalso,
    simp at l,
    exact l,
  },{
    exfalso,
    simp at l,
    exact l,
  },{
    by_contra,
    simp at h,
    finish,
  },{
    
  }-/
end