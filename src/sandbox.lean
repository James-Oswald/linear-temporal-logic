
import ltl
import tactic.linarith
import data.nat.modeq


/-
example (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
begin
  nat.modlt
end
-/

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

/-
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
-/

--Alt trafic light def
/-
def traficLightWorld: nat -> set nat
| 0 := {red} 
| 1 := {red, yellow}
| 2 := {green} 
| 3 := {yellow}
| (nat.succ n) := have n - 4 < n.succ, {
  linarith
/-
  induction n,{
    finish,
  },{
    simp,
  }
-/
}, traficLightWorld (n - 4)
-/

--Once red the light can not become green imediatlty
--For any state, the light being red implies the next state is not green
/-
example : sat traficLightWorld □((atom red) l→ ~∘(atom green)) := begin
  rewrite satAlways,
  intros j,
  rewrite satImpl,
  repeat {rewrite sat},

  induction j,{
    simp [traficLightWorld, worldSlice, sliceComposition, colors, green, red, yellow],
  },{
    simp [traficLightWorld, worldSlice, sliceComposition] at j_ih,
    simp [traficLightWorld, worldSlice, sliceComposition],
    by_contra,
    simp at h,
    have T : (j_n % 4 = 0 ∧ (1 + j_n) % 4 = 1 ∧ (j_n + 2) % 4 = 2) ∨
              (j_n % 4 = 1 ∧ (1 + j_n) % 4 = 2 ∧ (j_n + 2) % 4 = 3) ∨
              (j_n % 4 = 2 ∧ (1 + j_n) % 4 = 3 ∧ (j_n + 2) % 4 = 0) ∨
              (j_n % 4 = 3 ∧ (1 + j_n) % 4 = 0 ∧ (j_n + 2) % 4 = 1), by sorry,
    cases T,
    --Case 1 
    rw nat.succ_eq_one_add j_n at h,
    cases h,
    cases T with t1 t2,
    cases t2 with t2 t3,
    rw [t1, t2] at j_ih,
    rw colors at j_ih,
    rw colors at j_ih,
    --nat.modeq

  },

  /-
  by_contradiction,
  cases h,
  simp at h_right,
  rw sliceComposition at h_right,
  induction j,{
    rw worldSlice at h_right,
    simp at h_right,
    rewrite traficLightWorld at h_right,
    simp [nat.add_mod_eq_ite, colors] at h_right,
    simp [red, green, yellow] at h_right,
    exact h_right,
  },{
    
  } 
  -/
-/


-- U right distributes over ∧   
example: ∀(φ ψ ρ : ltlFormula), (φ l∧ ψ) U ρ ≡ ((φ U ρ) l∧ (ψ U ρ)) :=
begin
  intros φ ψ ρ,
  rw ltlEq,
  split,{
    rw satAllWorlds,
    intro σ,
    rw satImpl,
    intro H,
    rw sat,
    rw sat at H,
    split,{
      rw sat,
      cases H,
      existsi H_w,
      cases H_h,
      split,
      exact H_h_left,
      intro k,
      intro H2,
      have H3 := H_h_right k H2,
      rw sat at H3,
      cases H3,
      exact H3_left,
    },{
      rw sat,
      cases H,
      existsi H_w,
      cases H_h,
      split,
      exact H_h_left,
      intro k,
      intro H2,
      have H3 := H_h_right k H2,
      rw sat at H3,
      cases H3,
      exact H3_right, --Only diffrence from above sub proof
    }
  },{
    rw satAllWorlds,
    intro σ,
    rw satImpl,
    intro H,
    rw sat at H,
    cases H,
    rw sat at H_left H_right,
    rw sat,
    cases H_right,
    cases H_left,
    
    existsi H_left_w,
    cases H_left_h,
    split,
    exact H_left_h_left,
    intros k H2,
    have H3 := H_left_h_right k H2,
    sorry,
  }
end 