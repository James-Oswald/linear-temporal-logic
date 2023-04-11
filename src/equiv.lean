
/-

In this file we prove some basic tautologies and equivelences in LTL

-/

import ltl

-- Tautologies --------------------------------------------------------------------------

--Any rule in the form □φ l→ ∘φ is a tautology
example: ∀(φ : ltlFormula), satAllWorlds (□φ l→ ∘φ) :=
begin
  intros φ,
  rw satAllWorlds,
  intros σ,
  rw satImpl,
  intros H,
  rw satAlways at H,
  rw sat,
  have inst := H 1,
  exact inst, 
end

-- Equivelences -------------------------------------------------------------------------

-- All of these are listed on wikipedia https://en.wikipedia.org/wiki/Linear_temporal_logic

-- ∘ distributes over ∧   
example: ∀(φ ψ : ltlFormula), ∘(φ l∧ ψ) ≡ (∘φ l∧ ∘ψ) :=
begin
  intros φ ψ,
  rw ltlEq,
  split,
  repeat {  --Same steps in both directions
    rw satAllWorlds,
    intro σ,
    rw satImpl,
    intro H,
    repeat {rw sat},
    repeat {rw sat at H},
    exact H,
  },
end 

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



  }
end 