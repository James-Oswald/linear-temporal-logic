
/-

In this file we prove some basic tautologies and equivelences in LTL

-/

import ltl

--A formulae is a tautology if it is satisfied on all worlds
def satAllWorlds (φ : ltlFormula) : Prop := ∀ (σ : world), sat σ φ 

def ltlEq (φ ψ : ltlFormula) : Prop := satAllWorlds ((φ l→ ψ) l∧ (ψ l→ φ))
notation φ `≡` ψ := ltlEq φ ψ

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

-- duality laws 
example: ∀(φ : ltlFormula), ~∘φ ≡ ∘~φ :=
begin 
  intros φ,
  rw ltlEq,
  rw satAllWorlds,
  intro σ,
  rw sat,
  split,
  repeat {
    rw satImpl,
    intro H,
    repeat {rw sat},
    repeat {rw sat at H},
    exact H,
  },
end 

example: ∀(φ : ltlFormula), ~⋄φ ≡ □~φ :=
begin 
  intros φ,
  rw ltlEq,
  rw satAllWorlds,
  intro σ,
  rw sat,
  split,{
    rw satImpl,
    intro H,
    rw sat at H,
    rw satEventually at H,
    simp at H,
    rw satAlways,
    intro j,
    rw sat,
    revert j,
    exact H,
  },{
    rw satImpl,
    intro H,
    rw satAlways at H,
    rw sat,
    rw satEventually,
    simp,
    intro j,
    rw <-sat,
    revert j,
    exact H,
  },
end

--idempotency laws
example: ∀(φ : ltlFormula), ⋄⋄φ ≡ ⋄φ :=
begin 
  intros φ,
  rw ltlEq,
  rw satAllWorlds,
  intro σ,
  rw sat,
  split,{
    rw satImpl,
    intro H,
    rw satEventually,
    rw satEventually at H,
    cases H,
    rw satEventually at H_h,
    cases H_h,
    existsi H_w + H_h_w,
    rw <-sliceComposition,
    exact H_h_h,
  },{
    rw satImpl,
    intro H,
    rw satEventually,
    rw satEventually at H,
    cases H,
    existsi H_w,
    rw satEventually,
    existsi 0,
    rw sliceComposition,
    simp,
    exact H_h,
  },
end

example: ∀(φ : ltlFormula), □□φ ≡ □φ :=
begin 
  intros φ,
  rw ltlEq,
  rw satAllWorlds,
  intro σ,
  rw sat,
  split,{
    rw satImpl,
    intro H,
    rw satAlways,
    intro j,
    rw satAlways at H,
    have H2 := H j,
    rw satAlways at H2,
    have H3 := H2 0,
    rw sliceComposition at H3,
    simp at H3,
    exact H3,
  },{
    rw satImpl,
    intro H,
    rw satAlways,
    intro j,
    rw satAlways,
    intro j_1,
    rw satAlways at H,
    have H2 := H (j + j_1),
    rw <-sliceComposition at H2,
    exact H2,
  },
end

-- ∘ distributes over ∧   
example: ∀(φ ψ : ltlFormula), ∘(φ l∧ ψ) ≡ (∘φ l∧ ∘ψ) :=
begin
  intros φ ψ,
  rw ltlEq,
  rw satAllWorlds,
  intro σ,
  rw sat,
  split,
  repeat {  --Same steps in both directions
    rw satImpl,
    intro H,
    repeat {rw sat},
    repeat {rw sat at H},
    exact H,
  },
end 


