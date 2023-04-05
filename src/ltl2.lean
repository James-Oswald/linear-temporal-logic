

import data.set.basic
import tactic.linarith

-- LTL Formulae Syntax --------------------------------------------------------------

inductive ltlFormula : Type
| ltlTrue : ltlFormula
| atom : nat -> ltlFormula
| not : ltlFormula -> ltlFormula
| and : ltlFormula -> ltlFormula -> ltlFormula
--Next (Circle Operator), φ is true in the next state
-- x → φ → x → x → x → ...
| next : ltlFormula -> ltlFormula      
--Until (U operator), φ U ψ, ψ is true at some point φ is true until then
-- φ,¬ψ → φ,¬ψ → φ,¬ψ → ψ → x → ...             
| until : ltlFormula -> ltlFormula -> ltlFormula    

notation `~`φ := (ltlFormula.not φ)
notation φ `l∧` ψ := (ltlFormula.and φ ψ)
notation `∘`φ  := (ltlFormula.next φ) 
notation φ `U` ψ := (ltlFormula.until φ ψ)

open ltlFormula

--Eventually (Diamond Operator), φ is eventually true
-- ¬φ → ¬φ → ¬φ → φ → x → ...
def eventually (φ : ltlFormula) : ltlFormula := ltlTrue U φ
notation `⋄`φ  := (eventually φ) 

--Always (Box Operator), φ is always true
-- φ is not eventually not true
-- φ → φ → φ → φ → φ → ...
def always (φ : ltlFormula) : ltlFormula := ~⋄~φ
notation `□`φ := (always φ)

def ltlImplies (φ ψ : ltlFormula) : ltlFormula := ~(φ l∧ ~ψ)
notation φ `l→` ψ := ltlImplies φ ψ

-- Worlds and World Slices --------------------------------------------------------------

--Worlds are functions that map a state index to a set of
--props (nats) that are true in that state
def world : Type := nat -> (set nat)

--A world slice creates a new world at the provided offset
--Notation looks kind of like a python slice
def worldSlice (σ : world) (i : nat) : world := λn, σ (n + i)
notation σ`[`i`...]` := (worldSlice σ i)  

--The slice composition theorem says that we can compose 2 slices 
--by adding their offsets
theorem sliceComposition : ∀(σ : world) (i j : nat), σ[i...][j...] = σ[i + j...] :=
begin
  intros σ i j,
  rewrite worldSlice,
  rewrite worldSlice,
  rewrite worldSlice,
  simp,
  have H : ∀ (n : nat), (n + j + i) = (n + (i + j)), {
    intros n,
    linarith,
  },
  simp [H],
end

-- LTL Formulae Semantics --------------------------------------------------------------

def sat : world->ltlFormula->Prop
| σ ltlTrue := true
| σ (atom a) := a ∈ (σ 0)
| σ (not φ) := ¬(sat σ φ)
| σ (and φ ψ) := sat σ φ ∧ sat σ ψ
| σ (next φ) := sat (σ[1...]) φ
-- φ must remain true until ψ becomes true
-- There exists an i at which ψ becomes true, until that time i φ is true forall  0 <= k < i   
| σ (until φ ψ) := ∃ (i : nat), (sat (σ[i...]) ψ ∧ ∀ (k : nat), (k < i) -> sat (σ[k...]) φ) 

--Simplifying the SAT for the Eventually operator
--There exists a state j in the future which φ is true
theorem satEventually : ∀φ σ, sat σ (⋄φ) ↔ ∃(j : nat), sat (σ[j...]) φ := begin
  intros φ σ,
  apply iff.intro,{
    rewrite eventually,
    rewrite sat,
    intros H,
    cases H with w1 H,
    existsi w1,
    cases H with left right,
    exact left,
  },{
    rewrite eventually,
    rewrite sat,
    intros H,
    cases H with w1 H,
    existsi w1,
    split,{
      exact H,
    },{
      intros k,
      rewrite worldSlice,
      rewrite sat,
      finish,
    }
  }
end

--Simplifying the SAT for the Always operator
--Forall states j in the future and present, φ is true
theorem satAlways : ∀φ σ, sat σ (□φ) ↔ ∀(j : nat), sat (σ[j...]) φ := begin
  intros φ σ,
  apply iff.intro,{
    rewrite always,
    rewrite sat,
    rewrite satEventually,
    simp,
    intros H j,
    have H2 := H j,
    rewrite worldSlice at H2,
    rewrite sat at H2,
    rewrite <-worldSlice at H2,
    simp at H2,
    exact H2,
  },{
    rewrite always,
    rewrite sat,
    rewrite satEventually,
    simp,
    intros H j,
    have H2 := H j,
    rewrite worldSlice,
    rewrite sat,
    rewrite <-worldSlice,
    simp,
    exact H2,
  }
end

