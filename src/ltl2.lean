import data.set.basic

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
notation `O`φ  := (ltlFormula.next φ) 
notation φ `U` ψ := (ltlFormula.until φ ψ)

open ltlFormula

--Eventually (Diamond Operator), φ is eventually true
-- ¬φ → ¬φ → ¬φ → φ → x → ...
def eventually (φ : ltlFormula) : ltlFormula := ltlTrue U φ
notation `⋄`φ  := (eventually φ) 

--Always (Box Operator), φ is always true
-- φ → φ → φ → φ → φ → ...
def always (φ : ltlFormula) : ltlFormula := (~(⋄(~φ))) 
notation `□`φ := (always φ)

--Worlds are functions that map a state index to a set of
--props (nats) that are true in that state
def world : Type := nat -> (set nat)

def worldSlice (σ : world) (i : nat) : world := λn, σ (n + i)
notation σ`[`i`...]` := (worldSlice σ i)  

def sat : world->ltlFormula->Prop
| σ ltlTrue := true
| σ (atom a) := a ∈ (σ 0)
| σ (not φ) := ¬(sat σ φ)
| σ (and φ ψ) := sat σ φ ∧ sat σ φ
| σ (next φ) := sat (σ[1...]) φ
-- φ must remain true until ψ becomes true
-- There exists an i at which ψ becomes true, until that time i φ is true forall  0 <= k < i   
| σ (until φ ψ) := ∃ i ≥ 0, (sat (σ[i...]) ψ ∧ ∀ (k : nat), (0 ≤ k ∧ k < i) -> sat (σ[k...]) φ) 

--Simplifying the SAT for the Eventually operator
--There exists a state j in the future which φ is true
theorem satEventually : ∀φ σ, sat σ (⋄φ) ↔ ∃j ≥ 0, sat (σ[j...]) φ := begin
  intros φ σ,
  apply iff.intro,{
    rewrite eventually,
    rewrite sat,
    intros H,
    cases H with w1 H,
    cases H with w2 H,
    existsi [w1, w2],
    cases H with left right,
    exact left,
  },{
    rewrite eventually,
    rewrite sat,
    intros H,
    cases H with w1 H,
    cases H with w2 H,
    existsi [w1, w2],
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
theorem satAlways : ∀φ σ, sat σ (□φ) ↔ ∀j ≥ 0, sat (σ[j...]) φ := begin
  intros φ σ,
  apply iff.intro,{
    rewrite always,
    rewrite sat,
    rewrite satEventually,
    simp,
    intros H j c,
    have H2 := (H j) c,
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
    intros H j c,
    have H2 := (H j) c,
    rewrite worldSlice,
    rewrite sat,
    rewrite <-worldSlice,
    simp,
    exact H2,
  }
end