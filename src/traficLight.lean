
import ltl
import data.nat.modeq
import tactic.linarith

open ltlFormula

--Proving properties about a specific example
def red : nat := 1
def yellow : nat := 2
def green : nat := 3

def colors : nat -> set nat
| 0 := {red} 
| 1 := {red, yellow}
| 2 := {green} 
| 3 := {yellow}
| _ := {0}

def traficLightWorld (m : nat) : set nat := colors (m % 4)

--The trafic light is green infinitly often
--Always eventually green
example : sat traficLightWorld □⋄(atom green) := begin
  rewrite satAlways,
  intros j,
  rewrite satEventually,
  --This is our witness, for all states j, the light will be green at state 2 + 3*j
  existsi 2 + 3*j, 
  rewrite sliceComposition,
  rewrite worldSlice,
  rewrite sat,
  simp,
  have H : j + (2 + 3*j) = 2 + 4*j, by linarith,
  rw H,
  rw traficLightWorld,
  simp,
  have H2 : 2 % 4 = 2, by apply nat.add_mod_eq_ite,
  rw H2,
  unfold colors,
  simp,
end
 
