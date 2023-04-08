
--Havily influenced by Benzmuller's paper 
--"Interacting with Modal Logics in the Coq Proof Assistant"
--http://page.mi.fu-berlin.de/cbenzmueller/papers/C44.pdf

--The type for "worlds"
variable world : Type

#check world

--The type for individuals
variable i : Type

--Accessability relations between worlds
variable r : world -> world -> Prop

--Modal Propositions take a world and return a prop
def ltlProp : Type := world -> Prop

#check ltlProp

def ltlnot (p : ltlProp world) (w : world) : Prop := ¬(p w)
notation 

#check ltlnot