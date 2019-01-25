namespace Propositions.ex1

axioms (P Q : Prop) 
axioms (p1 p2 : P)
axiom Cool : P → Prop

#check true
#check false
#check P
#check Q
#check p1 = p2
#check P ∧ Q
#check P → Q
#check P ↔ Q
#check P ∨ Q
#check ¬ P
#check ∀ p : P, Cool p
#check ∃ p : P, Cool p

end Propositions.ex1
