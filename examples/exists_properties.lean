
/-
Introduction rule requires a witness where a predicate
can be proven to be true for that witness
-/
def existsIntro 
  (T: Type) 
  (pred: T → Prop) 
  (witness : T) 
  (proof : pred witness) 
  : ∃(w: T), pred w
  := exists.intro witness proof

example{T: Type}{witness: T}
  {predicate: T → Prop}
  {proof: predicate witness}:
  ∃ m, predicate m := 
    ⟨ witness, proof ⟩

def isEven(n : nat) : Prop :=
  ∃(m : nat), m + m = n

lemma pf8is4twice: 4 + 4 = 8 := rfl

theorem even8: isEven 8 :=
  exists.intro 4 pf8is4twice

theorem even8': ∃(m : nat), m + m = 8 :=
  exists.intro 4 pf8is4twice

theorem even8'': eightEven := 
  ⟨ 4, pf8is4twice ⟩ 

theorem even8''' : isEven 8 := 
begin
  unfold isEven, -- not necessary
  exact ⟨ 4, pf8is4twice ⟩ 
end 
