axiom isEven : ℕ → Prop

def myProp : Prop := 
    ∀ (x y : ℕ), (isEven x ∧ isEven y) → isEven ( x^2 + y^2 ) 


example : ∀ ( P Q : Prop), P ∧ Q → P :=
    λ P Q : Prop,
        λ pandq : P ∧ Q,

