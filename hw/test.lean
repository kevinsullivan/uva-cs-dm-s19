example: ∀ a b : nat, a = b → b = a :=
begin
assume a b : ℕ,
assume ab : a = b,
apply (eq.symm ab),
end 

lemma foo : ∀ a b : nat, a = b → b = a :=
λ a,
    λ b,
        λ ab,
        (eq.symm ab)

#check foo