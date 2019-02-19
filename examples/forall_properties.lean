
lemma commutativity_forall{S: Type}:
  (∀(s: S), ∀(P: S → Prop), P s) ↔ 
    (∀(P: S → Prop), ∀(s: S), P s) := 
begin
  split,
    assume pfUnivPS,
    intros,
    exact pfUnivPS s P,

    assume pfUnivPS,
    intros,
    exact pfUnivPS P s,
end

lemma commutativity_forall'{S: Type}:
  (∀(s: S), ∀(P: S → Prop), P s) ↔ 
    (∀(P': S → Prop), ∀(s': S), P' s') := 
begin
  split,
    assume pfUnivPS,
    intros,
    exact pfUnivPS s' P',

    assume pfUnivPS,
    intros,
    exact pfUnivPS P s,
end

lemma forall_is_impl{P Q: Prop}:
   (∀(p: P), Q) ↔ (P → Q) :=
begin
  split,
    assume pfPimpQ,
    assumption,

    assume pfPimpQ,
    assumption,
end
