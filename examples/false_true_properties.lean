
lemma notFalse: ¬false :=
begin
  assume pfFalse,
  assumption,
end

lemma falseImpliesAnything{anything: Prop}:
  false → anything :=
begin
  assume pfFalse,
  have pfAnything: anything := false.elim pfFalse,
  assumption,
end

lemma tru: true :=
begin
  exact true.intro,
end
