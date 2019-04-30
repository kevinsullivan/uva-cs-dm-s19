inductive day : Type
| sunday : day
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day

open day

def tues : day := tuesday

def tom : day → day
| sunday := monday
| monday := tuesday
| tuesday := wednesday
| wednesday := thursday
| thursday := friday
| friday := saturday
| saturday := sunday

def tom' (d : day) : day :=
match d with
| sunday := monday
| monday := tuesday
| tuesday := wednesday
| wednesday := thursday
| thursday := friday
| friday := saturday
| saturday := sunday
end

#check tom'

-- semantically the same, but not syntactically
example: tom = tom' :=
begin
  sorry,
--  exact eq.refl tom,
end

def isWeekday : day → bool
| monday := tt
| tuesday := tt
| wednesday := tt
| thursday := tt
| friday := tt
| _ := ff

def isWeekday' : day → bool
| saturday := ff
| sunday := ff
| _ := tt

example :
    ∀ d : day,
    tom (tom (tom (tom (tom (tom (tom d)))))) = d :=
begin
  intro d,
  induction d,
  exact rfl,
  exact rfl,
  exact rfl,
  exact rfl,
  exact rfl,
  exact rfl,
  exact rfl,
end

example :
    ∀ d : day,
    tom (tom (tom (tom (tom (tom (tom d)))))) = d :=
begin
  intro d,
  induction d,
  repeat {exact rfl},
end

inductive switch : Type
| On : switch
| Off : switch

open switch 

def turnOn (s: switch) : switch :=
match s with
| _ := On
end

def turnOff (s: switch) : switch :=
match s with
| _ := Off
end


def toggle (s : switch) : switch :=
match s with 
| On := Off
| Off := On
end

def toggle': switch → switch
  | On := Off
  | Off := On

example : ∀ s : switch, toggle (toggle s) = s :=
begin
  intro s,
  induction s,
  exact rfl,
  exact rfl,
end


#print list
#print prod

inductive myprod (S T : Type) : Type
| mk (s : S) (t : T) : myprod

def p1 := myprod.mk 1 "Hello"

def fst' : ∀ (S T : Type), myprod S T → S
| S T (myprod.mk f s) := f

#eval fst' nat string p1

def fst : ∀ { S T : Type }, myprod S T → S
| S T (myprod.mk f s ) := f

#eval fst p1

def snd' : ∀ (S T : Type), myprod S T → T
| S T (myprod.mk f s) := s

def snd : ∀ { S T : Type }, myprod S T → T
| S T (myprod.mk f s) := s

def swap' : ∀ (S T : Type), myprod S T → myprod T S
| S T (myprod.mk f s) := (myprod.mk s f)

def swap : ∀ { S T : Type }, myprod S T → myprod T S
| S T (myprod.mk f s) := (myprod.mk s f)

#check swap p1

theorem proj_ok :
    ∀ (S T : Type) (s : S) (t : T),
    myprod.mk
        (fst (myprod.mk s t))
        (snd (myprod.mk s t)) =
    (myprod.mk s t) :=
begin
intros S T s t,
exact rfl,
end

theorem proj_ok' :
    ∀ (S T : Type) (pr : myprod S T),
    myprod.mk
        (fst pr)
        (snd  pr) =
    pr :=
begin
intros S T pr,
cases pr with f s,
exact rfl,
end

theorem swap_involutive :
    ∀ (S T : Type) (pr : myprod S T),
    swap (swap pr) = pr :=
begin
  intros S T pr,
  sorry
  --exact rfl,      -- fix this proof
end


-- Let's test it  out
def p2 := myprod.mk 1 2
def p3 := myprod.mk 1 tt
#check p2
#check p3
#eval fst' nat nat (myprod.mk 1 1)
#eval fst (myprod.mk 1 1)
#eval snd' string bool (myprod.mk "Hello" tt)
#eval snd (myprod.mk "Hello" tt)
#eval swap' string bool (myprod.mk "Hello" tt)
#eval swap (myprod.mk "Hello" tt)

/-
BOOLEAN
-/

    inductive mybool : Type
    | ttt : mybool
    | fff : mybool

    open mybool

    -- unary functions (why four?)

    def id_mybool (b: mybool) : mybool := b
    def true_mybool (b: mybool) := ttt
    def false_mybool (b: mybool) := fff
    def not_mybool: mybool → mybool
    | ttt := fff
    | fff := ttt

    -- binary functions (how many are there total?)

    def and_mybool: mybool → mybool → mybool
        | ttt ttt := ttt
        | ttt fff := fff
        | fff ttt := fff
        | fff fff := fff

    def and_mybool': mybool → mybool → mybool
        | ttt ttt := ttt
        | _ _ := fff

    def or_mybool (b1 b2 : mybool) : mybool :=
      match b1, b2 with
        | fff, fff := fff
        | _, _ := ttt
      end

    def implies_mybool (b1 b2 : mybool) : mybool :=
      match b1, b2 with
        | ttt, fff := fff
        | _, _ := ttt
      end

    example: ∀(b1 b2: mybool),
      (implies_mybool b1 b2) = (or_mybool (not_mybool b1) b2) :=
    begin
      intros b1 b2,
      induction b1,
        induction b2,
          -- ttt ttt
          unfold implies_mybool,
          unfold not_mybool,
          unfold or_mybool,
          -- ttt fff
          unfold implies_mybool,
          unfold not_mybool,
          unfold or_mybool,
        -- fff _
        unfold implies_mybool,
        unfold not_mybool,
        unfold or_mybool,
    end

    def xor_mybool (b1 b2 : mybool) : mybool :=
      match b1, b2 with
        | ttt, fff := ttt
        | fff, ttt := ttt
        | _, _ := fff
      end

    -- For booleans, xnor is equality - why?
    def xnor_mybool (b1 b2 : mybool) : mybool :=
      match b1, b2 with
        | ttt, ttt := ttt
        | fff, fff := ttt
        | _, _ := fff
      end
    
    def eq_mybool (b1 b2 : mybool) : mybool :=
      match b1, b2 with
        | ttt, ttt := ttt
        | fff, fff := ttt
        | _, _ := fff
      end

    example: ∀(b1 b2: mybool),
      (xnor_mybool b1 b2) = (xor_mybool b1 (not_mybool b2)) :=
    begin
      intros,
      induction b1,
        induction b2,
          -- ttt ttt
          unfold xnor_mybool,
          unfold not_mybool,
          unfold xor_mybool,
          -- ttt fff
          unfold xnor_mybool,
          unfold not_mybool,
          unfold xor_mybool,
        induction b2,
          -- fff ttt
          unfold xnor_mybool,
          unfold not_mybool,
          unfold xor_mybool,
          -- fff fff
          unfold xnor_mybool,
          unfold not_mybool,
          unfold xor_mybool,
    end

    lemma xnor_is_eq: ∀(b1 b2: mybool),
      (xnor_mybool b1 b2) = (eq_mybool b1 b2) :=
    begin
      intros,
      exact rfl,
    end

    theorem and_mybool_comm : 
        ∀ b1 b2 : mybool, and_mybool b1 b2 = and_mybool b2 b1 :=
    begin
      intros b1 b2,
      induction b1,
      induction b2,
      repeat {trivial},
      induction b2,
      repeat {trivial},
    end

    theorem and_mybool_implies_or_mybool : 
        ∀ b1 b2 : mybool, 
            implies_mybool (and_mybool b1 b2) (or_mybool b1 b2) = ttt :=
    begin
    intros b1 b2,
    induction b1,
    induction b2,
    trivial,
    trivial,
    induction b2,
    trivial,
    trivial,
    end
    

    theorem demorgan1 : ∀ b1 b2 : mybool,
        not_mybool (and_mybool b1 b2) =
        or_mybool
            (not_mybool b1)
            (not_mybool b2) :=
    begin
    intros b1 b2,
    induction b1,
    induction b2,
    apply rfl,
    apply rfl,
    induction b2,
    apply rfl,
    apply rfl,
    end

    theorem demorgan2 : ∀ b1 b2 : mybool,
        not_mybool (or_mybool b1 b2) =
        and_mybool
            (not_mybool b1)
            (not_mybool b2) :=
    begin
    intros b1 b2,
    induction b1, 
    induction b2,
    apply rfl,
    apply rfl,
    induction b2,
    apply rfl,
    apply rfl,
    end

   -- NATURAL NUMBERS


    namespace mynat

    inductive mynat : Type
    | zero : mynat
    | succ : mynat → mynat

    def z := mynat.zero
    def one := mynat.succ (mynat.zero)
    def two := mynat.succ one
    def three := mynat.succ two
    def four :=     mynat.succ 
                        (mynat.succ 
                            (mynat.succ 
                                (
                                    mynat.succ 
                                        mynat.zero
                                )
                            )
                        )


    -- functions

    -- some unary functions
    def id_mynat (n: mynat) := n
    def zero_mynat (n: mynat) := mynat.zero

    def pred : mynat → mynat 
    | mynat.zero := mynat.zero
    | (mynat.succ n') := n'

    #reduce pred four

    -- a binary function, and it's recursive
    def add_mynat: mynat → mynat → mynat
    | mynat.zero m := m
    | (mynat.succ n') m :=
        mynat.succ (add_mynat n' m)

    #reduce add_mynat three four

    def mul_mynat: mynat → mynat → mynat
      | mynat.zero m := mynat.zero
      | (mynat.succ n') m := add_mynat m (mul_mynat n' m)

    #reduce mul_mynat two three

    def exp_mynat: mynat → mynat → mynat
      | m mynat.zero := one
      | m (mynat.succ n') := mul_mynat m (exp_mynat m n')

    #reduce exp_mynat two three
    #reduce exp_mynat three two

    -- 3^2 = 2^3 + 1
    example: (exp_mynat three two) =
                mynat.succ(exp_mynat two three) := rfl

    -- tetration
    def tet_mynat: mynat → mynat → mynat
      | m mynat.zero := one
      | m (mynat.succ n') := exp_mynat m (tet_mynat m n')

    #reduce tet_mynat two three

    example: (tet_mynat two three) =
                (exp_mynat two four) := rfl

    -- a certificate

    -- zero is a left identify
    theorem zero_left_id : 
        ∀ m : mynat, add_mynat mynat.zero m = m :=
    begin
      intro m,
      trivial,
    end

    -- zero is a right identity, requires induction
    theorem zero_right_id : 
        ∀ m : mynat, add_mynat m mynat.zero = m :=
    begin
      intro m,
      -- proof by induction
      induction m with m' h,
        -- first the base case
        apply rfl,
        -- then the inductive case
        simp [add_mynat],
        assumption,
    end

    -- Prove n + (m + 1) = (n + m) + 1
   lemma add_n_succ_m :
     ∀ n m : mynat, 
       add_mynat n (mynat.succ m) =
         mynat.succ (add_mynat n m) :=
    begin
      intros n m,
      induction n with n' h,
        apply rfl,  -- base case

        simp [add_mynat], -- inductive case
        assumption,
    end

    example: ∀(m n : mynat),
      add_mynat m n = add_mynat n m :=
    begin
      intros m n,
      -- by induction on m 
      induction m with m' h,
        --base case: m = zero
        simp [add_mynat],
        rw zero_right_id,

        -- inductive case: if true for m then true for succ m
        simp [add_mynat],
        rw add_n_succ_m,
        -- rewrite using induction hypothesis!
        rw h,
    end

end mynat

#check nat.zero

example : ∀ n : ℕ, true :=
begin
  intro n,
  cases n with n',
  exact true.intro,
  exact true.intro,
end

example : ∀ (P Q : Prop), P ∨ Q → true :=
begin
  intros P Q pq,
  cases pq with p q,
  exact true.intro,
  exact true.intro,
end

namespace ll_ns

  inductive list : Type
    | empty : list
    | node : ℕ → list → list

  #reduce list.empty
  def list_9 := list.node 9 list.empty
  def list_5_9 := list.node 5 list_9
  def list_1_5_9 := list.node 1 list_5_9
  def list_4_1_5_9 := list.node 4 list_1_5_9
  def list_1_4_1_5_9 := list.node 1 list_4_1_5_9
  def list_pi := list.node 3 list_1_4_1_5_9
  #reduce list_pi

  def count: list → ℕ
    | list.empty := 0
    | (list.node _ next) := 1 + (count next)

  #reduce count list_pi

  -- Not really recursive!
  def count'(ll: list): ℕ :=
    match ll with
      | list.empty := 0
      | (list.node _ next) := 1 + (count next)
    end

  #reduce count' list_pi

  def last: list → ℕ
    | list.empty := 0  -- because we need a total function
    | (list.node val list.empty) := val
    | (list.node _ rem) := last rem

  #reduce last list_pi

  def sum: list → ℕ
    | list.empty := 0
    | (list.node val next) := val + (sum next)
  
  #reduce sum list_pi

  -- Returns a list devoid of its last node
  -- E.g., (head (list.node 5 (list.node 9 list.empty))) returns
  --         (list.node 5 list.empty)
  def head: list → list
    | list.empty := list.empty
    | (list.node _ list.empty) := list.empty
    | (list.node val rem) := (list.node val (head rem))

  #reduce head list_pi

  -- Lemma that adding an element to a list and then
  -- taking the head is the same as taking the head and
  -- then adding an element (unless the list is empty)
  lemma head_commutes_with_listnode:
    ∀(mylist: list)(val: ℕ),
      (mylist = list.empty) ∨
        (head (list.node val mylist)) =
           (list.node val (head mylist)) :=
  begin
    intros,
    induction mylist with val' mylist',
      -- base case
      apply or.inl,
      exact rfl,
      -- inductive case
      apply or.inr,
      cases mylist_ih,
        -- empty
        simp [head],
        -- non-empty
        simp [head],
  end

  lemma head_shortens_nonempty_list:
    ∀(mylist: list), (mylist = list.empty) ∨ 
      (count (head mylist)) = (count mylist) - 1 :=
  begin
    assume mylist,
    induction mylist with val mylist casen,
      -- base case
      apply or.inl,
      exact rfl,
      -- inductive case
      apply or.inr,
      cases casen,
        -- empty case
        rw casen,
        simp [head],
        simp [count],
        -- nonempty case
        simp [count],
        induction mylist with val' mylist casen',
          -- base case
          simp[head],
          -- inductive case
          have newfact := head_commutes_with_listnode (list.node val' mylist) val,
          cases newfact with impossibly_empty commutes,
            -- impossibly empty
            trivial,
            -- non-empty
            sorry
  end

  -- Returns a reversed list
  -- A reversed list is a list that starts with the last node
  -- in the original list and is followed by the reverse list
  -- of the head of the original list
--  def reverse: list → list
--    | list.empty := list.empty
--    | nonempty_list := (list.node 
--                          (last nonempty_list)
--                          (reverse (head nonempty_list)))

end ll_ns