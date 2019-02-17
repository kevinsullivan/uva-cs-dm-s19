section hw1

/-
1a. (10 pts) Define a binding from the name "seven" to the value 7.
-/

def seven: ℕ := 7

/-
1b. (10 pts) Use #check to determine the type of "seven"
-/

#check seven

/-
2a. (15 pts) Define a function in "C Style" (see section 2.4.6.2)
called "cube" that takes a single argument, x, and returns the value x^3
-/

def cube(x: ℕ) := x^3

/-
2b. (5 pts) Use #check to determine the type of "cube"
-/

#check cube
-- ℕ → ℕ

/-
3a. (15 pts) Define a function in "Lambda Style" (see section 2.4.6.1)
called "cube'" that takes a single argument, x, and returns the value x^3
-/

def cube': ℕ → ℕ := λ(x: ℕ), x^3

/-
3b. (5 pts) Use #check to determine the type of "cube'"
-/

#check cube'
-- ℕ → ℕ

/-
4. (20 pts) First read the short sections in the notes that we skipped 
on "Tactic Style" development. Then replace the underscore in the following 
"Tactic Style" function definition to create "cube''" so that it returns 
the value x^3, computed using a combination of x and sq_x.
-/

def cube'': ℕ → ℕ :=
begin
  assume x,
  have sq_x := x * x,
  exact x * sq_x
end

/-
5. (20 pts) Use #reduce three times, once with each version of the cube
function to calculate 3^3.
-/

#reduce cube 3
#reduce cube' 3
#reduce cube'' 3

end hw1