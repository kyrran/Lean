
set_option pp.structure_projections false

namespace l10
open nat

#check nat
#check ℕ 
#check zero
#check succ
#check succ zero
#check succ (succ(succ zero))

/--
inductive nat: Type
| zero : nat
| succ : nat → nat
--/

--zero and succ are different
--succ is injective : if succ m = succ n then m = n
--all the natural numbers are generaed from zero and succ

example : ∀ n : ℕ, 0 ≠ succ n :=
begin
  assume n h,
  contradiction,
end

def pred : ℕ → ℕ
| zero := zero
| (succ n) := n

#reduce (pred 7)

   
theorem inj_succ : ∀ m n : ℕ, succ m = succ n → m = n :=
begin
  assume m n h,
  change pred (succ m) = pred (succ n),
  rewrite h,
end
--utomatically for all inductive types which avoids the need to define pred:
example :  ∀ m n : nat, succ m = succ n → m = n :=
begin
  assume m n h,
  injection h, --given h : succ m = succ n, we can prove m = n
end

--structural recursion (primitive recursion)
def double : ℕ → ℕ
| zero := 0
| (succ n) := succ (succ (double n))
--double 7 = double (succ 6) = succ (succ (double 6)) = succ (succ 12) = 14

#reduce (double 7)

def half : ℕ → ℕ
| zero := zero
| (succ zero) := zero
| (succ (succ n)) := succ (half n)

#reduce (half 7)
#reduce (half (double 7))

/--
def foo3 : ℕ → ℕ
| 0 := 0
| (succ n) := foo3 (succ n)
--/
--non terminating recursion



--proof by induction
theorem half_double : ∀ n : ℕ , half (double n) = n :=
begin
  assume n,
  induction n with n' ih, --induction hypothesis
  refl,
  dsimp [double],
  dsimp [half],  --similar to apply
  apply congr_arg succ, --eliminate same term
  --exact ih,
  rewrite ih,
end
end l10







namespace l11

set_option pp.structure_projections false
open nat

--primirative/structural recursion
--induction

def foo : ℕ → ℕ 
| 0 := 0
| (succ n) := succ (foo n)

#reduce (foo 7)

example : ∀ n : ℕ , foo n = n :=
begin
  assume n,
  induction n with n' ih,
  --dsimp[foo],
  reflexivity,

  dsimp[foo],
  --apply congr_arg succ,
  --exact ih,
  rewrite ih, 
end

def add : ℕ → ℕ → ℕ
| m  zero     := m
| m  (succ n) := succ (add m n)

#reduce add 7 3

local notation m + n := add m n

theorem add_rneutr : ∀ n : ℕ, n + 0 = n := --right neutral
begin
  assume n,
  dsimp[(+),add],
  refl,
end

theorem add_lneutr : ∀ n : ℕ, 0 + n  = n :=
begin
  assume n,
  induction n with n' ih,
  refl,
  
  apply congr_arg succ, --local notation
  exact ih,
end

--associativity

theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) :=
begin
  assume l m n,
  induction n with n' ih,
  --dsimp[(+),add],
  refl,

  dsimp [(+), add],
  apply congr_arg succ,
  exact ih,
end
--shown that + with 0 is a monoid
--another monoid 1 * n


-- commutativity
lemma add_succ_lem : ∀ m n : ℕ, succ m + n = succ (m + n) :=
begin
  assume m n,
  induction n with n' ih,
  --dsimp[(+),add],
  refl,

  apply congr_arg succ,
  exact ih,
end


theorem add_comm : ∀ m n : ℕ , m + n = n + m :=
begin
  assume m n,
  induction m with m' ih,
  dsimp[(+),add],
  apply add_lneutr,--left neutral --rewrite lneutr,
  
  dsimp[(+),add],
  --transitivity,
  rewrite add_succ_lem,
  apply congr_arg succ,
  exact ih,
end

theorem add_comm2 : ∀ m n : ℕ , m + n = n + m :=
begin
  assume m n,
  induction m with m' ih,
  dsimp[(+),add],
  rewrite add_lneutr,
  calc
    succ m' + n = succ (m' + n) : by apply add_succ_lem
    ... = succ (n + m') : by apply congr_arg succ ih
    ... = n + succ m' : by refl
end

end l11






