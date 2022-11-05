/-
COMP2009-ACE

Exercise 05 (Natural numbers)

    This exercise has 2 parts both count for 50%.

    In the first part the goal is to complete the proof that the
    natural numbers with addition and multiplication form a
    semiring. I include the proof the addition forms a commutative
    monoid (which we have done in the lecture.

    You are not supposed to use the ring tactic for the first part
    (otherwise it would be no challenge).

    Yes, you may need some additional lemmas.

    In the 2nd part you should show that ≤ is anti-symmetric. I
    include the proofs (from the lecture) that it is reflexive and
    transitive. You are allowed to use the ring tactic for this part. 
    (but note that you have to create a lean project to access the
    tactic library).

    You create a lean project using 
    leanproject new my_project
    which creates a folder my_project. You need to stire the exercise
    in my_project/src
    See https://leanprover-community.github.io/install/project.html
    for details.

    However, if you work with the web interface you don't need to
    create a project - ity should work out of the box.

    Please only submit the lean file not the whole project directory.

-/
import tactic -- will fail if you haven't created a project.
set_option pp.structure_projections false

namespace ex05_01

open nat

-- definition of addition:
def add : ℕ → ℕ → ℕ 
| n zero     := n
| n (succ m) := succ (add n m)

local notation m + n := add m n

-- have shown that it is a commutative monoid

theorem add_rneutr : ∀ n : ℕ, n + 0 = n :=
begin
  assume n,
  reflexivity,
end

theorem add_lneutr : ∀ n : ℕ, 0 + n  = n :=
begin
  assume n,
  induction n with n' ih,
  reflexivity,
  dsimp [(+),add],
  rewrite ih,
end

theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) :=
begin
  assume l m n,
  induction n with n' ih,
  reflexivity,
  dsimp [(+),add],
  rewrite ih,
end

lemma add_succ_lem : ∀ m n : ℕ, succ m + n = succ (m + n) :=
begin
  assume m n,
  induction n with n' ih,
  reflexivity,
  apply congr_arg succ,
  exact ih,
end

theorem add_comm : ∀ m n : ℕ , m + n = n + m :=
begin
  assume m n,
  induction m with m' ih,
  apply add_lneutr,
  calc 
    succ m' + n = succ (m' + n) : by apply add_succ_lem
    ... = succ (n + m') : by apply congr_arg succ; exact ih
    ... = n + succ m' : by reflexivity,
end

-- now we define addition

 def mul : ℕ → ℕ → ℕ
 | m 0     := 0
 | m (succ n) := (mul m n) + m

 local notation m * n := mul m n

-- and your task is to show that it is a commutative semiring, i.e.

theorem mult_rneutr : ∀ n : ℕ, n * 1 = n :=
begin
  assume n,
  induction n with n' ih,
  reflexivity,
  dsimp[(*), mul],
  apply add_lneutr,
end

theorem mult_lneutr : ∀ n : ℕ, 1 * n  = n :=
begin
  assume n,
  induction n with n' ih,
  reflexivity,
  apply (congr_arg succ),
  rewrite ih,
  reflexivity,
end

theorem mult_zero_l : ∀ n : ℕ , 0 * n = 0 :=
begin
  assume n,
  induction n with n' ih,
  reflexivity,
  dsimp[(*), mul],
  rewrite ih,
  reflexivity,
end 

theorem mult_zero_r : ∀ n : ℕ , n * 0 = 0 :=
begin
  assume n,
  induction n with n' ih,
  reflexivity,
  dsimp[(*),mul],
  reflexivity,
end


theorem mult_distr_r :  ∀ l m n : ℕ , l * (m + n) = l * m + l * n :=
begin
  assume l m n,
  induction n with n' ih,
  dsimp [(+),add],
  apply congr_arg,
  reflexivity,

  induction l with l' ih2,
  rewrite mult_zero_l,
  rewrite mult_zero_l,
  rewrite mult_zero_l,
  reflexivity,

  apply (congr_arg succ),
  rewrite ih,
  rewrite add_assoc,
end


theorem mult_distr_l :  ∀ l m n : ℕ , (m + n) * l = m * l + n * l :=
begin
  assume l m n,
  induction l with l' ih3,
  reflexivity,

  dsimp[(*),mul],   
  rewrite ih3,
  
  rewrite add_assoc,
  rewrite (add_comm (n * l') (m + n)),
  rewrite ← add_assoc,
  rewrite ← add_assoc,
  rewrite (add_comm (n * l') n),
  rewrite ← add_assoc,
end


theorem mult_assoc : ∀ l m n : ℕ , (l * m) * n = l * (m * n) :=
begin
  assume l m n,
  induction n with n' ih2,
  reflexivity,

  induction l with l' ih,
  rewrite mult_zero_l,
  rewrite mult_zero_l,
  rewrite mult_zero_l,

  dsimp[(*), mul],
  rewrite ih2,
  rewrite mult_distr_r,
end

lemma helper : ∀ m n :ℕ , succ n * m = n * m + m  :=
begin
  assume m n,
  induction m with m' ih,
  reflexivity,
  dsimp[(*),mul],
  apply congr_arg succ,
  rewrite ih,
  rewrite (add_comm  (n * m') m' ),
  rewrite (add_comm (n * m' + n) m'),
  rewrite ← add_assoc,
end

theorem mult_comm :  ∀ m n : ℕ , m * n = n * m :=
begin
  assume m n,
  induction n with n' ih,
  dsimp[(*),mul],
  rewrite mult_zero_l,
  dsimp[(*),mul],
  rewrite ih,
  rewrite helper,
end

end ex05_01

namespace ex05_2
-- part 2
-- we define ≤ as follows
open nat 

def le(m n : ℕ) : Prop :=
  ∃ k : ℕ , k + m = n

local notation x ≤ y := le x y
local notation x ≥ y := le y x

-- and we have shown that it is a preorder, i.e. reflexive and transitive:
-- note that we have used the ring tactic to do all the equational reasoning:
example : ∀ m n : nat, succ m = succ n → m = n :=
begin
  assume m n h,
  injection h,
end

theorem le_refl : ∀ x : ℕ , x ≤ x :=
begin
  assume x,
  existsi 0,
  ring,
end

theorem le_trans : ∀ x y z : ℕ , x ≤ y → y ≤ z → x ≤ z :=
begin
  assume x y z xy yz,
  cases xy with k p,
  cases yz with l q,
  existsi (k+l),
  rewrite← q,
  rewrite← p,
  ring,
end

-- Your task is to show that ≤ is antisymmetric, and hence a *partial order*
-- you are allowed to use the ring tactic.
-- Yes, you may need some lemmas!
axiom add_succ_lem : ∀ m n : ℕ, succ m + n = succ (m + n)

lemma leq_meaning : ∀ x  y :ℕ , x ≤ y → x =y ∨ succ x ≤  y :=
begin
  assume x y yx,
  dsimp[le]at yx,
  cases yx with a h,
  induction a with a' ih,
  left,
  rewrite ← h,
  ring,

  right,
  dsimp[le],
  existsi a',
  calc
    a' + succ x = succ (a'+ x) : by reflexivity
    ... = succ a' + x: by rewrite add_succ_lem
    ... = y : by exact h,
end

lemma leq_absurd : ∀ x:ℕ , ¬ (succ x ≤ x) :=
begin
  assume x,
  assume h,
  cases h with a g,
  induction x with x' ih,
  contradiction,
  apply ih,
  injection g,
end

theorem anti_sym : ∀ x y : ℕ , x ≤ y → y ≤ x → x = y :=
begin
  assume x y xy yx, 
  have aux : x =y ∨ succ x ≤  y,
  apply leq_meaning,
  exact xy,

  cases aux,
  exact aux,

  have p : succ x ≤ x,
  apply le_trans,
  exact aux,
  exact yx,
  have np : ¬ (succ x ≤ x),
  apply leq_absurd,
  contradiction,
end

end ex05_2