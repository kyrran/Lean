/-
COMP2009-ACE

Exercise 02 (Propositional logic)

    This exercise has 2 parts. In the 1st part you are supposed to
    formally define what certain relation bewteen humans are (like
    Father, brother-in-law etc). Here we use Lean only as a syntax  and type checker. 
    In the 2nd part we play logic poker again :-) but this time for
    predicate logic. 

    You are only allowed to use the tactics introduced in the lecture
    (i.e. assume, exact, apply, constructor, cases, left, right, have, 
    trivial, existsi, reflexivity, rewrite)

    Please only use the tactics in the way indicated in the script,
    otherwise you may lose upto 2 style points. 

-/

namespace family

-- Given the following type, predicates and relations:

constant People : Type
constants Male Female : People → Prop
-- Male x means x is male
-- Female x means x is fmeale
constant Parent : People → People → Prop
-- Parent x y means x is a parent of y
constant Married : People → People → Prop
-- Married x y means x is married to y

/-
Define the following relations (People → People → Prop) 
using the predicates and relations above:

- Father x y = x is the father of y
- Brother x y = x is the brother of y
- Grandmother x y = x is the grandmother of y
- FatherInLaw x y = x is the father-in-law of y
- SisterInLaw x y = x is the sister in law of y
- Uncle x y = x is the uncle in t

If you are not sure about the definition of these terms, check them 
in wikipedia. If there is more than one option choose one.
-/

/- As an example: here is the definition of Father: -/

def Father (x y : People) : Prop
  := Parent x y ∧ Male x

-- insert your definitions here
def Sibling (x y :People) :Prop
  := (x ≠ y) ∧ ( ∃ h : People, Parent h x ∧ Parent h y )
  
def Brother (x y : People) : Prop
--two person have same parent
  := Male x ∧ Sibling  x y 

def Mother (x y : People) : Prop
  := Parent x y ∧ Female x

def Grandmother (x y : People) : Prop
--the mother of one's father or mother.
  := ∃ z : People, Mother x z ∧ Parent z y 

def FatherInLaw (x y : People) : Prop 
--the father of one's husband or wife.
  := ∃ h : People, Father x h ∧  Married y h

def SisterInLaw (x y : People) : Prop 
--the wife of one's brother or sister
  := Female x ∧ (∃ z : People, Married x z ∧ Sibling z y )

def Uncle (x y : People) : Prop
--the brother of one's father or mother
  := ∃ z : People, Brother x z ∧ Parent z y
  
end family

namespace poker
/-
   We play the game of logic poker - but this time with predicate logic :-)

    You have to classify the propositions into
    a) provable intuitionistically (i.e. in plain lean)
    b) provable classically (using em : P ∨ ¬ P or raa : ¬¬ P → P).
    c) not provable classically.
    and then you have to prove the propositions in a) and b) accordingly.

    Here is how you score:
    We start with 10 points :-)
    For any proposition which you didn't classify correctly (or not at all)
    you loose 1 point. :-(
    For any proposition which is provable but you didn't prove you loose
    1 point. :-(
    We stop subtracting points at 0. :-)

    Write the classification as a comment using -- after the proposition.

    You are only allowed to use the tactics introduced in the lecture
    (i.e. assume, exact, apply, constructor, cases, left, right, have, 
    trivial, existsi, reflexivity, rewrite)

    Please only use the tactics in the way indicated in the script,
    otherwise you may lose upto 2 style points. 

    For propositions classified into c) just keep "sorry," as the proof.
-/

variable A : Type
variables PP QQ : A → Prop
variables RR : A → A → Prop
variables P Q R : Prop

open classical

theorem raa : ¬ ¬ P → P := 
begin
  assume nnp,
  cases (em P) with p np,
    exact p,
    have f : false,
      apply nnp,
      exact np,
    cases f,
end

theorem ex01 : (∀ x:A, ∃ y : A , RR x y) → (∃ y : A, ∀ x : A, RR x y) :=
begin-- c)  not provable classically
  sorry,
end

theorem ex02 :  (∃ y : A, ∀ x : A, RR x y) → (∀ x:A, ∃ y : A , RR x y) :=
begin --a) provable intuitionistically
  assume h,
  assume x,
  cases h with y rr,
  existsi y,
  apply rr,
end

theorem ex03 : ∀ x y : A, x = y → RR x y → RR x x :=
begin --b) provable classically
  assume a b pp,
  assume hab,
  apply raa,
  assume h,
  have h1: ¬ RR a b,
  rewrite ← pp,
  exact h,
  apply h1,
  exact hab,
end

theorem ex04 : ∀ x y z : A, x ≠ y → x ≠ z → y ≠ z :=
begin -- c) not provable classically
  sorry,
end

theorem ex05 : ∀ x y z : A, x = y → x ≠ z → y ≠ z :=
begin --a) provable intuitionistically
  assume x y z pp,
  assume xz,
  rewrite ← pp,
  exact xz,
end

theorem ex06 : ∀ x y z : A, x ≠ y → (x ≠ z ∨ y ≠ z) :=
begin --b) provable classically
  assume x y z xy,
  cases(em (y=z)) with xz nxz,
  left,
  rewrite ← xz,
  exact xy,
  right,
  assume yz,
  apply nxz,
  exact yz,
end

theorem ex07 : ¬ ¬ (∀ x : A, PP x) → ∀ x : A, ¬ ¬ PP x :=
begin --a) provable intuitionistically
  assume h,
  assume a npp,
  apply h,
  assume pp,
  apply npp,
  apply pp,
end

theorem ex08 : (∀ x : A, ¬ ¬ PP x) → ¬ ¬ ∀ x : A, PP x :=
begin --b) provable classically
  assume nnpp,
  assume npp,
  apply npp,
  assume a,
  apply raa,
  assume nppa,
  apply nnpp,
  exact nppa,
end

theorem ex09 : (∃ x : A, true) → (∃ x:A, PP x) → ∀ x : A,PP x :=
begin ---c) not provable classically
  sorry
end


theorem aux_thm: (¬ ∀ (x : A), PP x) →   ∃ x : A, ¬ PP x :=
begin
    assume h,
    apply raa,
    assume ng,
    apply h,
    assume x,
    apply raa,
    assume np,
    apply ng,
    existsi x,
    exact np,
end

theorem ex10 : (∃ x : A,  true) → (∃ x:A, (PP x → ∀ x : A,PP x)) :=
begin ---b) provable classically
  assume atr,
  cases atr with a tr,
  cases em (∀ x : A, PP x) with app napp,
  existsi a,
  assume ppa,
  exact app,

  have h :(∃ x: A, ¬ PP x),
  apply aux_thm,
  exact napp,

  cases h with a1 npp,
  existsi a1,
  assume ppa1,
  have f: false,
  apply npp,
  exact ppa1,
  cases f,
end

end poker
