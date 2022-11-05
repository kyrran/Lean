--lecture on propositional logic
variables P Q R : Prop

--proposition :definitive statement which we may be able to prove
--propositional connectives

#check P ∧ Q --and, conjunction 
#check P ∨ Q -- or, disconjunction 
#check P → Q -- if-then, implication
#check ¬ P --not, negation
-- ¬ P = P → false
#check P ↔ Q --if and only if, equivalence
#check false
#check true

--P → (Q→ R)

--tautologies: If we are proving a statement containing propositional variables then this means that the statement is true for all replacements of the variables with actual propositions. We say it is a tautology.

theorem I: P → P :=
begin
  assume h,
  exact h,
end

theorem C : (P → Q) → (Q → R) → (P → R) :=
begin
  assume p2q,
  assume q2r,
  assume p,
  apply q2r, --q->r, then r can be replaced by q, goal is q
  apply p2q, --goal is p
  exact p,
end

theorem swap : (P → Q → R) → (Q → P → R) :=
begin
  assume left,
  assume lq,
  assume lp,
  apply left, -- two goals
  exact lp,
  exact lq,
end


#print I
#print C
#print swap

/--
  ASSUME => to prove = right after |-
  APPLY => to use
  EXACT
--/













example : P → Q → P ∧ Q :=
begin
  assume p q, -- p → q → r
  constructor, -- turns goal into two goals
  exact p,
  exact q,
end


theorem comAnd : P ∧ Q → Q ∧ P :=
begin
  assume pq,
  cases pq with p q, -- p ∧ q becomes p and q
  constructor,
  exact q,
  exact p,
end

theorem curry: (P → Q → R) ↔ (P ∧ Q → R) :=
begin
  constructor, -- left to right, and right to left
  assume lhs,
  assume pq,
  cases pq with p q,
  apply lhs, -- two goals become three goals necuase p q r in consequence
  exact p,
  exact q,

  assume rhs,
  assume p q,
  apply rhs, -- two goals become three goals necuase p q r in consequence
  constructor,
  exact p,
  exact q,
end 

/--
  constuctor => to prove conjunction
  cases h with x y => to use conjunction
--/













--disconjunction, or, ∨ 
example: P → P ∨ Q :=
begin
  assume p,
  left, --- either prove P or we can prove Q
  exact p,
end

example: Q → P ∨ Q :=
begin
  assume q,
  right, --- either prove P or we can prove Q
  exact q,
end

theorem case_lem : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  assume pr qr pq,
  cases pq with p q, --seperate two cases, either p or q
  apply pr,
  exact p,

  apply qr,
  exact q,
end

/--
  to prove disconjunction -> left, right
  to use an assumption of disconjunction -> cases h with x y
--/

example: P ∨ Q → Q ∨ P :=
begin
  assume pq,
  cases pq with p q,
  right,
  exact p,
  left,
  exact q,
end













example : true :=
begin
  trivial, --/constructor -- can only prove
end

--efq, Ex falso quod libet 
--from false follows everything.
-- If pigs can fly then I am the president of America 
theorem efq: false → P :=
begin
  assume f,
  cases f, -- can only use
end

-- ¬P = P → false 
theorem contr: ¬ (P ∧ ¬ P) :=
begin
  assume pnp, --goal turns to false
  cases pnp with p np,
  apply np, -- because ¬P = P → false 
  exact p,
end

/--
  to prove true : trival
  to use false: cases (no with)
--/












--The truth based logic is called classical logic
--evidence based one is called intuitionistic logic

--de morgen law
/--
  ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q
  ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q
--/
theorem dm1 : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
-- p ↔ q = p → q ∧ q → p 
begin
  constructor, --to prove ∧ use constructor
  assume npq,
  constructor,
  assume p, --not p = p -> false
  apply npq,
  left,
  exact p,

  assume q,
  apply npq,
  right,
  exact q,

  assume npnq,
  assume pq,
  cases npnq with np nq, --to use and , cases with x y
  cases pq with p q, --to use or , cases with x y
  apply np,
  exact p,

  apply nq,
  exact q,
end


--law of exclude middle : P ∨ ¬ P 
--em = excluded middle
--the third is not given
open classical
#check em P

--It is not the case that I have a cat and that I have a dog
--I don’t have a cat or I don’t have a dog ?
--NO
theorem dm2 : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := -----em
begin
  constructor, -- to prove and
  assume npq,
  cases (em P) with p np, -- add one more case
  right,
  assume q,
  apply npq,
  constructor,
  apply p,

  apply q,
  
  left,
  apply np,

  assume npnq pq,
  cases npnq with np nq,
  apply np,
  cases pq with p q,
  exact p,

  apply nq,
  cases pq with p q,
  exact q,
end
-- raa equivalent to the principle of excluded middle
--indirect proof 
theorem raa : ¬ ¬ P → P :=
begin
  assume nnp,
  cases (em P) with p np,
  exact p,
  apply efq, -- false -> P 
  apply nnp,
  exact np
end

theorem nn_em : ¬ ¬ (P ∨ ¬ P) :=
begin
  assume npnp,
  apply npnp,
  right,
  assume p,
  apply npnp,
  left,
  exact p
end

--em and raa are equivalent 














--predicate logic
--Predicate logic extends propositional logic, we can use it to talk about objects and their properties.
--types (sets)
#check ℕ -- \nat--\bn
#check list ℕ 
#check bool
variables A B C : Type


--predicates
--Prime: ℕ → Prop
--Prime 3 : Prop -- 3 is a prime number

--A = type of students
--isClever : A → Prop

--relations: leq : ℕ -> (ℕ → Prop)
--we write x ≤ y for leq x y
-- 3 ≤ 4 : Prop
--leq 3 4 : Prop

variables PP QQ : A → Prop --two predicates PP QQ
--PP x means x is clever
--QQ x means x is funny

--quantifiers
-- ∀ : for all, universal quantifier
-- ∃ : exists, existential quantifier
-- (∀ x : A, PP x) all students are clever
-- (∃ x : A, PP x) there is a clever student


--equality
-- a b : A , we can form a = b: Prop, means a is equal to b

--proofs
--∀ x : A, PP x
--how to prove: assume h
--how ro use: apply h --h : ∀ x : A, PP x, and we want to prove PP a


--If all students are clever 
--then if all clever students are funny 
--then all students are funny.
example : (∀ x : A, PP x) → (∀ y : A, PP y → QQ y) → ∀ z : A , QQ z :=
begin
  assume h g,
  assume george, --using george as an example of z
  apply g, --pp y -> qq y => pp george
  apply h, --pp x 
end

--all students are clever and funny is the same as saying that all students are clever and all students are funny.
example : (∀ x : A, PP x ∧ QQ x) ↔ (∀ x : A , PP x) ∧ (∀ x : A, QQ x) :=
begin
  constructor,
  assume h,
  constructor,
  assume y,
  have pq : PP y ∧ QQ y, --change the goal? add one more assumption?
  apply h, --one goal eliminated
  cases pq with p q,
  exact p, --exact the same, use exact

  assume y,
  have pq2 : PP y ∧ QQ y, --change the goal?
  apply h, --one goal eliminated
  cases pq2 with p q,
  exact q, 

  assume g,
  cases g with pp qq,
  assume z,
  constructor,
  apply pp, --x and z are same format but not same element, use apply
  apply qq,
end

-- ∃ x : A, PP x
--how to prove: existsi a, to show PP a
-- h : ∃ x : A, PP x
--how to use: cases h with a p, given a : A, p : PP a

--If there is a clever student and all clever students are funny then there is a funny student.
example : (∃ x : A, PP x)
  → (∀ y : A, PP y → QQ y)
  → ∃ z : A , QQ z :=
begin
  assume g h,
  cases g with a p, -- g : ∃ (x : A), PP x => a : A, p : PP a
  existsi a,
  apply h,
  exact p,
end

--There is a student who is clever or funny is the same as saying there is a student who is funny or there is a student who is clever.
example : (∃ x : A, PP x ∨ QQ x)
              ↔ (∃ x : A , PP x) ∨ (∃ x : A, QQ x) :=
begin
  constructor,
  assume h,
  cases h with a g,
  cases g with p q,
  left,
  existsi a, -- there is already an a as variable on the top
  exact p,
  right,
  existsi a,
  exact q,

  assume h,
  cases h with p q,
  cases p with a pa, -- have to create a variable at first
  existsi a,
  left,
  exact pa,
  cases q with a q,
  existsi a,
  right,
  exact q,
end


example : (∀  x : A, PP x ∨ QQ x)
              ↔ (∀  x : A , PP x) ∨ (∀ x : A, QQ x) :=
begin
  sorry
end
/--
(∀  x : A , PP x) ∨ (∀ x : A, QQ x) -> (∀  x : A, PP x ∨ QQ x)
--/

example : (∃ x : A, PP x ∧  QQ x)
              ↔ (∃ x : A , PP x) ∧ (∃ x : A, QQ x) :=
begin
  sorry
end
/--
(∃ x : A, PP x ∧  QQ x)
              →  (∃ x : A , PP x) ∧ (∃ x : A, QQ x) 
--/


--have aux: P
--first i have to prove P
--then I can use aux : P











variable People : Type

variable Loves : People → People → Prop

--everybody loves somebody
--predicate logic
#check ∀ x : People, ∃ y : People, Loves x y

--there is somebody who is loved by everyone
#check ∃ y : People, ∀ x : People, Loves x y

example: (∃ y : People, ∀ x : People, Loves x y) → (∀ x : People, ∃ y : People, Loves x y) :=
begin
  assume h,
  assume g,
  cases h with a alla, --there is no other object for exist to use, we can only use exist to move on
  existsi a,
  apply alla,
end

--everybody loves themselves
#check ∀ x : People, Loves x x

--everybody loves at most one person
#check ∀ x y z: People, Loves x y → Loves x z → y = z

--everybody only loves themselves
#check ∀ x y : People, Loves x y → x = y

example: (∀ x : People, Loves x x) → (∀ x y z: People, Loves x y → Loves x z → y = z) → (∀ x y : People, Loves x y → x = y) :=
begin
  assume h g,
  assume a b,
  assume ab,
  apply g, --question mark here
  apply h, --everybody loves themselves
  exact ab,
end

--currying equivalent
-- (P ∧ Q → R) ↔ (P→ Q → R)
--((∃ x : A, PP x) → R)  ↔ (∀ x : A , PP x → R)
theorem curry_pred : ((∃ x : A, PP x) → R)  ↔ (∀ x : A , PP x → R)  :=
begin
  constructor,
  assume h,
  assume a,
  assume g,
  apply h,
  existsi a,
  exact g,

  assume h g,
  cases g with a ppa,
  apply h,
  exact ppa, ---? question mark here
  --apply ppa,
end

--equality
example : ∀ x : A, x = x :=
begin
  assume h,
  reflexivity,
end

example:  ∀ x y : A, x = y → PP y → PP x :=
begin
  assume a b,
  assume h,
  assume g,
  rewrite h, --change the goal using equality
  exact g,
end

example:  ∀ x y : A, x=y → PP x → PP y :=
begin
  assume a b,
  assume h,
  assume g,
  rewrite ← h, -- another direction of equality, from right to left
  exact g,
end


/--
  Equality is an equivalence relation, it mens that it is

  reflexive (∀ x : A, x=x),
  symmetric (∀ x y : A, x=y → y=x)
  transitive (∀ x y z : A, x=y → y=z → x=z)
--/

theorem sym_eq : ∀ x y : A, x = y → y=x :=
begin
  assume x y p,
  rewrite p, ---automatically uses reflexivity
end

theorem trans_eq : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z,
  assume xy yz,
  rewrite xy,
  exact yz,
end
/--equality
  to prove: reflexivity
  to use: rewrite h && rewrite ← h
--/
example : ∀ x y : A, x=y → y=x :=
begin
  assume x y p,
  symmetry,
  exact p,
end

example : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z xy yz,
  transitivity, --x = ? = z
  exact xy,
  exact yz,
end

example : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z xy yz,
  calc
    x = y   : by exact xy
    ... = z : by exact yz, -- last expression of the previous line, in this case y.
end












--de morgan for propositional logic
-- ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q
-- ¬ (∃ x : A, PP x) ↔ ∀ x : A, ¬ PP x
-- ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q
-- ¬ (∀ x : A, PP x) ↔ ∃ x : A, ¬ PP x 
example : ¬ P ∨ ¬ Q → ¬ (P ∧ Q):=
begin
  assume h,
  assume pq,
  cases pq with p q,
  cases h with np nq,
  apply np,
  exact p,

  apply nq,
  exact q,
end


theorem dm1_pred : ¬ (∃ x : A, PP x) ↔ ∀ x : A, ¬ PP x :=
begin
  constructor,
  assume h,
  assume a,
  assume ppa,
  apply h,
  existsi a,
  exact ppa,

  assume h,
  assume ppx,
  cases ppx with a ppa,
  apply h,
  exact ppa,
end

--classical logic needed
theorem dm2_pred : ¬ (∀ x : A, PP x) ↔ ∃ x : A, ¬ PP x :=
begin
  constructor,
  assume h,
  apply raa, --!!q = q, add !! to goal
  assume npp,

  apply h,
  assume a,
  apply raa,---double time
  assume nppa,
  apply npp,
  existsi a,
  exact nppa,

  assume h,
  assume nppx,
  cases h with a nppa,
  apply nppa,
  apply nppx,
end
/--
  in every non-empty pub, there is one person such that if this person drinks then everybody is drinking. true
  A = prople in the pub
  PP x = x is drinking
--/

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

theorem drinker: (∃ x : A, true) → ∃ x : A, PP x → ∀ x : A, PP x :=
--(∃ x : A,  true) → (∃ x:A, (PP x → ∀ x : A,PP x)) :=
begin
  ---b) provable classically
  assume atr,
  cases atr with a tr,
  cases em (∀ x : A, PP x) with app napp,  --create two assumptions, P and ¬ P
  existsi a,
  assume ppa,
  exact app,

  have h :(∃ x: A, ¬ PP x),  --one changes goal, one adds as assumption
  apply aux_thm, --we know napp and current goal are equal
  exact napp,

  cases h with a1 npp,
  existsi a1,
  assume ppa1,
  have f: false,
  apply npp,
  exact ppa1,

  cases f, --to use false
end

theorem ex09 : (∃ x : A, true) → (∃ x:A, PP x) → ∀ x : A,PP x :=
begin ---c) not provable classically
  sorry
end
