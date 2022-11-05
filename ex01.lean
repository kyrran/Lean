/-
COMP2009-ACE

Exercise 01 (Propositional logic) (10 points)

Prove all the following propositions in Lean. 1 point per exercise.
That is replace "sorry" with your proof. 

You are only allowed to use the tactics introduced in the lecture
(i.e. assume, exact, apply, constructor, cases, left, right, have)

Please only use the tactics in the way indicated in the script,
otherwise you may lose upto 2 style points. 

-/

variables P Q R : Prop

theorem e01 : P → Q → P :=
begin
  assume p q,
  exact p,
end

theorem e02 : (P → Q → R) → (P → Q) → P → R :=
begin
  assume pqr pq p,
  apply pqr,
  exact p,
  apply pq,
  exact p,
end

theorem e03 : (P → Q) → P ∧ R → Q ∧ R :=
begin
  assume pq pr,
  cases pr with p r,
  constructor,
  apply pq,
  exact p,
  exact r,
end

theorem e04 : (P → Q) → P ∨ R → Q ∨ R :=
begin
  assume pq pr,
  cases pr with p r,
  left,
  apply pq,
  exact p,
  right,
  exact r,
end

theorem e05 : P ∨ Q → R ↔ (P → R) ∧ (Q → R) :=
begin
  constructor,
  assume pqr,
  constructor,
  assume p,
  apply pqr,
  left,
  exact p,
  
  assume q,
  apply pqr,
  right,
  exact q,

  assume first second,
  cases first with first_left first_right,
  cases second with c d,
  apply first_left,
  exact c,
  apply first_right,
  exact d,
end

theorem e06 : P → ¬ ¬ P :=
begin
  assume p,
  assume np,
  apply np,
  exact p,
end

theorem e07 : P ∧ true ↔ P :=
begin
  constructor,
  assume pt,
  cases pt with p t,
  exact p,

  assume p2,
  constructor,
  exact p2,
  trivial, 
end

theorem e08 : P ∨ false ↔ P :=
begin
  constructor,
  assume pf,
  cases pf with p f,
  exact p,
  cases f,
  
  assume p2,
  left,
  exact p2,
end

theorem e09 : P ∧ false ↔ false :=
begin
  constructor,
  assume pf,
  cases pf with p f,
  cases f,  

  assume f2,
  cases f2,
  --constructor and then exact also work
end

theorem e10 : P ∨ true ↔ true :=
begin
  constructor,
  assume pt,
  trivial, --cases pt and then exact also work
  assume t2,
  right,
  trivial,
end

