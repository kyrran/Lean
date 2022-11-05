/-
COMP2009-ACE

Exercise 02 (Propositional logic)

   We play the game of logic poker :-)

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
    (i.e. assume, exact, apply, constructor, cases, left, right, have, trivial)

    Please only use the tactics in the way indicated in the script,
    otherwise you may lose upto 2 style points. 

    For propositions classified into c) just keep "sorry," as the proof.
-/

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

theorem e01 : (P → Q) → (R → P) → (R → Q) := 
---a)  provable intuitionistically
begin
  assume pq rp r,
  apply pq,
  apply rp,
  exact r,
end

theorem e02 : (P → Q) → (P → R) → (Q → R) :=
---c) not provable classically
begin
  sorry,
end

theorem e03 : (P → Q) → (Q → R) → (P → R) :=
--a) provable intuitionistically
begin
  assume pq qr pr,
  apply qr,
  apply pq,
  exact pr,
end

theorem e04 : P → (P → Q) → P ∧ Q :=
--a) provable intuitionistically
begin
  assume p pq,
  constructor,
  exact p,
  apply pq,
  exact p,
end

theorem e05 : P ∨ Q → (P → Q) → Q :=
--a) provable intuitionistically
begin
  assume pq,
  assume p2q,
  cases pq with p q,
  apply p2q,
  exact p,
  exact q,
end

theorem e06 : (P → Q) → ¬ P ∨ Q :=
--b) provable classically
begin
  assume pq,
  cases (em P) with p np,
  right,
  apply pq,
  exact p,
  left,
  exact np,
end


theorem e07 : (¬ P ∨ Q) → P → Q :=
--a) provable intuitionistically
begin
  assume npq p,
  cases npq with np q,
  have h: P ∨ Q,
  left,
  exact p,
  have h: false,
  apply np,
  exact p,
  cases h,
  exact q,
end


theorem e08 : ¬ (P ↔ ¬ P) :=
--b) provable classically
begin
  assume pnp,
  cases pnp with pnp npp,
  cases (em P) with p np,
  cases (em ¬ P) with np1 p1,
  apply np1,
  exact p,
  apply p1,
  apply pnp,
  exact p,
  apply np,
  apply npp,
  exact np,
end


theorem e09 : ¬ P ↔ ¬ ¬ ¬ P :=
---a) provable intuitionistically
begin
  constructor,
  assume np,
  assume nnp,
  apply nnp,
  exact np,
  assume nnnp,
  assume p,
  apply nnnp,
  assume np2,
  apply np2,
  exact p,
end

theorem e10 : ((P → Q) → P) → P :=
--b) provable classically
begin
  assume pqp,
  apply raa,
  assume np,
  apply np,
  apply pqp,
  assume p,
  apply raa,
  assume nq,
  apply np,
  exact p,
end


