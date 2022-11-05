import tactic
set_option pp.structure_projections false

theorem binom : ∀ x y : ℕ, (x + y)^2 = x^2 + 2*x*y + y^2 :=
begin
  assume a b,
  ring,
end

set_option pp.structure_projections false
open nat

--multiplication
def mul : ℕ → ℕ → ℕ
| m 0     := 0
| m (succ n) := (mul m n) + m

-- m * 0 = n
-- m * (n + 1) = m * n + m

local notation m * n := mul m n

#reduce mul 5 3



----ring
--semi ring
/--
A semiring is a set together with two binary operators S(+,*) satisfying the following conditions:

1. Additive associativity: For all a,b,c in S, (a+b)+c=a+(b+c),

2. Additive commutativity: For all a,b in S, a+b=b+a, --left and right neutral

3. Multiplicative associativity: For all a,b,c in S, (a*b)*c=a*(b*c),

4. Left and right distributivity: For all a,b,c in S, a*(b+c)=(a*b)+(a*c) and (b+c)*a=(b*a)+(c*a).

--/

--ring with 4. Additive inverse: For every a in S there exists -a in S such that a+(-a)=(-a)+a=0,

/--
The field axioms are generally written in additive and multiplicative pairs.

name	addition	multiplication
associativity	(a+b)+c=a+(b+c)	(ab)c=a(bc)
commutativity	a+b=b+a	ab=ba
distributivity	a(b+c)=ab+ac	(a+b)c=ac+bc
identity	a+0=a=0+a	a·1=a=1·a
inverses	a+(-a)=0=(-a)+a	aa^(-1)=1=a^(-1)a if a!=0
--/

/--
Natural numbers (ℕ)	Semiring
Integers (ℤ)	Ring
Rational numbers (ℚ)	Field
Real numbers (ℝ)	Complete Field
Complex numbers (ℂ)	Algebraically complete Field
--/



def exp : ℕ → ℕ → ℕ
| n zero := 1
| n (succ m) := exp n m * n



--order ≤ , m ≤ n
def le (m n : ℕ) : Prop := ∃ k : ℕ , k + m = n

local notation x ≤ y := le x y
local notation x ≥  y := le x y

theorem le_refll : ∀ x : ℕ , x ≤ x :=
begin
   assume x,
   dsimp[(≤),le], 
   existsi 0,
   ring,
end

theorem le_transs : ∀ x y z : ℕ , x ≤ y → y ≤ z → x ≤ z :=
begin
   assume x y z ,
   assume xy yz,
   dsimp[(≤ ),le],
   dsimp[(≤ ),le] at xy,
   dsimp[(≤ ),le] at yz,

   cases xy with k p, -- ≤ is an exist statement
   cases yz with l q,
   existsi (k+l),
   rewrite← q,
   rewrite← p,
   ring,
end

--partial order: a partial order is a relation which is reflexive, transitive and antisymmetric. 
--reflexive (∀ x : A, x≤x),
--transitive (∀ x y z : A, x≤y → y≤z → x≤z)
--antisymmetry (∀ x y : ℕ , x ≤ y → y ≤ x → x = y)









-- decidability
-- x,y : ℕ 
-- x = y : Prop
set_option pp.structure_projections false

example: 3=3 :=
begin
  reflexivity,
end 

example : ¬ (3 = 5) :=
begin
  assume n,
  have h : 2=4,
  injection n,
  have k : 1=3,
  injection h,
  have l : 0 = 2,
  injection k,
  contradiction,
end

example : ¬ (3 = 5) :=
begin
  assume n,
  cases n,
end

open nat

def eq_nat : ℕ → ℕ → bool 
| zero zero := tt
| zero (succ n) := ff
| (succ m) zero := ff
| (succ m) (succ n) := eq_nat m n

#reduce eq_nat 3 3

#reduce eq_nat 3 5 

lemma eq_nat_1 : ∀ m : ℕ, eq_nat m m = tt :=
begin
  assume m,
  induction m with n' ih,
  dsimp [eq_nat],
  reflexivity,
  dsimp [eq_nat],
  exact ih,
end

lemma eq_nat_2 : ∀ m n : ℕ, eq_nat m n = tt → m = n :=
begin
  assume m,
  induction m with m' ih_m,
  assume n,
  cases n, -- n be 0 and succ n
  assume h,
  reflexivity,

  assume h,
  dsimp [eq_nat] at h,
  contradiction,

  assume n h,
  cases n,
  dsimp [eq_nat] at h,
  contradiction,
  have g : m'=n,
  apply ih_m,
  dsimp [eq_nat] at h,
  exact h,
  rewrite g,
end    
  
theorem eq_nat_dec : ∀ m n : ℕ, m=n ↔ eq_nat m n = tt :=
begin
  assume m n,
  constructor,
  assume e,
  rewrite e,
  apply eq_nat_1,
  apply eq_nat_2,
end 

-- ok equality for natural numbers is decidable
-- are all relations decidable, are all equalities decidable?

/--
Certainly not all relations or predicates are decidable. An example for an undecidable relation is equality of functions that is given f g : ℕ → ℕ is f = g? Two functions are equal iff they agree on all arguments f = g ↔ ∀ n :ℕ,f n = g n. It is clear that we cannot decide this, i.e. define a function into bool, because we would have to check infinitely many inputs.
--/

-- there are undecidable predicates
-- TM : Set
-- Halts : TM → Prop
-- halts : TM → bool -- there is no such function, see Halting problem

-- f g : ℕ → ℕ
-- f = g ?
-- ∀ n : ℕ, f n = g n
-- eq_fun : (ℕ → ℕ) → (ℕ → ℕ) → bool -- is undecidable
-- halts_after_n_steps : TM → ℕ → bool -- is definable
-- Halts tm := ¬ (halts_after_n_step = λ x, ff)

-- h : succ m = succ n
-- ⊢ m = n
-- injection h,

-- a = b
-- calc 
--   a = c : by ..
--   ... = d : by ..
--   ... = b : by ..


