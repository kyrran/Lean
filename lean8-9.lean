

namespace bool

-- inductive bool : Type

#check bool
#check ff
#check tt

--tt,ff are the only elements of bool

def bnot: bool → bool
| ff := tt
| tt := ff

#eval bnot ff --the result #eval
#eval bnot tt

def band : bool → bool → bool
| ff x := ff
--| ff ff := ff
--| ff tt := ff
| tt x := x
--| tt ff := ff
--| tt tt := tt

--tt && x = x
--ff & x = dd
--to use them we use dsimp[(&&),band]
--to use them in an assumption h we use dsimp[(&&),band] at h

def bor: bool → bool → bool
| tt x := tt
| ff x := x

local notation x && y := band x y
local notation x || y := bor x y
--predicate logic that every element of bool is either tt or ff:

example : ∀ x : bool, x=tt ∨ x=ff :=
begin
  assume a,
  cases a, -- a = ff, or a = tt
  right,
  reflexivity, --equal to themselves
  left,
  reflexivity,
end

-- to prove bool : cases

--tt and ff are different

def is_tt : bool → Prop
|ff := false
|tt := true

#reduce is_tt ff


theorem cons : tt ≠ ff  := --- \ne
-- ¬ (tt = ff)
-- (tt = ff) → false
begin
  assume tf,
  change (is_tt ff), -- to use is_tt replaces the current goal with another one that is definitionally the same
  rewrite ← tf,
  dsimp [is_tt], --move it back
  constructor,--trivial,
  --contradiction, 
  --contradiction will solve the current goal if there is an inconsistent assumption like assuming that two different constructors of an inductive type are equal.
end


theorem distr_b : ∀ x y z : bool, x && (y || z) = x && y || x && z :=
begin
  assume a b c,
  cases a, --every a b c is either tt or ff
  --dsimp [band], --eliminate unneccarry part to make it clear
  --dsimp [bor],
  reflexivity,
  
  --dsimp[band],
  reflexivity,
end

theorem dm1_b : ∀ x y : bool, bnot (x || y) = bnot x && bnot y :=
begin
  sorry,
end

theorem dm2_b : ∀ x y : bool, bnot (x && y) = bnot x || bnot y :=
begin
  sorry,
end

-- prop, true, false
-- bool tt ff\

-- (∧) : Prop → Prop → Prop
-- (&&) : bool → bool → bool

theorem and_thm : ∀ x y : bool,  (x && y = tt) ↔ (x = tt) ∧ (y = tt) :=
begin
  assume a b,
  constructor,
  assume h,
  cases a,
  dsimp[(&&),band] at h,
  contradiction,

  constructor,
  reflexivity, 
  exact h, -- b has to be tt if assumption h wotks

  assume g,
  cases g with g1 g2,
  rewrite g1,
  --dsimp
  exact g2,
end

example: ∀ x : bool, ∃ y : bool, y = bnot x  :=
begin
  assume a,
  existsi (bnot a), -- y = bnot a
  reflexivity,
end

example: ∀ y : bool, ∃ x : bool, y = bnot x  :=
begin
  assume y,
  existsi (bnot y), -- y = bnot a
  cases y,
  dsimp[bnot],
  reflexivity,
  dsimp[bnot],
  reflexivity,
end

example :∀ f : bool → bool, ∀ x : bool, ∃ y: bool, y = f x :=
begin
  assume f x,
  existsi (f x), --f(x) but in lean is f x
  reflexivity,
end

def foo (x : bool) : bool := ff
#reduce foo tt
#reduce foo ff

example : ¬ (∀ f : bool → bool, ∀ y : bool, ∃ x: bool, y = f x) :=
begin
  assume f,
  have g : ∀ y : bool, ∃ x: bool, y = foo x,
  apply f,

  have k : ∃ x: bool, tt = foo x,
  apply g,
  cases k with x y,
  dsimp[foo] at y,
  contradiction,
end

--can we always prove either p or not p?
--if we hace only bool, no type variables, no predicate variables, no prosositional variables,,,

end bool