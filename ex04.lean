/-
COMP2009-ACE

Exercise 04 (Bool)

    This exercise has 2+1 parts. 

    The first part is "logic chess" which has slightly different rules
    than logic poker but see below. The 2nd part asks you to define
    implication on booleans and prove it correct. You are not supposed
    to use classical logic for this exercise.

    Part 1+2 count for 80% of the mark (40% each). If you think you should get
    100% and are prepared to put a lot of extra effort in then try
    part 3. But you have been warned. They will be no help with this
    one.  

    You are only allowed to use the tactics introduced in the lecture
    (i.e. assume, exact, apply, constructor, cases, left, right, have, 
    trivial, existsi, reflexivity, rewrite, dsimp, contradiction, calc)

    Please only use the tactics in the way indicated in the script,
    otherwise you may lose upto 2 style points.     

-/

namespace ex04

def bnot : bool → bool 
| tt := ff
| ff := tt 

def band : bool → bool → bool 
| tt b := b
| ff b := ff

def bor : bool → bool → bool 
| tt b := tt
| ff b := b

local notation x && y := band x y
local notation x || y := bor x y

/-
PART I (40%)
============
Logic chess

Unlike logic poker in logic chess there is no guessing. You either
prove the proposition or you prove its negation, for example if the
proposition is true, e.g. 

chx0) ∀ x : bool, x=x

then you just go ahead and prove it -/

theorem chx0 : ∀ x : bool, x=x :=
begin
  assume x,
  reflexivity,
end

/- However, if the proposition is false, e.g.

chx1) ∀ x : bool, x ≠ x

then  you prove its negation -/

theorem chx1 : ¬ (∀ x : bool, x ≠ x) :=
begin
  assume h,
  have g : tt ≠ tt,
  apply h,
  apply g,
  reflexivity,
end

/-
For each of the following proposition either prove them or their negation.

ch01) ∀ x : bool, bnot (bnot x) = x
ch02) ∀ x:bool,∃ y:bool, x ≠ y
ch03) ∃ x:bool,∀ y:bool, x ≠ y
ch04) ∀ x y : bool, x=y ∨ x ≠ y
ch05) ∃ x:bool, x=bnot x
ch06) ∀ x y z : bool, x=y ∨ x=z ∨ y=z
ch07) ∀ y:bool, ∃ x:bool, y = bnot x
ch08) ∀ x y : bool, bnot x = bnot y → x=y
ch09) ∃ b : bool, ∀ y:bool, b && y = y
ch10) ∃ b : bool, ∀ y:bool, b && y = b
-/

-- insert answer here
theorem ch01 : ∀ x : bool, bnot (bnot x) = x  :=
begin
  assume x,
  cases x,
  refl,
  refl,
end

theorem ch02 : ∀ x:bool, ∃ y:bool, x ≠ y  :=
begin
  assume x,
  cases x,
  existsi tt,
  assume h,
  contradiction,
  existsi ff,
  assume h2,
  contradiction,
end

theorem ch03 : ¬ (∃ x:bool,∀ y:bool, x ≠ y)  :=
--to prove its negation
begin
  assume x,
  cases x with x h,
  apply h,
  reflexivity,
end

theorem ch04: ∀ x y : bool, x=y ∨ x ≠ y :=
begin
  assume x y,
  cases x,
  cases y,
  left,
  reflexivity,
  right,
  assume fftt,
  contradiction,
  
  cases y,
  right,
  assume ttff,
  contradiction,
  left,
  reflexivity,
end

theorem ch05: ¬ (∃ x:bool, x = bnot x) :=
--to prove negation
begin
  assume h,
  cases h with x h,
  cases x,
  dsimp[bnot] at h,
  contradiction,
  dsimp[bnot] at h,
  contradiction,
end

theorem ch06: ∀ x y z : bool, x=y ∨ x=z ∨ y=z :=
begin
  assume x y z,
  cases x,
  cases y,
  left,
  reflexivity,

  right,
  cases z,
  left,
  reflexivity,

  right,
  reflexivity,

  cases y,
  cases z,
  right,
  right,
  reflexivity,
  
  right,
  left,
  reflexivity,

  left,
  reflexivity,
end

theorem ch07: ∀ y:bool, ∃ x:bool, y = bnot x :=
begin
  assume y,
  cases y,
  existsi tt,
  reflexivity,
  existsi ff,
  reflexivity,
end

theorem ch08: ∀ x y : bool, bnot x = bnot y → x=y :=
begin
  assume x y,
  assume h,
  cases x,
  cases y,
  reflexivity,
  dsimp[bnot] at h,
  rewrite h,

  cases y,
  dsimp[bnot] at h,
  rewrite h,
  reflexivity,
end

theorem ch09: ∃ b : bool, ∀ y:bool, b && y = y :=
begin
  existsi tt,
  assume y,
  dsimp [(&&),band],
  refl,
end

theorem ch10: ∃ b : bool, ∀ y:bool, b && y = b :=
begin
  existsi ff,
  assume y,
  dsimp [(&&),band],
  refl,
end

/- 
PART II (40%)
=============

Define the operation 

implb :   bool → bool → bool 

by pattern matching on bool and show that it corresponds to
implication on Prop, i.e. prove

theorem implb_ok : ∀ x y : bool , implb x y = tt ↔ (x = tt) → (y = tt) 

-/

-- insert answer here
def implb : bool → bool → bool
| tt y := y
| ff y := tt

theorem implb_ok : ∀ x y : bool , implb x y = tt ↔ (x = tt) → (y = tt) :=
begin
  assume x y,
  constructor,
  assume h1,
  assume xtt,
  cases x,
  contradiction,

  dsimp[implb] at h1,
  exact h1,

  assume xttytt,
  cases x,
  dsimp[implb],
  reflexivity,

  dsimp[implb],
  apply xttytt,
  reflexivity,
end

/-
PART III (20%)
==============

(only for the criminally insane)

Prove the following theorem about functions  bool → bool.

Hint: Use "cases e:b" on a boolean expression b. This also adds
equations "e:b = tt" and "e:b = ff" to the cases.

-/

theorem weird : ∀ f : bool → bool, ∀ x:bool, f (f (f x)) = f x :=
begin
  assume f,
  assume x,
  cases x,
  cases g : f ff,
  rewrite g,
  exact g,

  cases ftt: f tt,
  exact g,

  exact ftt,

  cases o : f (f (f tt)),
  cases r : f tt,
  reflexivity,
  rewrite ← o,
  rewrite r,
  rewrite r,
  exact r,

  cases t : f tt,
  rewrite ← o,
  rewrite t,
  cases w : f ff,
  exact w,
  
  rewrite t,
  reflexivity,  
end

end ex04
