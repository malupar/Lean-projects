/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic-- imports all the Lean tactics

namespace Section3sheet3

/-

# More on functions

Another question on the Imperial introduction to proof problem sheet on functions
is "If `f : X → Y` and `g : Y → Z` and `g ∘ f` is injective, is it true that `g` is injective?"
This is not true. A counterexample could be made by letting `X` and `Z` have one element,
and letting `Y` have two elements; `f` and `g` are then not hard to write down. Let's
see how to do this in Lean by making inductive types `X`, `Y` and `Z` and functions
`f` and `g` which give an explicit counterexample.

-/
-- Let X be {a}
inductive X : Type
  | a : X

-- in fact the term of type X is called `X.a`.
-- Let Y be {b,c}
inductive Y : Type
  | b : Y
  | c : Y

inductive Z : Type
  | d : Z

-- Define f by f(X.a)=Y.b
def f : X → Y
  | X.a => Y.b

-- define g by g(Y.b)=g(Y.c)=Z.d
def g : Y → Z
  | Y.b => Z.d
  | Y.c => Z.d

-- Here `Z` only has one term, so if `z : Z` then `cases z` only produces one goal,
-- namely "what you get if you change `z` to `Z.d`".
example (z : Z) : z = Z.d := by
  cases z
  rfl

theorem Yb_ne_Yc : Y.b ≠ Y.c := by
  intro h
  -- x ≠ y is definitionally equal to (x = y) → False
  cases h

-- no cases when they're equal!
theorem gYb_eq_gYc : g Y.b = g Y.c := by
  cases g Y.b
  rfl

open Function

theorem gf_injective : Injective (g ∘ f) := by
  intro a b
  cases a
  cases b
  intro h
  rfl

-- This is a question on the IUM (Imperial introduction to proof course) function problem sheet.
-- Recall that if you have a hypothesis of the form `h : ∀ A, ...`, then `specialize h X`
-- will specialize `h` to the specific case `A = X`.
example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Injective (ψ ∘ φ) → Injective ψ := by
  intro h
  specialize h X Y Z f g
  have hInj : Injective (g ∘ f) := by apply gf_injective
  apply h at hInj
  specialize hInj gYb_eq_gYc
  apply Yb_ne_Yc at hInj
  exact hInj

-- Below is another one. Let's make a sublemma first.
theorem gf_surjective : Surjective (g ∘ f) := by
  intro b
  use X.a

-- Another question from IUM
example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Surjective (ψ ∘ φ) → Surjective φ := by
  intro h
  specialize h X Y Z f g
  have hSur : Surjective (g ∘ f) := by apply gf_surjective
  apply h at hSur
  specialize hSur Y.c
  cases' hSur with x hx
  cases x
  have hNX : Y.b ≠ Y.c := by apply Yb_ne_Yc
  apply hNX at hx
  exact hx

end Section3sheet3
