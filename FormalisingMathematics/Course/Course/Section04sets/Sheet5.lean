/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  constructor
  · intro h
    cases' h with hA hA2
    exact hA
    exact hA2
  · intro h
    constructor
    · apply h

example : A ∩ A = A := by
  ext x
  constructor
  · intro h
    apply h.left
  · intro h
    constructor <;>
    · apply h

example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  · intro h
    apply h.right
  · intro h
    cases h

example : A ∪ univ = univ := by
  ext x
  constructor
  · intro h
    trivial
  · intro h
    exact mem_union_right A h

example : A ⊆ B → B ⊆ A → A = B := by
  intro hAB hBA
  ext x
  constructor
  · apply hAB
  · apply hBA

example : A ∩ B = B ∩ A := by
  ext x
  constructor <;>
  · intro h
    exact ⟨h.right, h.left⟩

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  constructor
  · intro h
    exact ⟨⟨h.left, h.right.left⟩, h.right.right⟩
  · intro h
    exact ⟨h.left.left, ⟨h.left.right, h.right⟩⟩

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  · rintro (hA | hB | hC)
    · left; left; exact hA
    · left; right; exact hB
    · right; exact hC
  · rintro ((hA | hB) | hC)
    left; exact hA
    right; left; exact hB
    right; right; exact hC

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  exact union_inter_distrib_left A B C

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  exact inter_union_distrib_left A B C
