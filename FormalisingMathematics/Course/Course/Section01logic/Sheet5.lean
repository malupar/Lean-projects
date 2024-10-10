/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;>
  · intro h
    rw [h]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ hQR
  rw [hQR] at hPQ
  exact hPQ
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;>
  · intro h
    exact ⟨h.right, h.left⟩
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro h
    exact ⟨h.left.left, ⟨h.left.right, h.right⟩⟩
  · intro h
    exact ⟨⟨h.left, h.right.left⟩, h.right.right⟩
  done

example : P ↔ P ∧ True := by
  constructor
  · intro h
    exact ⟨h, trivial⟩
  · intro h
    exact h.left
  done

example : False ↔ P ∧ False := by
  constructor
  · intro h
    exfalso
    exact h
  · intro h
    exact h.right
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ hRS
  constructor
  · intro hPR
    rw [hPQ] at hPR
    rw [hRS] at hPR
    exact hPR
  · intro hPR
    rw [← hPQ] at hPR
    rw [← hRS] at hPR
    exact hPR
  done

example : ¬(P ↔ ¬P) := by
  intro h
  by_cases hP : P
  · rw [h] at hP
    apply hP
    rw [h]
    exact hP
  · apply hP
    rw [h]
    exact hP
  done
