/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro h
  left
  apply h
  done

example : Q → P ∨ Q := by
  intro h
  right
  apply h
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR
  cases' h with hP hQ
  · exact hPR hP
  · exact hQR hQ
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases' h with hP hQ
  · right
    exact hP
  · left
    exact hQ
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro h
    cases' h with hPQ hR
    · cases' hPQ with hP hQ
      · left; apply hP
      · right; left; apply hQ
    · right; right; apply hR
  · intro h
    cases' h with hP hQR
    · left; left; apply hP
    · cases' hQR with hQ hR
      · left; right; apply hQ
      · right; apply hR
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPQ
  cases' hPQ with hP hQ
  · apply hPR at hP; left; apply hP
  · apply hQS at hQ; right; apply hQ
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPR
  cases' hPR with hP hR
  · apply hPQ at hP; left; apply hP
  · right; apply hR
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPR hQS
  constructor
  · intro hPQ
    cases' hPQ with hP hQ
    · rw [hPR] at hP; left; apply hP
    · rw [hQS] at hQ; right; apply hQ
  · intro hPQ
    cases' hPQ with hP hQ
    · rw [← hPR] at hP; left; apply hP
    · rw [← hQS] at hQ; right; apply hQ
  done

-- simplified solution
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPR hQS
  rw [hPR, hQS]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hP; apply h; left; apply hP
    · intro hQ; apply h; right; apply hQ
  · intro h hPQ
    cases' hPQ with hP hQ
    · apply h.left; apply hP
    · apply h.right; apply hQ
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right; intro hQ; apply h; exact ⟨hP, hQ⟩
    · left; apply hP
  · intro h hPQ
    cases' h with hNP hNQ
    · apply hNP; apply hPQ.left
    · apply hNQ; apply hPQ.right
  done
