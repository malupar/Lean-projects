/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro hPQ
  exact hPQ.left
  done

example : P ∧ Q → Q := by
  intro hPQ
  exact hPQ.right
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro hPQR hPQ
  apply hPQR
  exact hPQ.left
  exact hPQ.right
  done

example : P → Q → P ∧ Q := by
  intro hP hQ
  exact ⟨hP, hQ⟩
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro hPQ
  exact ⟨hPQ.right, hPQ.left⟩
  done

example : P → P ∧ True := by
  intro hP
  exact ⟨hP, trivial⟩
  done

example : False → P ∧ False := by
  intro hF
  exfalso
  exact hF
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hPQ hQR
  exact ⟨hPQ.left, hQR.right⟩
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro hPQR hP hQ
  apply hPQR
  exact ⟨hP, hQ⟩
  done
