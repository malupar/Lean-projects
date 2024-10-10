/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  apply h
  trivial
  done

example : False → ¬True := by
  intro h
  exfalso
  apply h
  done

example : ¬False → True := by
  intro h
  trivial
  done

example : True → ¬False := by
  intro h h2
  apply h2
  done

example : False → ¬P := by
  intro hF hP
  apply hF
  done

example : P → ¬P → False := by
  intro hP hPF
  apply hPF at hP
  apply hP
  done

example : P → ¬¬P := by
  intro hP hPF
  apply hPF hP
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hNQ hP
  apply hPQ at hP
  apply hNQ at hP
  apply hP
  done

example : ¬¬False → False := by
  intro h
  apply h
  intro hF
  apply hF
  done

example : ¬¬P → P := by
  intro hPF
  by_contra hP
  apply hPF at hP
  apply hP
  done

example : (¬Q → ¬P) → P → Q := by
  intro hNQNP  hP
  by_contra hNP
  apply hNQNP at hNP
  apply hNP at hP
  apply hP
  done
