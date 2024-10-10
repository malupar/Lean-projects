/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-!

# Logic in Lean, example sheet 2 : `True` and `False`

We learn about the `True` and `False` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/


-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by
  trivial
  done

example : True → True := by
  intro hTrivial
  trivial
  done

example : False → True := by
  intro hFake
  trivial
  done

example : False → False := by
  intro hFake
  exact hFake
  done

example : (True → False) → False := by
  intro hContra
  apply hContra
  trivial
  done

example : False → P := by
  intro hFake
  exfalso
  exact hFake
  done

example : True → False → True → False → True → False := by
  intro hT hF hT2 hF2 h
  exact hF
  done

example : P → (P → False) → False := by
  intro hP hPF
  apply hPF at hP
  exact hP
  done

example : (P → False) → P → Q := by
  intro hPF hP
  exfalso
  apply hPF at hP
  exact hP
  done

example : (True → False) → P := by
  intro hTF
  exfalso
  apply hTF
  trivial
  done
