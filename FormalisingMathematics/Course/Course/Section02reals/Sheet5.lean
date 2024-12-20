/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import Course.Section02reals.Sheet3
-- import the definition of `TendsTo` from a previous sheet

namespace Section2sheet5

open Section2sheet3

-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  rw [tendsTo_def] at ha ⊢
  intro ε hε
  specialize ha ε hε
  cases' ha with B h
  use B
  intro n hn
  specialize h n hn
  have hAbs : ∀ x :  ℝ, |-x| = |x| := by exact fun x ↦ abs_neg x
  rw [← hAbs]
  ring_nf
  exact h

/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) :=
  by
  rw [tendsTo_def] at *
  -- let ε > 0 be arbitrary
  intro ε hε
  --  There's a bound X such that if n≥X then a(n) is within ε/2 of t
  specialize ha (ε / 2) (by linarith)
  cases' ha with X hX
  --  There's a bound Y such that if n≥Y then b(n) is within ε/2 of u
  obtain ⟨Y, hY⟩ := hb (ε / 2) (by linarith)
  --  use max(X,Y),
  use max X Y
  -- now say n ≥ max(X,Y)
  intro n hn
  rw [max_le_iff] at hn
  specialize hX n hn.1
  specialize hY n hn.2
  --  Then easy.
  rw [abs_lt] at *
  constructor <;>-- `<;>` means "do next tactic to all goals produced by this tactic"
    linarith

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  -- this one follows without too much trouble from earlier results.
  intro ε hε
  have hε2 : (ε/2) > 0 := by exact half_pos hε
  specialize ha (ε/2) hε2
  specialize hb (ε/2) hε2
  cases' ha with B1 ht
  cases' hb with B2 hu
  use max B1 B2
  intro n hn
  have hna : B1 <= n := by exact le_of_max_le_left hn
  have hnb : B2 <= n := by exact le_of_max_le_right hn
  specialize ht n hna
  specialize hu n hnb
  rw[abs_lt] at *
  ring_nf
  constructor <;>
    linarith

end Section2sheet5
