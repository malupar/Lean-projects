open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r =>
  (byCases
    (fun hq : q =>
    show (p → q) ∨ (p → r) from Or.inl (fun _ : p => show q from hq))
    (fun hnq : ¬q =>
    show (p → q) ∨ (p → r) from Or.inr
    (fun hp : p =>
      show r from (Or.elim (h hp)
      (fun hq : q =>
      absurd hq hnq)
      (fun hr : r =>
      show r from hr))
    )))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) =>
  (byCases
    (fun hp : p =>
    (byCases
      (fun hq : q =>
      (h ⟨hp, hq ⟩).rec)
      (fun hnq : ¬q =>
      show ¬p ∨ ¬q from Or.inr hnq)))
    (fun hnp : ¬p =>
    show ¬p ∨ ¬q from Or.inl hnp))

example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) =>
  (byCases
    (fun hp : p =>
    show p ∧ ¬q from ⟨hp, sorry⟩)
    (fun hnp : ¬p =>
    show p ∧ ¬q from sorry))

example : (p → q) → (¬p ∨ q) :=
  fun h : p → q =>
  (byCases
    (fun hp : p =>
    show ¬p ∨ q from Or.inr (h hp))
    (fun hnp : ¬p =>
    show ¬p ∨ q from Or.inl hnp))

example : (¬q → ¬p) → (p → q) :=
  fun h : ¬q → ¬p =>
  fun hp : p =>
  (byCases
    (fun hq : q =>
    show q from hq)
    (fun hnq : ¬q =>
    absurd hp (h hnq)))

example : p ∨ ¬p :=
  byCases
    (fun hp : p =>
    show p ∨ ¬p from Or.inl hp)
    (fun hnp : ¬p =>
    show p ∨ ¬p from Or.inr hnp)

example : (((p → q) → p) → p) :=
  fun h : (p → q) → p =>
  (byCases
    (fun hpq : p → q =>
    show p from h hpq)
    (fun hpq : ¬(p → q) =>
    sorry ))
