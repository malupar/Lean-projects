variable (p q r : Prop)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) =>
    fun hpq : p ∧ q =>
    show r from h hpq.left hpq.right)
    (fun h : p ∧ q → r =>
    fun hp : p =>
    fun hq : q =>
    show r from h (⟨hp, hq⟩))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : (p ∨ q) → r =>
    And.intro
      (fun hp : p =>
      show r from h (Or.inl hp))
      (fun hq : q =>
      show r from h (Or.inr hq)))
    (fun h : (p → r) ∧ (q → r) =>
    fun hpq : p ∨ q =>
    (Or.elim hpq
      (fun hp : p =>
      show r from h.left hp)
      (fun hq : q =>
      show r from h.right hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) =>
    And.intro
      (fun hp : p =>
      show False from h (Or.inl hp))
      (fun hq : q =>
      show False from h (Or.inr hq)))
    (fun h : ¬p ∧ ¬q =>
    (fun hpoq : p ∨ q =>
    (Or.elim hpoq
      (h.left)
      (h.right))))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h : ¬p ∨ ¬q =>
  fun paq : p ∧ q =>
  h.elim
    (fun hnp : ¬p =>
    absurd paq.left hnp)
    (fun hnq : ¬q =>
    absurd paq.right hnq)

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p =>
  absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q =>
  (fun hpq : p → q =>
  show False from h.right (hpq h.left))

example : ¬p → (p → q) :=
  fun h : ¬p =>
  fun hp : p =>
  absurd hp h

example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q =>
  fun hp : p =>
  Or.elim h
    (fun hnp : ¬p =>
    absurd hp hnp)
    (fun hq : q =>
    show q from hq)

example : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False =>
    (h.elim
      (fun hp : p =>
      show p from hp)
      (fun hNot : False =>
      hNot.rec)))
    (fun h : p =>
    show p ∨ False from Or.inl h)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun h : p ∧ False =>
    show False from h.right)
    (fun h : False =>
    h.rec)

example : (p → q) → (¬q → ¬p) :=
  fun h : p → q =>
  fun hnq : ¬q =>
  fun hp : p =>
  show False from hnq (h hp)
