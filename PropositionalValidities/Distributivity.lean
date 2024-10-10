variable (p q r : Prop)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
        show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
        show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
    (Or.elim h
      (fun l : p ∧ q =>
      show p ∧ (q ∨ r) from ⟨l.left, Or.inl l.right⟩)
      (fun l : p ∧ r =>
      show p ∧ (q ∨ r) from ⟨l.left, Or.inr l.right⟩)
    ))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) =>
    (Or.elim h
      (fun hp : p =>
      show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inl hp, Or.inl hp⟩)
      (fun hqr : q ∧ r =>
      show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr hqr.left, Or.inr hqr.right⟩)
    ))
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
    have hpq : p ∨ q := h.left
    (Or.elim h.right
      (fun hp : p =>
      show p ∨ (q ∧ r) from Or.inl hp)
      (fun hr : r =>
      (Or.elim hpq
        (fun hp : p =>
        show p ∨ (q ∧ r) from Or.inl hp)
        (fun hq : q =>
        show p ∨ (q ∧ r) from Or.inr ⟨hq, hr⟩)))))
