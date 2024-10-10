variable (p q r : Prop)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
    show p ∧ (q ∧ r) from And.intro (And.left (And.left h)) (And.intro (And.right (And.left h)) (And.right h)))
    (fun h : p ∧ (q ∧ r) =>
    show (p ∧ q) ∧ r from And.intro (And.intro (And.left h) (And.left (And.right h))) (And.right (And.right h)))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      (Or.elim h
        (fun hpq : p ∨ q =>
          Or.elim hpq
            (fun hp : p =>
            show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hp)
            (fun hq : q =>
            show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_left r hq)))
        (fun hr : r =>
        show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_right q hr))))
    (fun h : p ∨ (q ∨ r) =>
      (Or.elim h
        (fun hp : p =>
        show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_left q hp))
        (fun hqr : q ∨ r =>
          Or.elim hqr
            (fun hq : q =>
            show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_right p hq))
            (fun hr : r =>
            show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) hr))))
