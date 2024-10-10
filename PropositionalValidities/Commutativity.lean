variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  -- Here we split the two implications
  Iff.intro
    -- Here we show ->
    (fun h : p ∧ q =>
    show q ∧ p from And.intro (And.right h) (And.left h))
    -- Here we show <-
    (fun h : q ∧ p =>
    show p ∧ q from And.intro (And.right h) (And.left h))

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      -- In order to prove that a or b -> c we do case a -> c b -> c
      (Or.elim h
        (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
        (fun hq : q =>
        show q ∨ p from Or.intro_left p hq)))
    (fun h : q ∨ p =>
      (Or.elim h
        (fun hp : q =>
        show p ∨ q from Or.intro_right p hp)
        (fun hq : p =>
        show p ∨ q from Or.intro_left q hq)))
