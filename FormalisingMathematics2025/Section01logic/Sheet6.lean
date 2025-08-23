/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP
  done

example : Q → P ∨ Q := by
  intro h
  right
  exact h
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intros hPoQ hP hQ
  cases hPoQ with
  | inl hP1 =>
    apply hP
    exact hP1
  | inr hQ1 =>
    apply hQ
    exact hQ1
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases hPoQ with
  | inl hP =>
    right
    exact hP
  | inr hQ =>
    left
    exact hQ
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  . intro h1
    cases h1 with
    | inl hPoQ =>
      cases hPoQ with
      | inl hP =>
        left
        exact hP
      | inr hQ =>
        right
        left
        exact hQ
    | inr hR =>
      right
      right
      exact hR
  . intro h2
    cases h2 with
    | inl hP =>
      left
      left
      exact hP
    | inr hQoR =>
      cases hQoR with
      | inl hQ =>
        left
        right
        exact hQ
      | inr hR =>
        right
        exact hR
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intros hPR hQS hPoQ
  cases hPoQ with
  | inl hP =>
    left
    apply hPR
    exact hP

  | inr hQ =>
    right
    apply hQS
    exact hQ
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intros hPQ hPoR
  cases hPoR with
  | inl hP =>
  left
  apply hPQ
  exact hP
  | inr hR =>
  right
  exact hR
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intros hPR hQS
  rw [hPR,hQS]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  . intro h1
    constructor
    . intro hP
      apply h1
      left
      exact hP
    . intro hQ
      apply h1
      right
      exact hQ
  . intro h2
    cases h2 with
    | intro hl hr =>
      intro hPoQ
      cases hPoQ with
      | inl hP =>
        apply hl
        exact hP
      | inr hQ =>
        apply hr
        exact hQ
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  . intro h
    by_cases hP : P
    . right
      intro hQ
      apply h
      constructor
      . exact hP
      . exact hQ
    . left
      exact hP
  . intro h2
    cases h2 with
    | inl hP =>
    intro h4
    apply hP
    exact h4.1
    | inr hQ =>
    intro h5
    apply hQ
    exact h5.2
