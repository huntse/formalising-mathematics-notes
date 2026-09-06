/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;>
  . intro h
    rw [h]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
 intro h1 h2
 rwa [h1]
  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;>
  . intro h
    rwa [and_comm]

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro h
  rw [and_assoc] at h
  exact h
  intro h2
  rw [and_assoc]
  exact h2

example : P ↔ P ∧ True := by
  constructor
  intro h
  constructor
  exact h
  trivial
  intro h2
  cases h2 with
  | intro hP
  exact hP

/- I don't currently understand this at all -/
example : False ↔ P ∧ False := by
  constructor
  · rintro ⟨⟩
  · rintro ⟨-, ⟨⟩⟩

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intros h1 h2
  rw [h1,h2]

example : ¬(P ↔ ¬P) := by
  intro h1
  have hnP : ¬P := by
    cases h1 with
    | intro hP hnP =>
      intro h3
      apply hP <;> assumption
  apply hnP
  rw [h1]
  exact hnP
