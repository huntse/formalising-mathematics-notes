/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

-- Here are a few ways to break down a conjunction:

-- You can use `obtain`
example : P ∧ Q → P := by
  intro h
  obtain ⟨left, right⟩ := h
  exact left

-- or `rcases` (which is just `obtain` but with a slightly different syntax)
example : P ∧ Q → P := by
  intro h
  rcases h with ⟨left, right⟩
  exact left

/--
The pattern `intro h` then `rcases h with ...` is so common that it has an abbreviation as
`rintro ...`, so you could also do
-/
example : P ∧ Q → P := by
  rintro ⟨left, right⟩
  exact left

-- or you can get the relevant part out directly using `.left`
example : P ∧ Q → P := by
  intro h
  exact h.left

-- or by using `.1` (the first part)
example : P ∧ Q → P := by
  intro h
  exact h.1

example : P ∧ Q → Q := by
  intro h
  cases h with
  | intro hP hQ =>
  exact hQ

example : (P → Q → R) → P ∧ Q → R := by
  intros h1 h2
  cases h2 with
  | intro hP hQ =>
  apply h1 at hP
  apply hP at hQ
  exact hQ

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  -- After the `constructor` tactic, we have *2 goals* for the first time!
  -- We use centre-dots, typed as `\.` to help Lean (and the reader) figure out when we're done
  · assumption
  · assumption

-- If the exact same tactic works to finish both goals, these can be combined:
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  all_goals assumption

-- or alternatively
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor <;> assumption

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
 | intro hP hQ =>
  constructor
  . apply hQ
  . apply hP

example : P → P ∧ True := by
  intro h
  constructor
  . apply h
  . trivial

example : False → P ∧ False := by
  intro h
  exfalso
  exact h

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intros h1 h2
  cases h1 with
 | intro hP hQ =>
  cases h2 with
 | intro hQ2 hR =>
  constructor
  . exact hP
  . exact hR

example : (P ∧ Q → R) → P → Q → R := by
  intros h hP hQ
  apply h
  constructor
  . apply hP
  . exact hQ
