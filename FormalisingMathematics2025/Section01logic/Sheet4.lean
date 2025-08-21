/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h
  cases h with
 | intro hP hQ =>
  exact hP
  done

example : P ∧ Q → Q := by
  intro h
  cases h with
  | intro hP hQ =>
  exact hQ
  done

example : (P → Q → R) → P ∧ Q → R := by
  intros h1 h2
  cases h2 with
  | intro hP hQ =>
  apply h1 at hP
  apply hP at hQ
  exact hQ
  done

example : P → Q → P ∧ Q := by
  intros hP hQ
  constructor
  . apply hP
  . apply hQ
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
 | intro hP hQ =>
  constructor
  . apply hQ
  . apply hP
  done

example : P → P ∧ True := by
  intro h
  constructor
  . apply h
  . triv
  done

example : False → P ∧ False := by
  intro h
  exfalso
  exact h
  done

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
  done

example : (P ∧ Q → R) → P → Q → R := by
  intros h hP hQ
  apply h
  constructor
  . apply hP
  . exact hQ
  done
