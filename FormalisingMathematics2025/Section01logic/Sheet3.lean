/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/


-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  by_cases hP : True
  by_contra hC
  apply hC
  apply hP
  by_contra hC
  apply hP
  triv


example : False → ¬True := by
  intro h1
  exfalso
  exact h1
  done

example : ¬False → True := by
  intro
  triv
  done

example : True → ¬False := by
  intro h1
  by_contra hC
  apply hC
  done

example : False → ¬P := by
  intro h1
  by_contra
  exact h1
  done

example: P → ¬P → False := by
  intros hP hNP
  apply hNP
  exact hP

example : P → ¬¬P := by
  intros hP hnnP
  apply hnnP
  apply hP
  done

example : (P → Q) → ¬Q → ¬P := by
  intros h1 h2 h3
  apply h2
  apply h1 at h3
  exact h3

example : ¬¬False → False := by
  by_cases hP : False
  by_contra
  apply hP
  intro h2
  apply h2
  apply hP
  done

example : ¬¬P → P := by
  intro hP
  by_contra hC
  apply hP
  exact hC

example : (¬Q → ¬P) → P → Q := by
  intros h1 h2
  change (Q→False) → (P → False) at h1
  by_contra hnQ
  apply h1 at hnQ
  apply hnQ at h2
  exact h2
