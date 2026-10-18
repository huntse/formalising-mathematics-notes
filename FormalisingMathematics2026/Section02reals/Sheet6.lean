/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2026.Solutions.Section02reals.Sheet5
-- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  intro ε hε
  rw [tendsTo_def] at h
  obtain ⟨B, hB⟩ := h (ε/37) (by simpa)
  use B
  intro n hn
  specialize hB n hn
  calc |37 * a n - 37 * t|
    _ = |(a n - t) * 37|   := by ring_nf
    _ = |(a n - t)| * |37| := by apply abs_mul (a n - t) 37
    _ = |a n - t| * 37     := by ring_nf
    _ < ε                  := by linear_combination hB * 37


/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε hε
  rw [tendsTo_def] at h
  obtain ⟨B, hB⟩ := h (ε/c) (by exact div_pos hε hc)
  use B
  intro n hn
  specialize hB n hn
  calc |c * a n - c * t|
    _ = |(a n - t) * c|   := by ring_nf
    _ = |(a n - t)| * |c| := by apply abs_mul (a n - t) c
    _ = |a n - t| * |c|   := by ring_nf
    _ = |a n - t| * c     := by rw[abs_of_pos hc]
    _ < ε                 := by exact (lt_div_iff₀ hc).mp hB

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε hε
  rw [tendsTo_def] at h
  obtain ⟨B, hB⟩ := h (ε/|c|) (by exact div_pos hε (abs_pos_of_neg hc))
  use B
  intro n hn
  specialize hB n hn
  calc |c * a n - c * t|
    _ = |(a n - t) * c|   := by ring_nf
    _ = |(a n - t)| * |c| := by apply abs_mul (a n - t) c
    _ = |a n - t| * |c|   := by ring_nf
    _ < ε                 := by exact (lt_div_iff₀ (abs_pos_of_neg hc)).mp hB

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rcases lt_trichotomy c 0 with h_cneg | h_czero | h_cpos
  . exact tendsTo_neg_const_mul h h_cneg
  . -- c = 0 so c*t=0
    have : c * t = 0 := by exact mul_eq_zero_of_left h_czero t
    rw [this]
    intro ε hε
    -- likewise for all functions n ↦ c a n, every term is zero
    refine ⟨0, fun n _ ↦ ?_⟩
    dsimp only
    have (n : ℕ) : c * a n = 0 := mul_eq_zero_of_left h_czero (a n)
    rw [this n]
    simpa using hε
  . exact tendsTo_pos_const_mul h h_cpos

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  have : (fun n => a n * c) = (fun n => c * a n) := by
    funext n
    exact mul_comm (a n) c
  simp only[this, mul_comm t c]
  exact tendsTo_const_mul c h

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  intro ε hε
  rw [tendsTo_def] at *
  obtain ⟨a_0, ha⟩ := h1 ε hε
  obtain ⟨b_0, hb⟩ := h2 ε hε
  -- now we need to apply or specialize ha and hb such that if a_0 ≤ n and b_0 ≤ n then |a n - b n -t| < ε

  sorry

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  sorry

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  sorry

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
sorry

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  sorry

end Section2sheet6
