import Game.Levels.L16Lecture

open Finset

World "L16Pset"
Level 2
Title "Problem 2"

Introduction "
# Problem 2: Prove that multiplying a series by a constant scales its sum accordingly.

"

/-- The partial sums of the series `∑ k, c * a k` is equal to that of `c * ∑ k, a k`.
-/
TheoremDoc SeriesConstMul as "SeriesConstMul" in "∑aₙ"

/-- Prove this
-/
Statement SeriesConstMul (a b : ℕ → ℝ) (c : ℝ) (hb : ∀ n, b n = c * a n) : ∀ n, Series b n = c * Series a n := by
intro n
induction' n with n hn
change ∑ k ∈ range 0, b k = c * ∑ k ∈ range 0, a k
bound
change ∑ k ∈ range (n+1), b k = c * ∑ k ∈ range (n+1), a k
rewrite [sum_range_succ]
rewrite [sum_range_succ]
rewrite [show c * (∑ x ∈ range n, a x + a n) = c * (∑ x ∈ range n, a x) + c * a n by
  ring_nf]
change Series b n + b n = c * Series a n + c * a n
rewrite [hn]
rewrite [hb]
ring_nf

Conclusion ""
