import Game.Levels.L16Lecture

open Finset

World "L16Pset"
Level 3
Title "Problem 3"

Introduction "
# Problem 3: Prove that the sum of two series is the series of the sum.

"

/-- The partial sums of the series `∑ k, a k + b k` is equal to that of `∑ k, a k + ∑ k, b k`.
-/
TheoremDoc SeriesAdd as "SeriesAdd" in "∑aₙ"

/-- Prove this
-/
Statement SeriesAdd (a b c : ℕ → ℝ) (h : ∀ n, c n = a n + b n) : ∀ n, Series c n = Series a n + Series b n := by
intro n
induction' n with n hn
change ∑ k ∈ range 0, c k = ∑ k ∈ range 0, a k + ∑ k ∈ range 0, b k
bound
change ∑ k ∈ range (n+1), c k = ∑ k ∈ range (n+1), a k + ∑ k ∈ range (n+1), b k
rewrite [sum_range_succ, sum_range_succ, sum_range_succ]
change Series c n + c n = Series a n + a n + (Series b n + b n)
rewrite [hn, h]
ring_nf

Conclusion ""
