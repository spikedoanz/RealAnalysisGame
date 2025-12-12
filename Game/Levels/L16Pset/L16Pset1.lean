import Game.Levels.L16Lecture
import Game.Levels.L15PsetIntro

open Finset

World "L16Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1: Finite geometric series

"

/-- For any real `x` and natural number `n`,
`(1-x)*(1+...+x^(n-1)) = 1- x^n`.
-/
TheoremDoc FiniteGeomSeries as "FiniteGeomSeries" in "∑aₙ"

/-- Prove this
-/
Statement FiniteGeomSeries (x : ℝ) (n : ℕ) : (1 - x) * ∑ k ∈ range n, x ^ k = 1 - x ^ n := by
induction' n with n hn
bound
rewrite [sum_range_succ]
rewrite [show (1 - x) * (∑ k ∈ range n, x ^ k + x ^ n) = (1 - x) * ∑ k ∈ range n, x ^ k + (1 - x) * x ^ n by
  ring_nf]
rewrite [hn]
rewrite [show x ^ (n + 1) = x ^ n * x by ring_nf]
ring_nf

Conclusion ""
