import Game.Levels.L9Pset.L9Pset2

open Finset

World "L9Pset"
Level 3
Title "Problem 3"

Introduction "# Problem 3

Prove that `2 * (1 + 2 + ... + N) = N * (N + 1)`.

"

/-- `1 + 2 + ... + N = N * (N + 1) / 2`. -/
TheoremDoc SumFirstN as "SumFirstN" in "∑aₙ"

/-- Prove the statement. -/
Statement SumFirstN (N : ℕ) :
    2 * ∑ k ∈ range N, (k + 1) = N * (N + 1) := by
induction' N with N hN
bound
have f1 : ∑ k ∈ range (N + 1), (k + 1) = ∑ k ∈ range N, (k + 1) + (N + 1) := by apply sum_range_succ
rewrite [f1]
have f2 : 2 * (∑ k ∈ range N, (k + 1) + (N + 1)) = 2 * (∑ k ∈ range N, (k + 1)) + 2 * (N + 1) := by ring_nf
rewrite [f2, hN]
ring_nf

Conclusion ""
