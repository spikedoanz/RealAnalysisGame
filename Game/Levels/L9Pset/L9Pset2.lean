import Game.Levels.L9Pset.L9Pset1

open Finset

World "L9Pset"
Level 2
Title "Problem 2"

Introduction "# Problem 2

Prove that `N * (N + 1)` is always even.

"

/-- Prove the statement. -/
Statement (N : ℕ) :
    ∃ k : ℕ, N * (N + 1) = 2 * k := by
induction' N with N hN
use 0
choose k hk using hN
use k + N + 1
have f1 : (N + 1) * (N + 1 + 1) = N * (N + 1) + 2 * (1 + N) := by ring_nf
rewrite [f1, hk]
ring_nf

Conclusion ""
