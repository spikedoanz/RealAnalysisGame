import Game.Levels.L8Pset.L8Pset3

World "L8Pset"
Level 4
Title "Problem 4"

Introduction "# Problem 4

Suppose a sequence `σ : ℕ → ℕ` takes values in the
*natural numbers* (not reals), and is strictly increasing, that is,
if `i < j`, then `σ (i) < σ (j)`. Prove that
`σ (n)` grows at least as fast as `n` itself.

"


/--
If a sequence `σ : ℕ → ℕ` is strictly increasing, then it grows at least linearly.
-/
TheoremDoc SubseqGe as "SubseqGe" in "aₙ"


/-- Prove the statement. -/
Statement SubseqGe {σ : ℕ → ℕ} (hσ : ∀ i j, i < j → σ (i) < σ (j)) : ∀ n, n ≤ σ (n)  := by
intro n
induction' n with n hn
bound
have f1 : n < n + 1 := by bound
specialize hσ n (n + 1) f1
linarith [hn, f1, hσ]

Conclusion ""
