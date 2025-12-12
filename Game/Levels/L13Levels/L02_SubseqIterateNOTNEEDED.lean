import Game.Levels.L12Lecture

World "Lecture13"
Level 1
Title "Iterated Subsequence"


Introduction "
# Level 1: Iterated Subsequence

In the next level, we'll prove a theorem about `Monotone` subsequences
of certain sequences, for which this level is a warmup.

Here you'll prove the following. Assume that a sequence `σ : ℕ → ℕ` grows faster than the identity, `σ n > n`. For a fixed \"base point\" `n₀ : ℕ`, consider the \"orbit of n₀ under σ\", by which we mean: the sequence:

`n₀, σ n₀, σ^[2] n₀, ...`

In other words, start with `n₀` and keep applying `σ` iteratively (in Lean, we simply write the function: `fun n ↦ σ^[n] n₀`).

Goal: This orbit sequence is strictly increasing, that is, it is a `Subseq`.

## New theorem: `subseq_of_succ`

If you have a sequence `σ : ℕ → ℕ` and you know that
it increases from one term to its successor: `σ n < σ (n + 1)`,
then it's always strictly increasing, `i < j → σ i < σ j`; that is,
`σ` is a `Subseq`.

"

/--
If a sequence `σ : ℕ → ℕ` grows faster than the identity, `n < σ n`,
then the orbit of any base point `n₀ : ℕ` under `σ` -- this means the sequence `n₀, σ n₀, σ^[2] n₀, ...` -- is a `Subseq`, that is, is strictly increasing.
-/
TheoremDoc Subseq_of_Iterate as "Subseq_of_Iterate" in "aₙ"

/-- Prove this
-/
Statement Subseq_of_Iterate (σ : ℕ → ℕ) (hσ : ∀ n, n < σ n) (n₀ : ℕ) :
  Subseq (fun n ↦ σ^[n] n₀) := by
  apply subseq_of_succ
  intro n
  specialize hσ (σ^[n] n₀)
  have f : σ (σ^[n] n₀) = σ^[n+1] n₀ := by apply succ_iterate
  rewrite [f] at hσ
  apply hσ

Conclusion ""
