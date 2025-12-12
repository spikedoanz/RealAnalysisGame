import Game.Levels.L9Lecture
import Game.Levels.L8PsetIntro

open Finset

World "L9Pset"
Level 1
Title "Problem 1"

Introduction "# Problem 1

Prove the same theorem as `Bdd_of_ConvNonzero`, but without the assumption that `L ≠ 0`. (Hint: break
the proof into cases, and the case `L ≠ 0` should just be an appeal to `Bdd_of_ConvNonzero`. What
do you do in the other case?)

"

/-- If `a : ℕ → ℝ` is a sequence which converges, then it is bounded. -/
TheoremDoc Bdd_of_Conv as "Bdd_of_Conv" in "aₙ"

/-- Prove the statement. -/
Statement Bdd_of_Conv (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) :
    SeqBdd a := by
by_cases hL : L = 0
rewrite [hL] at ha
choose N hN using ha 1 (by norm_num)
have f1 : 0 ≤ ∑ k ∈ range N, |a k| := by apply sum_nonneg (by bound)
use 1 + ∑ k ∈ range N, |a k|
split_ands
linarith[f1]
intro n
by_cases hn : n < N
have f2 : |a n| ≤ ∑ k ∈ range N, |a k| := by apply TermLeSum a N n hn
linarith [f2]
have hn' : N ≤ n := by bound
specialize hN n hn'
ring_nf at hN
linarith [hN, f1]
apply Bdd_of_ConvNonzero a L ha hL

Conclusion ""
