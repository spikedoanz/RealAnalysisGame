import Game.Levels.L17Lecture
import Game.Levels.L16PsetIntro
open Finset

World "L17Pset"
Level 1
Title "Monotonicity of Series"
Introduction "
# Level 1: Monotonicity of Series

Prove `Monotone_of_NonNegSeries`:
If `0 ≤ a n`, then `Series a` is Monotone.

"
/-- If `a : ℕ → ℝ` is nonnegative, then `Series a` is `Monotone`.
-/
TheoremDoc Monotone_of_NonNegSeries as "Monotone_of_NonNegSeries" in "∑aₙ"

Statement Monotone_of_NonNegSeries {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) : Monotone (Series a) := by
apply Monotone_of_succ
intro n
change ∑ k ∈ range n, a k ≤ ∑ k ∈ range (n + 1), a k
rewrite [show ∑ k ∈ range (n + 1), a k = ∑ k ∈ range n, a k + a n by
  apply sum_range_succ]
specialize ha n
linarith [ha]


Conclusion "
"
