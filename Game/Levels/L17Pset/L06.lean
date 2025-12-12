import Game.Levels.L17Pset.L05'
open Finset

World "L17Pset"
Level 3
Title "The Comparison Test"
Introduction "
# Level 3: The Comparison Test

Prove the `ComparisonTest`: if `a n` is dominated by a convergent series,
then it also converges.

(In lecture 17, we proved a special case of this theorem, when we started studying the Basel Problem.)

"
/-- If `0 ≤ a n ≤ b n` and `Series b` converges, then so does `Series a`.
-/
TheoremDoc ComparisonTest as "ComparisonTest" in "∑aₙ"

Statement ComparisonTest {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n)
  (hb : SeriesConv b) : SeriesConv a := by
have bNonneg : ∀ n, 0 ≤ b n := by
  intro n;
  linarith [hab n, ha n]
choose L hL using hb
apply SeqConv_of_MonotoneBdd (Series a) L
intro n
have habBnd := SeriesOrderThm hab n
have bBnd := MonotoneLimitBound (Monotone_of_NonNegSeries bNonneg) hL n
linarith [habBnd, bBnd]
apply Monotone_of_NonNegSeries ha

Conclusion "
"
