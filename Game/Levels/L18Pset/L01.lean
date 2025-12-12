import Game.Levels.L18Lecture
import Game.Levels.L17PsetIntro

open Finset

World "L18Pset"
Level 1
Title "DiffOfSeries"
Introduction "
# Level 1: `DiffOfSeries`

Prove `DiffOfSeries`.

## New Theorem: `sum_Ico_succ`.

"

DisabledTheorem DiffOfSeries

theorem sum_Ico_succ {M : Type*} [AddCommMonoid M] {a b : ℕ} (hab : a ≤ b) (f : ℕ → M) :
    (∑ k ∈ Ico a (b + 1), f k) = (∑ k ∈ Ico a b, f k) + f b := by
apply sum_Ico_succ_top hab

/-- This is the analog of `sum_range_succ` to summing on intervals. -/
TheoremDoc sum_Ico_succ as "sum_Ico_succ" in "∑aₙ"

NewTheorem sum_Ico_succ

/-- Prove `DiffOfSeries`
-/
Statement (a : ℕ → ℝ) {n m : ℕ} (hmn : n ≤ m) :
  Series a m - Series a n = ∑ k ∈ Ico n m, a k := by
induction' m with m hm
have hn : n = 0 := by bound
rewrite [hn]
bound
change (∑ k ∈ range (m+1), a k) - _ = _
by_cases hm' : n ≤ m
specialize hm hm'
rewrite [sum_Ico_succ_top hm']
rewrite [sum_range_succ]
rewrite [← hm]
change Series a m + _ - _ = _
ring_nf
have hn : n = m + 1 := by bound
rewrite [hn]
change Series a (m+1) - _ = _
bound

Conclusion "
"
