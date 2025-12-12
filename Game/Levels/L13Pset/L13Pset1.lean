import Game.Levels.L13Lecture
import Game.Levels.L12PsetIntro

World "L13Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

Prove `AntitoneSubseq_of_UnBddPeaks`

## New theorem: `Antitone_of_succ`

"

theorem Antitone_of_succ {X : Type*} [Preorder X] (a : ℕ → X) (ha : ∀ n, a (n+1) ≤ a n) : Antitone a := by
exact antitone_nat_of_succ_le ha

/-- If `a (n+1) ≤ a n` holds for all `n`, then `a` is `Antitone`. -/
TheoremDoc Antitone_of_succ as "Antitone_of_succ" in "aₙ"

NewTheorem Antitone_of_succ

--DisabledTheorem AntitoneSubseq_of_UnBddPeaks

/-- Prove `AntitoneSubseq_of_UnBddPeaks`
-/
Statement {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (ha : UnBddPeaks a)
  : ∃ σ, Subseq σ ∧ Antitone (a ∘ σ) := by
change ∀ k, ∃ n > k, ∀ m > n, a m ≤ a n at ha
choose τ hτbnd hτAbnd using ha
let σ : ℕ → ℕ := fun n ↦ τ^[n] (τ 0)
use σ
split_ands
apply Subseq_of_Iterate
apply hτbnd
apply Antitone_of_succ
intro n
change a (τ^[n + 2] 0) ≤ a (τ^[n+1] 0)
rewrite [← show τ (τ^[n] 0) = τ^[n + 1] 0 by apply succ_iterate]
apply hτAbnd
rewrite [← show τ (τ^[n+1] 0) = τ^[n + 2] 0 by apply succ_iterate]
rewrite [show τ (τ^[n] 0) = τ^[n + 1] 0 by apply succ_iterate]
apply hτbnd



Conclusion ""
