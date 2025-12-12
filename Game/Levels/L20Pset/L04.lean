import Game.Levels.L20Pset.L03
open Finset

World "L20Pset"
Level 4
Title "Bounded Near Limit"
Introduction "
# Level 4: Bounded Near Limit

Prove that if `f → L` as `x → c`, then there is an `M > 0` such that
`|f (x)| < M` near `c`.
"
/--
If `f → L` as `x → c`, then there is an `M > 0` such that
`|f (x)| < M` near `c`.
-/
TheoremDoc Bdd_of_LimAt as "Bdd_of_LimAt" in "f(x)"

/-- Prove `Bdd_of_LimAt`
-/
Statement Bdd_of_LimAt (f : ℝ → ℝ) (c L : ℝ) (hf : FunLimAt f L c) :
  ∃ M > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x| < M := by
use |L| + 1, (by bound [show 0 ≤ |L| by bound])
choose δ δpos hδ using hf 1 (by bound)
use δ, δpos
intro x xNe hx
specialize hδ x xNe hx
rewrite [abs_lt] at hδ
rewrite [abs_lt]
have f1 : L ≤ |L| := by bound
have f2 : -|L| ≤ L := by bound
split_ands
linarith [hδ.1, f2]
linarith [hδ.2, f1]


Conclusion "
"
