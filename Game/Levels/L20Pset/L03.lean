import Game.Levels.L20Pset.L02
open Finset

World "L20Pset"
Level 3
Title "Const Times Limit"
Introduction "
# Level 3: Const Times Limit

Prove that if `f → L` as `x → c`, then `k · f → k · L`.
"
/--
If `f → L` as `x → c`, then `k · f → k · L`.
-/
TheoremDoc ConstTimesLimAt as "ConstTimesLimAt" in "f(x)"

/-- Prove `ConstTimesLimAt`
-/
Statement ConstTimesLimAt (f : ℝ → ℝ) (c L k : ℝ) (hf : FunLimAt f L c) :
  FunLimAt (fun x ↦ k * f x) (k * L) c := by
intro ε hε
by_cases hk : k = 0
use 1, (by bound)
intro x xne hx
rewrite [hk]
norm_num
apply hε
have hk' : 0 < |k| := by apply abs_pos_of_nonzero hk
choose δ δpos hδ using hf (ε / |k|) (by bound)
use δ, δpos
intro x xNe hx
rewrite [show (k * f x) - k * L = k * (f x - L) by ring_nf]
rewrite [show |k * (f x - L)| = |k| * |(f x - L)| by apply abs_mul]
specialize hδ x xNe hx
have f1 : |k| * |f x - L| < |k| * (ε / |k|) := by bound
have f2 : |k| * (ε / |k|) = ε := by field_simp
linarith [f1, f2]

Conclusion "
"
