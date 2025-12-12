import Game.Levels.L24Lecture

open Finset Set

World "L24Pset"
Level 1
Title "Lipschitz implies Uniformly Continuous"
Introduction "
# Level 1: Lipschitz implies Uniformly Continuous

A function `f : ℝ → ℝ` is called *Lipschitz* if there exists a constant `K > 0` such that for all `x, y ∈ ℝ`,

`|f(y) - f(x)| ≤ K * |y - x|`.

In this problem, you will prove that every Lipschitz function is uniformly continuous.

"

/-- Prove this
-/
Statement (f : ℝ → ℝ) (K : ℝ) (hK : K > 0) (hf : ∀ x y : ℝ, |f y - f x| ≤ K * |y - x|) (a b : ℝ) :
  UnifContOn f (Icc a b) := by
intro ε hε
let δ := ε / K
have δis : δ = ε / K := by rfl
have hδ : δ > 0 := by bound
use δ, hδ
intro x hx y hy hxy
specialize hf x y
have h2 : K * |y - x| < K * δ := by bound
have h3 : K * δ = ε := by rewrite [δis]; field_simp
linarith [hf, h2, h3]

Conclusion "
"
