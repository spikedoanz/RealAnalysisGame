import Game.Levels.L10Lecture
import Game.Levels.L9PsetIntro

World "L10Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:


Prove the Theorem `LimZeroTimesBdd`: if a sequence `a n` converges to `0`, and the sequence `b n` is merely bounded (not necessarily convergent!), then the product
`a * b` converges to `0`.
"

/--
If sequence `a : ℕ → ℝ` converges to `0` and sequence `b : ℕ → ℝ` is bounded, then `a n * b n` converges to `0`.
-/
TheoremDoc LimZeroTimesBdd as "LimZeroTimesBdd" in "aₙ"

/-- Prove this
-/
Statement LimZeroTimesBdd (a b c : ℕ → ℝ) (ha : SeqLim a 0) (hb : SeqBdd b) (hc : ∀ n, c n = a n * b n)
      : SeqLim c 0 := by
intro ε hε
choose L Lpos hL using hb
choose N hN using ha (ε / L) (by bound)
use N
intro n hn
rewrite [hc]
rewrite [(by ring_nf : (a n * b n) - 0 = a n * b n)]
rewrite [(by apply abs_mul : |a n * b n| = |a n| * |b n|)]
specialize hN n hn
rewrite [(by ring_nf : |a n - 0| = |a n|)] at hN
specialize hL n
have f1 : |a n| * |b n| ≤ |a n| * L := by bound
have f1' : |a n| * L < (ε / L) * L := by bound
have f2 : (ε / L) * L = ε := by field_simp
linarith [f1, f1', f2]

Conclusion "Done."
