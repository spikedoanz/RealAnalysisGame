import Game.Levels.L10Pset.L10Pset3

World "L10Pset"
Level 3
Title "Problem 3"

Introduction "
# Problem 3:

We proved `OrderLimLe`; now prove `OrderLimGt`. Notice that the assumption is a **strict** inequality, but the conclusion is not. Why not? (See next Exercise...)

"

/--
If a sequence `a` converges to `L` and `K < a n` for all `n`, then `K ≤ L`.
-/
TheoremDoc OrderLimGt as "OrderLimGt" in "aₙ"

/-- Prove this
-/
Statement OrderLimGt (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (K : ℝ) (hK : ∀ n, K < a n) :
    K ≤ L := by
by_contra hL
have hL' : L < K := by bound
have hLK : 0 < (K - L) := by linarith [hL']
choose N hN using ha (K - L) hLK
specialize hN N (by bound)
rewrite [abs_lt] at hN
have f1 : a N < L + (K - L) := by linarith [hN.2]
have f2 : K = L + (K - L) := by ring_nf
specialize hK N
linarith [f2, hK, f1]

Conclusion "Done."
