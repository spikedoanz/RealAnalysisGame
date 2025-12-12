import Game.Levels.L10Pset.L10Pset2

World "L10Pset"
Level 2
Title "Problem 2"

Introduction "
# Problem 2:

Finish the proof of `ProdLim`.

"

/--
If sequences `a b : ℕ → ℝ` converge with `a` going to `L` and `b` going to `M`, then `a n * b n` converges to `L * M`.
-/
TheoremDoc ProdLim as "ProdLim" in "aₙ"

/-- Prove this
-/
Statement ProdLim (a b c : ℕ → ℝ) (L M : ℝ) (ha : SeqLim a L)
    (hb : SeqLim b M) (hc : ∀ n, c n = a n * b n):
    SeqLim c (L * M) := by
by_cases hL : L = 0
rewrite [hL] at ha ⊢
rewrite [(by ring_nf : 0 * M = 0)]
have f : SeqBdd b := by apply Bdd_of_Conv b M hb
apply LimZeroTimesBdd a b c ha f hc
by_cases hM : M = 0
have f : SeqBdd a := by apply Bdd_of_Conv a L ha
rewrite [hM] at hb ⊢
rewrite [(by ring_nf : L * 0 = 0)]
have hc' : ∀ n, c n = b n * a n := by intro n; rewrite [hc]; ring_nf
apply LimZeroTimesBdd b a c hb f hc'
apply ProdLimNeNe a b c L M hL hM ha hb hc

Conclusion "Done."
