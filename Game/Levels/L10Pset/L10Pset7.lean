import Game.Levels.L10Pset.L10Pset6

World "L10Pset"
Level 6
Title "Problem 6"

Introduction "
# Problem 6:

Show that if a sequence has two subsequences that converge to
different limits, then the sequence itself cannot converge.

"


/--
If a sequence `a : ℕ → ℝ` has two convergent subsequences, `a ∘ σ` converges to `L` and `a ∘ τ` converges to `M ≠ L`, then `a` is not convergent.
-/
TheoremDoc Diverge_of_DiffSubseqLim as "Diverge_of_DiffSubseqLim" in "aₙ"


/-- Prove this
-/
Statement Diverge_of_DiffSubseqLim (a : ℕ → ℝ) (σ τ : ℕ → ℕ)
    (σsub : Subseq σ) (τsub : Subseq τ) (L M : ℝ)
    (hσ : SeqLim (a ∘ σ) L) (hτ : SeqLim (a ∘ τ) M) (hLM : L ≠ M)
    : ¬ SeqConv a := by
intro h
choose K hK using h
have haσ : SeqLim (a ∘ σ) K := by apply SubseqConv a K hK σ σsub
have hLK : L = K := by apply LimUnique (a ∘ σ) L K hσ haσ
have haτ : SeqLim (a ∘ τ) K := by apply SubseqConv a K hK τ τsub
have hMK : M = K := by apply LimUnique (a ∘ τ) M K hτ haτ
rewrite [hLK, hMK] at hLM
contradiction

Conclusion "Done."
