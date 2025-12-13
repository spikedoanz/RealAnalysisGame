import Game.Levels.L3Pset.L3Pset1

World "L3Pset"
Level 2
Title "Problem 2"

Introduction "# Problem 2

Prove that the sequence `(n + 1) / n` has a limit, say, `L`, and determine what
it is.

We haven't yet learned a good way to use the theorem `OneOverNLimZero` that we
already proved, so just adapt the proof of that, rather than trying to quote it.
(It's good practice!)
"

/-- Prove that the sequence `(n + 1) / n` has a limit `L` and determine what it is. -/
example (a : ℕ → ℝ) (ha : ∀ n, a n = (n + 1) / n) : ∃ L, SeqLim a L := by
    use 1
    intro ε hε
    have hArch : ∃ N : ℕ, 1 / ε < ↑N := by
        apply ArchProp at hε
        exact hε
    choose N hN using hArch
    use N
    intro n hn
    specialize ha n
    rewrite [ha]
    have hnℝ : (↑n:ℝ) ≥ (↑N:ℝ) := by exact_mod_cast hn
    have f3 : 0 < 1 / ε := by bound
    have N_neq_zero : (↑N:ℝ) > 0 := by
        linarith [f3, hN]
    have n_neq_zero : (↑n:ℝ) > 0 := by linarith [N_neq_zero, hnℝ]
    have : (↑n:ℝ) + 1 - (↑n:ℝ) = 1 := by simp
    field_simp
    rw [this]
    have Nε_leq_nε : (↑N:ℝ) * ε ≤ (↑n:ℝ) * ε := by bound
    field_simp at hN
    have : 1 / (↑n:ℝ) > 0 := by bound
    have : abs (1 / (↑n:ℝ))  = 1 / (↑n:ℝ) := by simp
    rw [this]
    field_simp
    linarith [Nε_leq_nε, hN]

Conclusion "Done."
