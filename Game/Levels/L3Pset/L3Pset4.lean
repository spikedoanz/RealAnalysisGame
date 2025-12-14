import Game.Levels.L3Pset.L3Pset3

open Nat

World "L3Pset"
Level 4
Title "Problem 4"

Introduction "# Problem 4

Here's an even more involved limit problem. We've had luck getting `bound` to prove `|X| = X`, especially when there's a hypothesis `h : 0 ≤ X` already available in the list of assumptions. But I've found it not to be reliable, unfortunately. So let me give you one more theorem for your toolchest.

## New Theorem: `abs_of_nonneg`.
If you have a hypothesis `h : 0 ≤ X` in your toolchest,
then you can prove that `|X| = X` via:

`have factName : |X| = X := by apply abs_of_nonneg h`.
"

/--
Usage: given hypothesis `h : 0 ≤ X`, you can prove: `have : |X| = X := by apply abs_of_nonneg h`
-/
TheoremDoc abs_of_nonneg as "abs_of_nonneg" in "|x|"

NewTheorem abs_of_nonneg

/-- Determine the limit `L` of the sequence `a (n) = (3n + 8) / (2n + 5)`, and prove that `a` indeed converges to `L`. -/
example (a : ℕ → ℝ) (ha : ∀ n, a n = (3 * n + 8) / (2 * n + 5)) :
    ∃ L, SeqLim a L := by
    use 3/2
    intro ε hε
    have hArch : ∃ N : ℕ, 1 / ε < ↑N := by
        apply ArchProp at hε
        exact hε
    choose N hN using hArch
    use N
    intro n hn
    specialize ha n
    have hnℝ : (↑n:ℝ) ≥ (↑N:ℝ) := by exact_mod_cast hn
    have f1 : 0 < 1 / ε := by bound
    have N_neq_zero : (↑N:ℝ) > 0 := by
        linarith [f1, hN]
    have n_neq_zero : (↑n:ℝ) > 0 := by linarith [N_neq_zero, hnℝ]
    have n_pos_nat : n > 0 := by
        by_contra h
        push_neg at h
        interval_cases n
        simp at n_neq_zero
    rewrite [ha]
    field_simp at hN
    ring_nf
    field_simp
    simp
    ring_nf
    have : (10 + (↑n:ℝ) * 4)⁻¹ > 0 := by
      field_simp
      simp
    norm_num
    have : 10 + (↑n:ℝ) * 4 >= 0 := by
      field_simp
      linarith [n_neq_zero]
    rw [abs_of_nonneg this]
    have f2: 1 / (10 + (↑n:ℝ) * 4) < 1 / (↑n) := by
      field_simp
      linarith
    have f3 : (1 / (↑n:ℝ)) <= (1 / (↑N:ℝ)) := by
        field_simp
        exact hnℝ
    have f4 : (1 / (↑N:ℝ)) < ε := by
        field_simp
        linarith [hN]
    have : (10 + (↑n:ℝ) * 4)⁻¹ = 1 / (10 + ↑n * 4) := by
      field_simp
    rw [this]
    linarith [f2, f3, f4]

Conclusion "Done."
