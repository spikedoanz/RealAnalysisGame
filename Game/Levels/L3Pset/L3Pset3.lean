import Game.Levels.L3Pset.L3Pset2

World "L3Pset"
Level 3
Title "Problem 3"

Introduction "# Problem 3

Determine what the limit of the sequence `1 / n ^ 2` is, and prove it.

Hints you may find useful: - We have yet to learn about dealing with the
square-root function.  So see if you can be even lazier in your choice of
parameters...  - If you know that `h : 0 < N` holds in the *natural* numbers,
then you can prove that that `1 ≤ N` simply by `apply`ing `h`, that is: `have h'
: 1 ≤ N := by apply h`. (This would not work for an inequality in the real
numbers, since it's in general not true!)
"

/-- Determine what the limit of the sequence `1 / n ^ 2` is, and prove it. -/
example (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n ^ 2) : ∃ L, SeqLim a L := by
    use 0
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
    have natn_geq_one : n >= 1 := by
        by_contra h
        push_neg at h
        interval_cases n
    have n_geq_one : (↑n:ℝ) >= 1 := by
        exact_mod_cast natn_geq_one
    have f2 : 1 / (n^2:ℝ) <= 1 / (n:ℝ) := by
        field_simp
        exact n_geq_one
    norm_num
    have :  ((↑n:ℝ) ^ 2)⁻¹ = 1 / (n^2:ℝ) := by simp
    rw [this]
    have f3 : (1 / (↑n:ℝ)) <= (1 / (↑N:ℝ)) := by
        field_simp
        exact hnℝ
    have f4 : (1 / (↑N:ℝ)) < ε := by
        field_simp
        linarith [hN]
    linarith [f2, f3, f4]

Conclusion "Done."
