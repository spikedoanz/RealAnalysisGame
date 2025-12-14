import Game.Levels.L6Pset.L6Pset3

World "L6Pset"
Level 4
Title "Problem 4"

Introduction "# Problem 4

You are given that a sequence `a : ℕ → ℝ` with the property that it takes arbitrarily large values exceeding 10 in absolute value.
Prove that cannot have a limit less than 5.
"

/-- Prove the statement. -/
example (a : ℕ → ℝ) (ha : ∀ N, ∃ n ≥ N, |a n| > 10)
  : ¬ ∃ L, |L| < 5 ∧ SeqLim a L := by
  push_neg
  intro L hL
  intro h
  specialize h 5
  simp at h
  choose N hN using h
  specialize ha N
  choose n hn using ha
  specialize hN n
  have f1 := hN hn.1
  have f2 := hn.2
  rw [abs_lt] at f1
  have f3 := f1.1
  have f4 := f1.2
  rw [abs_lt] at hL
  have f5 : a n > L - 5 := by linarith [f3]
  have f6 : a n < L + 5 := by linarith [f4]
  have f7 : a n < 10 := by linarith [f6, hL.2]
  have f8 : -10 < a n := by linarith [f5, hL.1]
  have f9 : -10 < a n ∧ a n < 10 := by
    split_ands
    exact f8
    exact f7
  rw [←abs_lt] at f9
  have : 10 < 10 := by linarith [f2, f9]
  absurd this
  simp

Conclusion "Done."
