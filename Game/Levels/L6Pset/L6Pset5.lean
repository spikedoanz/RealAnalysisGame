import Game.Levels.L6Pset.L6Pset4

World "L6Pset"
Level 5
Title "Problem 5"

Introduction "# Problem 5

You are given five sequences `a b c d e : ℕ → ℝ`, and you know that
`a`, `c`, and `e` converge to `L`, and that, for all `n`, `a n ≤ b n ≤ c n ≤ d n ≤ e n`.
Prove that both `b` and `d` also converge to `L`.
"

/-- Prove the statement. -/
example (a b c d e : ℕ → ℝ) (L : ℝ)
(ha : SeqLim a L)
(hc : SeqLim c L)
(he : SeqLim e L)
(hab : ∀ n, a n ≤ b n)
(hbc : ∀ n, b n ≤ c n)
(hcd : ∀ n, c n ≤ d n)
(hde : ∀ n, d n ≤ e n)
  : SeqLim b L ∧ SeqLim d L := by
  split_ands
  exact SqueezeThm a b c L ha hc hab hbc
  exact SqueezeThm c d e L hc he hcd hde

Conclusion "Done. (Hopefully you didn't do that by hand, but rather quoted -- twice -- a theorem that we recently proved?)"
