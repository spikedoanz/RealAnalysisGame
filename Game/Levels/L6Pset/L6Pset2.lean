import Game.Levels.L6Pset.L6Pset1

World "L6Pset"
Level 2
Title "Problem 2"

Introduction "# Problem 2

You know that `h : x = 2 ∧ y = 3 ∧ z = 4`.
Your goal is to show that: `z = 4`.
"

/-- Prove the statement. -/
example (x y z : ℝ) (h : x = 2 ∧ y = 3 ∧ z = 4)
  : z = 4 := by
  apply h.2.2

Conclusion "Done."
