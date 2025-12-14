import Game.Levels.L6Lecture
import Game.Levels.L4PsetIntro

World "L6Pset"
Level 1
Title "Problem 1"

Introduction "# Problem 1

You know that `hx : x = 2`, `hy : y = 3`, and that `hz : z = 4`.
Your goal is to show that: `x = 2 ∧ y = 3 ∧ z = 4`.
"

/-- Prove the statement. -/
example (x y z : ℝ) (hx : x = 2) (hy : y = 3) (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 := by
  split_ands
  exact hx
  exact hy
  exact hz

Conclusion "Done."
