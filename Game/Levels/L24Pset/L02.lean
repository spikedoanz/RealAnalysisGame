import Game.Levels.L24Pset.L01

open Finset Set

World "L24Pset"
Level 2
Title "Open Balls are Open"
Introduction "
# Level 2: Open Balls are Open

Prove that an open ball `Ball x r` is open, as a set.

"

namespace RealAnalysisGame

/-- Prove this
-/
lemma IsOpen_of_Ball (x : ℝ) (r : ℝ) : IsOpen (Ball x r) := by
by_cases hr : r > 0
intro y hy
simp only [Ball, Set.mem_Ioo] at hy
let δ := min (y - (x - r)) ((x + r) - y)
have hδpos : δ > 0 := by apply lt_min <;> linarith [hy]
have δ1 : δ ≤ y - (x - r) := by bound
have δ2 : δ ≤ (x + r) - y := by bound
use δ, hδpos
intro z hz
simp only [Ball, Set.mem_Ioo] at hz ⊢
split_ands
linarith [hz.1, δ1]
linarith [hz.2, δ2]
simp only [gt_iff_lt, not_lt] at hr
intro y hy
simp only [Ball, Set.mem_Ioo] at hy
exfalso
linarith [hy.1, hy.2, hr]

end RealAnalysisGame

Conclusion "
"
