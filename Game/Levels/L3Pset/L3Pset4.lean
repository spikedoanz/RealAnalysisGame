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
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = (3 * n + 8) / (2 * n + 5)) :
    ∃ L, SeqLim a L := by
use 3 / 2
intro ε hε
choose N hN using ArchProp hε
have OneOverε : 0 < 1 / ε := by bound
have Npos : (0 : ℝ) < N := by linarith [OneOverε, hN]
field_simp at hN
have Npos' : 0 < N := by exact_mod_cast Npos
have Nge1' : 1 ≤ N := by apply Npos'
have Nge1 : (1 : ℝ) ≤ N := by exact_mod_cast Nge1'
use N
intro n hn
specialize ha n
rewrite [ha]
have f1 : ((3 : ℝ) * n + 8) / (2 * n + 5) - 3 / 2 =
  1 / (2 * (2 * n + 5))
  := by field_simp; ring_nf
rewrite [f1]
have f2 : (0 : ℝ) ≤ (2 * (2 * n + 5)) := by bound
have f3 : (0 : ℝ) ≤ 1 / (2 * (2 * n + 5)) := by bound
have f4 : |(1 : ℝ) / (2 * (2 * n + 5))| = 1 / (2 * (2 * n + 5)) := by apply abs_of_nonneg f3
rewrite [f4]
field_simp
have f5 : (N : ℝ) ≤ n := by exact_mod_cast hn
have f6 : (2 : ℝ) * (2 * N + 5) * ε ≤ 2 * (2 * n + 5) * ε := by bound
have f6' : (N : ℝ) ≤ 2 * (2 * N + 5) := by bound
have f6'' : N * ε ≤ 2 * (2 * N + 5) * ε := by bound
have f7 : 1 < 2 * (2 * N + 5) * ε := by linarith [f6'', hN]
linarith [f7, f6]

Conclusion "Done."
