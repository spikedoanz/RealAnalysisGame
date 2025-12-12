import Game.Levels.L24Pset.L01
import Game.Levels.L24Pset.L02

World "L24Pset"
Title "Pset 24"

Introduction "
# Problem Set 24

Prove Problems 1 - 6 formally (in natural language); the rest can be proved using sketches of the main ideas.

$\\# 1)$ Prove that an arbitrary union of open sets is open.

$\\# 2)$ Prove that a finite intersection of open sets is open. Give a counterexample to show that an infinite intersection of open sets need not be open.

$\\# 3)$ Prove that an arbitrary intersection of closed sets is closed.

$\\# 4)$ Prove that a finite union of closed sets is closed. Give a counterexample to show that an infinite union of closed sets need not be closed.

$\\# 5)$ Prove that if a set `S : Set ℝ` is closed, then it contains all its limit points; that is, if a sequence `(x_n)` in `S` converges to `x`, then `x ∈ S`. (This is in fact what closed sets are \"closed\" under -- taking limits!)

$\\# 6)$ Prove that if a set `S : Set ℝ` contains all its limit points (`∀ (x : ℕ → ℝ) (L : ℝ), (∀ n, x n ∈ S) → (SeqLim x L) → (L ∈ S)`), then it is closed.

$\\# 7)$ Give a different proof that a closed interval `[a, b]` is Closed. Suppose `xₙ` is a sequence in `[a, b]` converging to `L`. Show that `L ∈ [a, b]`. [Hint: Try the Order Limit Theorem from Lecture 10, Level 2...]

$\\# 8)$ Let `S` be a set of reals, and let `T` be the set of its limit points (that is, the set of all `L : ℝ` such that there exists a sequence `(x_n)` in `S` converging to `L`). Show that if `L` is a limit point of `S ⋃ T`, then `L` is a limit point of `S`. That is, no new limit points are created when we pass from `S` to its \"closure\" `S ⋃ T`. [Hint: Remember how we proved that the real numbers are complete?...]

$\\# 9)$ Prove that if `S` is compact, then any sequence `(x_n)` in `S` has a subsequence that converges to a limit in `S`. The latter property is called *sequential compactness*.

$\\# 10)$ Conversely, prove that if `S` is sequentially compact (that is, every sequence in `S` has a subsequence converging to a limit in `S`), then it is compact.

$\\# 11)$⋆ (Optional!) Let `C` denote the \"Cantor set\". This is constructed as follows. Start with the closed interval `[0, 1]`. Remove the open middle third `(1/3, 2/3)`, leaving the two closed intervals `[0, 1/3]` and `[2/3, 1]`. Now remove the open middle thirds of these two intervals, leaving four closed intervals: `[0, 1/9]`, `[2/9, 1/3]`, `[2/3, 7/9]`, and `[8/9, 1]`. Continue this process indefinitely. The Cantor set `C` is defined as the intersection of all these sets obtained at each step. Show that the Cantor set `C` is closed and hence compact. A point `p` in a set `S` is said to be an *isolated point* of `S` if there exists a ball `Ball p r` that contains no other points of `S` except for `p` itself; that is, there is no nontrivial sequence in `S` converging to `p`. A set `S` is called *perfect* if it has no isolated points, that is, its every point is a nontrivial limit point.
Show that the Cantor set is perfect.

"
