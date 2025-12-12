import Game.Levels.L22Pset.L03

open Finset Set

World "L22Pset"
Level 4
Title "Integral Exercise"
Introduction "
# Level 4: Integral Exercise

As you may imagine, the proof that `f(x) = x ^ 2` is integrable will involve the following formula for the sum of squares:

`∑ i ∈ Finset.range n, (i + 1) ^ 2 = (n * (n + 1) * (2 * n + 1)) / 6`.

(All as real numbers.) Prove it. Then in natural language, prove that `f(x) = x ^ 2` is integrable on `[a,b]`.

"


/--
The sum of the squares of the first `n` natural numbers is given by the formula:
$$\\sum_{i=0}^{n-1} (i+1)^2 = \frac{n(n+1)(2n+1)}{6}.$$
-/
TheoremDoc sum_of_squares as "sum_of_squares" in "∑aₙ"

/-- Prove this
-/
Statement sum_of_squares (n : ℕ) :
  ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ 2 = ((n : ℝ) * (n + 1) * (2 * n + 1)) / 6 := by
induction' n with n hn
bound
rewrite [sum_range_succ, hn]
push_cast
ring_nf

Conclusion "
"
