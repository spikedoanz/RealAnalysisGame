import Game.Levels.L22Lecture

open Finset Set

World "Lecture23"
Level 1
Title "Riemann Sum Refinement"
Introduction "
# Level 1: Riemann Sum Refinement

**The Setup**: We have a uniformly continuous function on `[a,b]` - that is, there's a single `δ > 0` such that whenever two points are within `δ` of each other, the function values differ by at most `ε`.

**The Question**: If we refine our Riemann sum partition from `n` subintervals to `n * k` subintervals, how much can the Riemann sum change?

**The Intuition**: When we go from `n` to `n * k` subintervals, we're making the partition finer. If our original partition was already fine enough (meaning `2 * (b - a) / n < δ`), then the sample points in the refined partition shouldn't be too far from the corresponding sample points in the coarse partition. By uniform continuity, this means the function values shouldn't differ by much either.

**Your Goal**: Prove that under these conditions, the difference between the two Riemann sums is bounded by `(b - a) * ε`. This makes sense dimensionally: `ε` measures how much the function can vary locally, and `(b - a)` measures the size of the interval we're integrating over.

**Key Tool**: The `sum_of_prod` lemma lets you reorganize a sum over `m * n` terms as a double sum:

`∑ i ∈ range (m * n), f i = ∑ j ∈ range m, ∑ k ∈ range n, f (j + k * m)`

This will help you compare the refined sum (with `n * k` terms) to the original sum (with `n` terms) by grouping the refined sum into `n` blocks of `k` terms each.
"

lemma sum_of_prod {X : Type*} [CommSemiring X] (f : ℕ → X) (m n : ℕ) :
  ∑ i ∈ range (m * n), f i =
    ∑ j ∈ range m, ∑ k ∈ range n, f (j + k * m) := by
induction' m with m hm
simp
sorry

/--
The sum over `m * n` terms can be expressed as a double sum over `m` and `n`.
-/
TheoremDoc sum_of_prod as "sum_of_prod" in "∑aₙ"

NewTheorem sum_of_prod

/--
If a function `f` is uniformly continuous on `[a,b]`, then the Riemann sum at `n * k` differs
from that at `n` by at most `(b - a) * ε`, provided the partition is fine enough.
-/
TheoremDoc RiemannSumRefinement as "RiemannSumRefinement" in "∫f"

Statement RiemannSumRefinement (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) {n k : ℕ}
    (hn : n ≠ 0) (hk : k ≠ 0)
    {ε δ : ℝ} (hε : ε > 0) (hδ : δ > 0)
    (hunif : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |y - x| < δ → |f y - f x| < ε)
    (hfine : 2 * (b - a) / n < δ) :
  |RiemannSum f a b (n * k) - RiemannSum f a b n| < (b - a) * ε  := by
change |(b - a) / ↑(n * k) * ∑ i ∈ range (n * k), f (a + (i + 1) * (b - a) / ↑(n * k)) -
      (b - a) / n * ∑ i ∈ range n, f (a + (i + 1) * (b - a) / ↑n)| <
  (b - a) * ε
rewrite [sum_of_prod]
rewrite [show (b - a) / ↑(n * k) * ∑ j ∈ Finset.range n, ∑ k_1 ∈ Finset.range k, f (a + (↑(j + k_1 * n) + 1) * (b - a) / ↑(n * k)) -
      (b - a) / ↑n * ∑ i ∈ Finset.range n, f (a + (↑i + 1) * (b - a) / ↑n) =
      (b - a) / n * ∑ j ∈ Finset.range n,  ((1 / k) * ∑ ℓ ∈ Finset.range k, f (a + (ℓ + j * k + 1) * (b - a) / (n * k)) -
      f (a + (j + 1) * (b - a) / n)) by sorry]
have dx : ∀ j ∈ range n, ∀ ℓ ∈ range k,
      |a + (ℓ + j * k + 1) * (b - a) / (n * k) -  (a + (j + 1) * (b - a) / n)| < δ := by
  intro j hj ℓ hℓ
  rewrite [show
    |a + (ℓ + j * k + 1) * (b - a) / (n * k) -  (a + (j + 1) * (b - a) / n)|
    = |(ℓ + 1) * (b - a) / (n * k) -  (b - a) / n| by
    field_simp
    ring_nf]
  have h1 : |(ℓ + 1) * (b - a) / (n * k)  -  (b - a) / n| ≤ 2 * (b - a) / n := by sorry
  linarith [hfine, hδ, h1]
have dy : ∀ j ∈ range n, ∀ ℓ ∈ range k,
  |f (a + (ℓ + j * k + 1) * (b - a) / (n * k)) -  f (a + (j + 1) * (b - a) / n)| < ε := by
  intro j hj ℓ hℓ
  specialize hunif (a + (j + 1) * (b - a) / n) (by sorry)
    (a + (ℓ + j * k + 1) * (b - a) / (n * k)) (by sorry)
    (dx j hj ℓ hℓ)
  apply hunif
sorry

Conclusion "
# What You've Just Proved

You've just established a crucial bridge between uniform continuity and integration theory! Here's why this result matters:

**The Big Picture**: To prove that Riemann sums converge (i.e., that integrals exist), we need to show the Riemann sum sequence is Cauchy. But Riemann sums with different numbers of partitions seem hard to compare directly. Your theorem solves this by showing that if one partition count is a multiple of another, and both are fine enough, then their Riemann sums are close.

**The Uniform Continuity Connection**: Notice how the proof relied crucially on having a *single* `δ` that works for all points in `[a,b]`. If we only had pointwise continuity (where `δ` depends on the specific point), we couldn't make this argument work. This is why uniform continuity is the 'right' condition for integration.

**Next Steps**: In the next level, we'll use this result to prove the fundamental theorem that uniformly continuous functions are integrable. The strategy will be:
1. Given any two large partition counts `m` and `n`
2. Consider their common multiple `m * n`
3. Use your theorem twice: once to compare `m` with `m * n`, and once to compare `n` with `m * n`
4. Apply the triangle inequality to conclude that the Riemann sums for `m` and `n` are close

This is a beautiful example of how the 'right' mathematical framework (uniform continuity) makes difficult problems tractable!
"
