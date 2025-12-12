import Game.Levels.L17Lecture

open Finset

World "Lecture18"
Level 1
Title "Absolute Convergence Implies Convergence"
Introduction "
# Level 1: Absolute Convergence Implies Convergence

In this level, we introduce the concept of **absolute convergence** and prove one of the fundamental theorems about series: if a series converges absolutely, then it converges.

## New definition: `AbsSeriesConv`

A series `Series a` is said to converge *absolutely* (`AbsSeriesConv`) if the series of absolute values
`Series (fun n ↦ |a n|)` converges.

This is a *stronger* condition than ordinary convergence. For instance, the alternating harmonic series
$$\\sum_{k=1}^{\\infty} \\frac{(-1)^{k+1}}{k} = 1 - \\frac{1}{2} + \\frac{1}{3} - \\frac{1}{4} + \\cdots$$
converges but does *not* converge absolutely (since the harmonic series diverges).

## The Main Result

**Theorem** (`Conv_of_AbsSeriesConv`): If a series converges absolutely, then it converges.

In other words: *absolute convergence implies convergence*.

## Proof Strategy

The key insight is that if the series of absolute values converges, then it is Cauchy, which means the tails of the series get arbitrarily small. By the triangle inequality, if $\\sum |a_k|$ is small, then $|\\sum a_k|$ is also small.

We will use two helper lemmas (to be proved as homework):
- `DiffOfSeries`: The difference of partial sums equals the sum over the interval
- `Series_abs_add`: The triangle inequality for finite sums

Your task: Prove `Conv_of_AbsSeriesConv` using the Cauchy criterion and these lemmas.
"
/-- `(a : ℕ → ℝ) := SeriesConv (fun n ↦ |a n|)`

We say that a sequence `a : ℕ → ℝ` converges absolutely if `∑ |a n|` converges.-/
DefinitionDoc AbsSeriesConv as "AbsSeriesConv"

NewDefinition AbsSeriesConv

def AbsSeriesConv (a : ℕ → ℝ) : Prop := SeriesConv (fun n ↦ |a n|)


/--
If `n ≤ m`, then `Series a m - Series a n = ∑ k ∈ Ico n m, a k`.
-/
TheoremDoc DiffOfSeries as "DiffOfSeries" in "∑aₙ"

theorem DiffOfSeries (a : ℕ → ℝ) {n m : ℕ} (hmn : n ≤ m) :
  Series a m - Series a n = ∑ k ∈ Ico n m, a k := by
sorry

-- Future: replace `Series_abs_add` by `(Finset.)abs_sum_le_sum_abs`?
/--
If `n ≤ m`, then `|∑ k ∈ Ico n m, a k| ≤ ∑ k ∈ Ico n m, |a k|`.
-/
TheoremDoc Series_abs_add as "Series_abs_add" in "∑aₙ"

theorem Series_abs_add (a : ℕ → ℝ) {n m : ℕ} (hmn : n ≤ m) :
  |∑ k ∈ Ico n m, a k| ≤ ∑ k ∈ Ico n m, |a k| := by
sorry

NewTheorem DiffOfSeries Series_abs_add

/--
  If `Series (fun n ↦ |a n|)` converges, then `Series a` converges.
-/
TheoremDoc Conv_of_AbsSeriesConv as "Conv_of_AbsSeriesConv" in "∑aₙ"

Statement Conv_of_AbsSeriesConv {a : ℕ → ℝ} (ha : AbsSeriesConv a) : SeriesConv a := by
apply SeqConv_of_IsCauchy
intro ε hε
apply IsCauchy_of_SeqConv at ha
choose N hN using ha ε hε
use N
intro n hn m hnm
rewrite [DiffOfSeries _ hnm]
specialize hN n hn m hnm
rewrite [DiffOfSeries _ hnm] at hN
have f1 : |∑ k ∈ Ico n m, a k| ≤ ∑ k ∈ Ico n m, |a k| := by apply Series_abs_add _ hnm
have f2 :  ∑ k ∈ Ico n m, |a k| ≤ |∑ k ∈ Ico n m, (|a k|)| := by bound
linarith [f1, f2, hN]

Conclusion "
# Congratulations!

You've just proven one of the most important theorems in the theory of infinite series!

## What We've Learned

The theorem **absolute convergence implies convergence** gives us a powerful tool: to show a series converges, it often suffices to show it converges absolutely. This is frequently easier because we can ignore the signs of the terms.

## Key Technique

The proof relied on the **Cauchy criterion**: a series converges if and only if its partial sums form a Cauchy sequence. We showed that if the series of absolute values is Cauchy, then the original series must be Cauchy too, using the triangle inequality to bound the partial sums.

## Why This Matters

This theorem is the foundation for:
- **Comparison tests**: If $|a_n| \\leq b_n$ and $\\sum b_n$ converges, then $\\sum a_n$ converges absolutely (hence converges)
- **Rearrangement theorems**: Absolutely convergent series can be rearranged without changing their sum
- **Function series**: Power series and Fourier series often converge absolutely in their domains

## The Converse is False!

Remember: The converse is *not* true. There exist series that converge but do not converge absolutely. These are called **conditionally convergent** series, and they behave very differently from absolutely convergent series (as we'll see in the next level with the Alternating Series Test)!

The distinction between absolute and conditional convergence is one of the most important concepts in real analysis.
"
