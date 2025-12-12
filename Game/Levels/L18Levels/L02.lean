import Game.Levels.L18Levels.L01

open Finset

World "Lecture18"
Level 2
Title "Alternating Series Test"
Introduction "
# Level 2: Alternating Series Test

In this level, we prove one of the most elegant and useful results in the theory of infinite series: the **Alternating Series Test**, also known as the **Leibniz Test** (named after Gottfried Wilhelm Leibniz, who discovered it in the 17th century).

## The Setting

Consider an alternating series—one where the signs alternate between positive and negative:

$a_0 - a_1 + a_2 - a_3 + a_4 - \\cdots = \\sum_{n=0}^{\\infty} (-1)^n \\cdot a_n$

When does such a series converge?

## The Theorem

**Theorem** (`AlternatingSeriesTest`): Suppose `a : ℕ → ℝ` is an `Antitone` sequence (meaning $a_0 \\geq a_1 \\geq a_2 \\geq \\cdots$) that converges to `0`. Then the alternating series

$\\sum_{n=0}^{\\infty} (-1)^n \\cdot a_n$

converges.

In other words: *if the terms decrease to zero, then the alternating series converges*.

**Note**: By `AntitoneLimitBound` (to be proved in homework), since $a_n \\to 0$ and $a$ is antitone, we automatically have $a_n \\geq 0$ for all $n$.

## Classic Examples

- The alternating harmonic series: $\\sum_{k=1}^{\\infty} \\frac{(-1)^{k+1}}{k} = 1 - \\frac{1}{2} + \\frac{1}{3} - \\frac{1}{4} + \\cdots$ converges to $\\ln 2$
- The Leibniz formula for $\\pi$: $\\sum_{k=0}^{\\infty} \\frac{(-1)^k}{2k+1} = 1 - \\frac{1}{3} + \\frac{1}{5} - \\frac{1}{7} + \\cdots = \\frac{\\pi}{4}$

## Proof Strategy

The idea is to show that the **even** partial sums and **odd** partial sums both converge to the same limit:
- Even partial sums: $S_{2n} = a_0 - a_1 + a_2 - \\cdots - a_{2n-1}$ form a monotone increasing, bounded sequence
- Odd partial sums: $S_{2n+1} = a_0 - a_1 + a_2 - \\cdots + a_{2n}$ form a monotone decreasing, bounded sequence
- The difference $S_{2n+1} - S_{2n} = a_{2n} \\to 0$, so they converge to the same limit

This will require several technical lemmas (all to be proved in homework), but the main proof brings them all together beautifully!

Your task: Prove the `AlternatingSeriesTest` by showing both even and odd subsequences of partial sums converge to the same limit.

## New Theorems: look up: `AntitoneLimitBound`, `CoherenceOfReals`, `SeqEvenOdd`, `MonotoneSeriesEven`, `AntitoneSeriesOdd`, `BddSeriesEven`, `BddSeriesOdd`, and `DiffGoesToZero`.
"

/--
  If `a : ℕ → ℝ` is `Antitone` and converges to `L`, then for all `n`, `L ≤ a n`. Analogous to `MonotoneLimitBound`.
-/
TheoremDoc AntitoneLimitBound as "AntitoneLimitBound" in "aₙ"

-- ADD TO HOMEWORK
theorem AntitoneLimitBound {a : ℕ → ℝ} (ha : Antitone a) {L : ℝ} (aLim : SeqLim a L) : ∀ n,
  L ≤ a n := by
sorry

/--
  If `a → L` and `b → M` and `a - b → 0`, then `L = M`.
-/
TheoremDoc CoherenceOfReals as "CoherenceOfReals" in "aₙ"

-- ADD TO HOMEWORK
theorem CoherenceOfReals {a b : ℕ → ℝ} {L M : ℝ} (ha : SeqLim a L) (hb : SeqLim b M) (hab : SeqLim (fun n ↦ a n - b n) 0) : L = M := by sorry

/--
  Given `a : ℕ → ℝ`, if `a (2 n) → L` and `a (2n+1) → L`, then `a → L`.
-/
TheoremDoc SeqEvenOdd as "SeqEvenOdd" in "aₙ"

-- ADD TO HOMEWORK
theorem SeqEvenOdd {a : ℕ → ℝ} {L : ℝ} (ha2n : SeqLim (fun n ↦ a (2 * n)) L)
(ha2np1 : SeqLim (fun n ↦ a (2 * n + 1)) L) : SeqLim a L := by sorry

/--
  If `a : ℕ → ℝ` is `Antitone` and `∀ n, 0 ≤ a n`, then the even alternating series `n ↦ ∑ k ∈ range (2n), (-1)^k * a k` is `Monotone`.
-/
TheoremDoc MonotoneSeriesEven as "MonotoneSeriesEven" in "∑aₙ"

--ADD TO HOMEWORK
theorem MonotoneSeriesEven {a : ℕ → ℝ} (ha : Antitone a) (apos : ∀ n, 0 ≤ a n) : Monotone (fun n ↦ ∑ k ∈ range (2 * n), (-1)^k * a k) := by sorry

/--
  If `a : ℕ → ℝ` is `Antitone` and `∀ n, 0 ≤ a n`, then the odd alternating series `n ↦ ∑ k ∈ range (2n+1), (-1)^k * a k` is `Antitone`.
-/
TheoremDoc AntitoneSeriesOdd as "AntitoneSeriesOdd" in "∑aₙ"

--ADD TO HOMEWORK
theorem AntitoneSeriesOdd {a : ℕ → ℝ} (ha : Antitone a) (apos : ∀ n, 0 ≤ a n) : Antitone (fun n ↦ ∑ k ∈ range (2 * n + 1), (-1)^k * a k) := by sorry

/--
  If `a : ℕ → ℝ` is `Antitone` and `∀ n, 0 ≤ a n`, then the even alternating series `n ↦ ∑ k ∈ range (2n), (-1)^k * a k` is bounded by `a 0`.
-/
TheoremDoc BddSeriesEven as "BddSeriesEven" in "∑aₙ"

--ADD TO HOMEWORK
theorem BddSeriesEven {a : ℕ → ℝ} (ha : Antitone a) (apos : ∀ n, 0 ≤ a n) (n : ℕ) : ∑ k ∈ range (2 * n), (-1)^k * a k ≤ a 0 := by sorry

/--
  If `a : ℕ → ℝ` is `Antitone` and `∀ n, 0 ≤ a n`, then the odd alternating series `n ↦ ∑ k ∈ range (2n+1), (-1)^k * a k` is bounded below by `0`.
-/
TheoremDoc BddSeriesOdd as "BddSeriesOdd" in "∑aₙ"

--ADD TO HOMEWORK
theorem BddSeriesOdd {a : ℕ → ℝ} (ha : Antitone a) (apos : ∀ n, 0 ≤ a n) (n : ℕ) : 0 ≤ ∑ k ∈ range (2 * n + 1), (-1)^k * a k := by sorry

/--
  If `a → 0`, then the difference of odd and even alternating series, `n ↦ ∑ k ∈ range (2n+1), (-1)^k * a k - ∑ k ∈ range (2n), (-1)^k * a k` goes to `0`.
-/
TheoremDoc DiffGoesToZero as "DiffGoesToZero" in "∑aₙ"

--ADD TO HOMEWORK
theorem DiffGoesToZero {a : ℕ → ℝ} (aLim : SeqLim a 0) : SeqLim (fun n ↦ ∑ k ∈ range (2 * n + 1), (-1)^k * a k - ∑ k ∈ range (2 * n), (-1)^k * a k) 0 := by sorry

NewTheorem AntitoneLimitBound CoherenceOfReals SeqEvenOdd MonotoneSeriesEven AntitoneSeriesOdd BddSeriesEven BddSeriesOdd DiffGoesToZero

/--
  If `a` decreases to `0`, then the alternating series `Series (fun n ↦ (-1)^n * a n)` converges.
-/
TheoremDoc AlternatingSeriesTest as "AlternatingSeriesTest" in "∑aₙ"

Statement AlternatingSeriesTest {a : ℕ → ℝ} (ha : Antitone a) (aLim : SeqLim a 0) : SeriesConv (fun n ↦ (-1)^n * a n) := by
have apos : ∀ n, 0 ≤ a n := by apply AntitoneLimitBound ha aLim
let S2n : ℕ → ℝ := (fun n ↦ ∑ k ∈ range (2 * n), (-1)^k * a k)
let S2np1 : ℕ → ℝ := (fun n ↦ ∑ k ∈ range (2 * n + 1), (-1)^k * a k)
have s2nMono : Monotone S2n := by apply MonotoneSeriesEven ha apos
have s2np1Anti : Antitone S2np1 := by apply AntitoneSeriesOdd ha apos
have s2nBdd : ∀ n, S2n n ≤ a 0 := by apply BddSeriesEven ha apos
have s2np1Bdd : ∀ n, 0 ≤ S2np1 n := by apply BddSeriesOdd ha apos
have s2nCauchy : IsCauchy S2n := by apply IsCauchy_of_MonotoneBdd s2nMono s2nBdd
have s2nLim : SeqConv S2n := by apply SeqConv_of_IsCauchy s2nCauchy
have s2np1Cauchy : IsCauchy S2np1 := by apply IsCauchy_of_AntitoneBdd s2np1Anti s2np1Bdd
have s2np1Lim : SeqConv S2np1 := by apply SeqConv_of_IsCauchy s2np1Cauchy
choose L hL using s2nLim
choose M hM using s2np1Lim
have diffZero : SeqLim (fun n ↦ S2np1 n - S2n n) 0 := by apply DiffGoesToZero aLim
have hLM : M = L :=  CoherenceOfReals hM hL diffZero
have s2nIs : S2n = fun n ↦ Series (fun k ↦ (-1)^k * a k) (2 * n) := by rfl
rewrite [s2nIs] at hL
have s2np1Is : S2np1 = fun n ↦ Series (fun k ↦ (-1)^k * a k) (2 * n + 1) := by rfl
rewrite [s2np1Is] at hM
rewrite [hLM] at hM
use L
apply SeqEvenOdd hL hM

Conclusion "
# Congratulations!

You've just proven the **Alternating Series Test**—one of the most beautiful and practical convergence tests in real analysis!

## What We've Accomplished

This theorem tells us that an alternating series $\\sum_{n=0}^{\\infty} (-1)^n \\cdot a_n$ converges whenever:
1. The terms $a_n$ are decreasing (antitone)
2. The terms approach zero: $a_n \\to 0$

These conditions are remarkably easy to check in practice!

## The Power of the Proof Technique

The proof strategy—analyzing even and odd partial sums separately—is a powerful technique that appears throughout analysis:
- The even partial sums squeeze upward toward the limit
- The odd partial sums squeeze downward toward the limit
- They meet in the middle as $a_n \\to 0$

This \"pinching\" or \"squeezing\" argument is elegant and intuitive.

## A Crucial Observation: Conditional Convergence

Notice that the alternating harmonic series $\\sum_{k=1}^{\\infty} \\frac{(-1)^{k+1}}{k}$ converges by this test, but its absolute value series $\\sum_{k=1}^{\\infty} \\frac{1}{k}$ (the harmonic series) diverges!

This makes it **conditionally convergent**—it converges, but not absolutely. As we discussed in the introduction to this lecture, such series have remarkable properties: their sums can be rearranged to converge to *any* real number, or even to diverge! This is **Riemann's Rearrangement Theorem**, which we'll explore in future levels.

## Historical Note

Leibniz discovered this test in the 1670s while studying his famous series for $\\pi/4$ (also known centuries before to the Indian Madhava). It was one of the first convergence tests ever discovered, and it remains one of the most useful and elegant results in all of analysis.

## What's Next?

With absolute convergence (Level 1) and the alternating series test (Level 2) under our belt, we're now ready to explore the deep and sometimes counterintuitive theory of **rearrangements of series**—where the distinction between absolute and conditional convergence becomes truly dramatic!
"
