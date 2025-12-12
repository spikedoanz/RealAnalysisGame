import Game.Levels.L8PsetIntro

open Finset

World "Lecture9"
Level 1
Title "Finite Sums"

Introduction "
# Level 1: Finite Sums

Welcome to a new world of mathematics: **finite sums**! In this level, you'll prove that any individual term in a sum of absolute values is bounded by the total sum. This is a fundamental property that bridges discrete and continuous mathematics.

## The Goal

Prove that for any sequence `a : ℕ → ℝ` and natural number `N`, every term `|a n|` with `n < N` is at most the sum `∑ k ∈ range N, |a k|`.

Intuitively: if you're adding up a bunch of nonnegative numbers, no single number can be bigger than the total!

## Strategy: Induction from the Start!

🎯 **Big Hint:** Even though the goal starts with `∀ n < N`, do **NOT** begin with `intro n hn`. Instead, run **induction on `N`** right from the beginning!

This might feel counterintuitive, but trust the process. Induction gives you the perfect structure to peel off one term at a time using `sum_range_succ`.

### Your Induction Strategy:
- **Base case (`N = 0`):** There are no natural numbers less than 0, so you'll get a `contradiction`
- **Inductive step (`N → N + 1`):** Use `sum_range_succ` to write the sum for `N + 1` as the sum for `N` plus the new term `|a N|`
  - Split into cases: Is `n < N` (use inductive hypothesis) or `n = N` (use nonnegativity)?

## New Tools You'll Need

### Summation Notation
`∑ k ∈ range N` means sum as `k` goes from `0` to `N - 1` (which has `N` terms total!)

### `sum_range_succ`
Peels off the last term: `∑ k ∈ range (N + 1), f k = (∑ k ∈ range N, f k) + f N`

### `sum_nonneg`
If each term is nonnegative, so is the sum. Usage: `apply sum_nonneg`, then prove `∀ k ∈ range N, 0 ≤ f k`

### `contradiction`
If your hypotheses are contradictory (like `n : ℕ` with `n < 0`), this tactic closes the goal immediately.

### `by_cases`
Split into cases based on a decidable proposition. Usage: `by_cases h : n < N` creates two goals:
- One where `h : n < N` holds
- One where `h : ¬(n < N)` holds

Good luck! Remember: **induction first, then introduce `n`!**
"

/-- If your hypotheses lead to a contradiction, (for example: if one of your hypotheses is that `h : n < 0` where `n : ℕ` is a natural number) then the `contradiction` tactic closes the goal. -/
TacticDoc contradiction

NewTactic contradiction

/-- Given a function `f : ℕ → ℝ` and a natural number `N`, `sum_range_succ f n` says that:
`∑ n ∈ range (N + 1), f n = ∑ n ∈ range N, f n + f N`. -/
TheoremDoc Finset.sum_range_succ as "sum_range_succ" in "∑aₙ"

/-- If a function is nonnegative, then its sum is also. -/
TheoremDoc Finset.sum_nonneg as "sum_nonneg" in "∑aₙ"

NewTheorem Finset.sum_range_succ Finset.sum_nonneg

/-- `range N`

For a natural number `N`, `range N` represents the numbers from
`0` to `N-1` (there are `N` of them).

Usage: `∑ k ∈ range N, k = N * (N + 1) / 2`.
-/
DefinitionDoc range as "range"

NewDefinition range

/-- If `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) is a sequence, then any term `|a n|`
for `n < N` is less than the sum of all the terms for `n = 0` to `N - 1`. -/
TheoremDoc TermLeSum as "TermLeSum" in "∑aₙ"

/-- Prove this
-/
Statement TermLeSum {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (N : ℕ) :
    ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| := by
induction' N with N hN
intro n hn
contradiction
intro n hn
have f1 : ∑ k ∈ range (N + 1), |a k| = (∑ k ∈ range N, |a k|) + |a N| := by apply sum_range_succ
rewrite [f1]
by_cases hn' : n < N
specialize hN n hn'
have f1' : 0 ≤ |a N| := by bound
linarith [f1', hN]
have f2 : n = N := by bound
rewrite [f2]
have f3 : ∀ k ∈ range N, 0 ≤ |a k| := by bound
have f4 : 0 ≤ ∑ k ∈ range N, |a k| := by apply sum_nonneg f3
linarith [f4]


Conclusion "
# 🎉 Excellent Work!

You've just proven a fundamental result about finite sums! This theorem might seem simple, but it's a powerful building block that appears throughout analysis.

## What You Accomplished

You successfully proved that **every term is bounded by the total sum**:
```
∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k|
```

### Key Techniques You Mastered:

1. **Strategic induction** - You learned to use induction on `N` *before* introducing the universal quantifier, which made the proof structure much cleaner

2. **Working with finite sums** - You used `sum_range_succ` to peel off terms and `sum_nonneg` to establish nonnegativity

3. **Case analysis** - You split the proof into two cases (`n < N` vs `n = N`) and handled each appropriately

4. **Combining results** - You cleverly used the inductive hypothesis for earlier terms and nonnegativity for the final term

## Why This Matters

This result is essential for the next level! You'll use `TermLeSum` to prove that **convergent sequences are bounded**. Here's the connection:

- Every convergent sequence is eventually close to its limit
- But what about the finitely many terms *before* it gets close?
- That's where your theorem comes in! You can bound those initial terms by their finite sum
- Combine this with the eventual bound, and you get a global bound for the entire sequence

## Looking Ahead

In the next level, you'll prove `Bdd_of_ConvNonzero`: convergent sequences with nonzero limits are bounded. This is a cornerstone result in analysis that tells us convergent sequences can't escape to infinity.

Ready to see your theorem in action? Let's move on!
"
