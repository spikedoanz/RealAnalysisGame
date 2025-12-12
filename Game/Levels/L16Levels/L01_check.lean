import Game.Levels.L15Lecture

open Finset

World "Lecture16"
Level 1
Title "Series"

Introduction "
# Level 1: The Vanishing Term Test

Welcome to the study of infinite series! We now begin one of the most important topics in analysis.

Given a sequence `a : ℕ → ℝ`, we want to understand what it means to add up *all* its terms:
`a 0 + a 1 + a 2 + a 3 + ...`

Since we can't literally add infinitely many numbers, we instead look at the sequence of **partial sums**:

**Definition (Series):** `Series (a : ℕ → ℝ) : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, a k`

So `Series a n` is the sum of the first `n` terms of `a`.

**Definition (SeriesConv):** A series **converges** if its sequence of partial sums converges:
`SeriesConv (a : ℕ → ℝ) : Prop := SeqConv (Series a)`

**Definition (SeriesLim):** If the series converges to `L`, we write:
`SeriesLim (a : ℕ → ℝ) (L : ℝ) : Prop := SeqLim (Series a) L`

---

Your challenge: Prove that **if a series converges, its terms must go to zero**.

This is sometimes called the **nth-term test for divergence**: if the terms don't vanish, the series can't possibly converge!

**Hint:** If the partial sums form a convergent (hence Cauchy) sequence, what can you say about consecutive partial sums? And what's the relationship between `Series a (n+1)` and `Series a n`?

**Warning:** The converse is FALSE! The harmonic series `∑ 1/k` has terms going to zero, but it diverges. So vanishing terms are *necessary* but not *sufficient* for convergence.
"


/-- `(a : ℕ → ℝ) : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, a k`

Given a sequence `a : ℕ → ℝ`, the `Series a` is the sequence of its partial sums. -/
DefinitionDoc Series as "Series"

def Series (a : ℕ → ℝ) : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, a k

/-- `(a : ℕ → ℝ) (L : ℝ) : Prop := SeqLim (Series a) L`

If a sequence `a : N → ℝ` converges to `L`,
we say that `SeriesLim a L` holds. -/
DefinitionDoc SeriesLim as "SeriesLim"

def SeriesLim (a : ℕ → ℝ) (L : ℝ) : Prop := SeqLim (Series a) L

/-- `(a : ℕ → ℝ) : Prop := SeqConv (Series a)`

The Series of a sequence `a : N → ℝ` converges if the sequence of its partial sums converges. -/
DefinitionDoc SeriesConv as "SeriesConv"

def SeriesConv (a : ℕ → ℝ) : Prop := SeqConv (Series a)

NewDefinition Series SeriesConv SeriesLim

/-- If a series converges, then the terms go to zero
-/
TheoremDoc LimZero_of_SeriesConv as "LimZero_of_SeriesConv" in "∑aₙ"


Statement LimZero_of_SeriesConv (a : ℕ → ℝ) (ha : SeriesConv a) : SeqLim a 0 := by
intro ε hε
change SeqConv (Series a) at ha
have cau : IsCauchy (Series a) := by apply IsCauchy_of_SeqConv ha
choose N hN using cau ε hε
use N
intro n hn
specialize hN n hn (n+1) (by bound)
change |∑ k ∈ range (n+1), a k - ∑ k ∈ range n, a k| < ε at hN
rewrite [show ∑ k ∈ range (n+1), a k = ∑ k ∈ range n, a k + a n by apply sum_range_succ] at hN
rewrite [show ∑ k ∈ range n, a k + a n - ∑ k ∈ range n, a k = a n by ring_nf] at hN
rewrite [show a n - 0 = a n by ring_nf]
apply hN

Conclusion "
Excellent! You've proven one of the most important necessary conditions for series convergence.

## What You've Shown

**Theorem (LimZero_of_SeriesConv):** If `SeriesConv a`, then `SeqLim a 0`.

In other words: *The terms of a convergent series must approach zero.*

## Why This Matters

This gives us a quick **divergence test**. To show a series diverges, you only need to check whether its terms go to zero. If they don't, the series definitely diverges!

**Examples of divergent series:**
- `∑ 1` diverges (terms stay at 1)
- `∑ (-1)^k` diverges (terms oscillate between ±1)
- `∑ k/(k+1)` diverges (terms approach 1, not 0)

## The Key Insight

Your proof used a beautiful idea: the difference between consecutive partial sums is exactly one term of the original sequence:

`Series a (n+1) - Series a n = a n`

Since convergent sequences are Cauchy, consecutive partial sums get arbitrarily close together. Therefore the terms `a n` must vanish!

## Critical Warning: The Converse Fails!

Be careful! It is **NOT** true that if `SeqLim a 0`, then `SeriesConv a`.

The classic counterexample is the **harmonic series**:
`∑ 1/k = 1 + 1/2 + 1/3 + 1/4 + ...`

Here `1/k → 0`, but the series diverges! The partial sums grow like `log n`.

So vanishing terms are *necessary* but not *sufficient* for convergence. To prove a series converges, we need additional tests (which we'll develop in future levels).

## Historical Note

This test was known to early mathematicians like Nicole Oresme (14th century) and Jakob Bernoulli (17th century). It was one of the first tools for distinguishing convergent from divergent series.

Oresme also proved the harmonic series diverges using a clever grouping argument, showing that the converse of this theorem fails -- a result that surprised many mathematicians at the time!

---

**Next:** We'll evaluate some explicit series, starting with the beautiful Leibniz series.
"
