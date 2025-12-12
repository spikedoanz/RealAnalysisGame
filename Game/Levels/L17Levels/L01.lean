import Game.Levels.L16Lecture

open Finset

World "Lecture17"
Level 1
Title "Leibniz Series"
Introduction "
# Level 1: Leibniz Series — Partial Sums

Welcome to Lecture 17! We now turn to evaluating explicit series, starting with a beautiful classical example.

Consider the series:
`∑ k, 1 / ((k + 1) * (k + 2)) = 1/2 + 1/6 + 1/12 + 1/20 + 1/30 + ...`

This series was studied by Gottfried Wilhelm Leibniz in the 17th century. Our goal is to find an *explicit formula* for its partial sums.

## The Strategy: Telescoping

The key insight is **partial fractions**. Each term can be rewritten as:
`1 / ((k + 1) * (k + 2)) = 1/(k + 1) - 1/(k + 2)`

When we sum these, most terms cancel! This is called a **telescoping sum**:
```
  (1/1 - 1/2) + (1/2 - 1/3) + (1/3 - 1/4) + (1/4 - 1/5) + ...
= 1/1 - 1/2 + 1/2 - 1/3 + 1/3 - 1/4 + 1/4 - 1/5 + ...
= 1 - 1/(n+1)
```

## Your Challenge

Prove that for the sequence `a` defined by `a n = 1 / ((n + 1) * (n + 2))`, we have:

`∑ k ∈ range n, a k = 1 - 1 / (n + 1)`

**Hint:** Use induction on `n`. The base case is straightforward. For the inductive step, use `sum_range_succ` to split off the last term, apply the inductive hypothesis, and then do some algebra with `field_simp` and `ring_nf`.

"

/-- The series `∑ k, 1 / ((k + 1) * (k + 2))` converges.
-/
TheoremDoc LeibnizSeriesFinite as "LeibnizSeriesFinite" in "∑aₙ"

Statement LeibnizSeriesFinite {a : ℕ → ℝ} (ha : ∀ n, a n = 1 / ((n + 1) * (n + 2))) :
∀ n, ∑ k ∈ range n, a k = 1 - 1 / (n + 1) := by
  intro n
  induction' n with m hm
  bound
  rewrite [show ∑ k ∈ range (m + 1), a k = ∑ k ∈ range m, a k + a m by apply sum_range_succ]
  rewrite [hm]
  rewrite [ha m]
  push_cast
  norm_num
  field_simp
  ring_nf

Conclusion "
Beautiful! You've found an explicit formula for the partial sums of the Leibniz series.

## What You've Proven

**Theorem (LeibnizSeriesFinite):** For `a n = 1 / ((n + 1) * (n + 2))`, we have:
`∑ k ∈ range n, a k = 1 - 1 / (n + 1)`

## The Power of Telescoping

Your proof used the **telescoping** technique: the terms cancel in pairs, leaving only the first and last pieces. This is one of the most elegant methods in mathematics!

The partial fractions decomposition `1/((k+1)(k+2)) = 1/(k+1) - 1/(k+2)` was the key insight that made everything collapse beautifully.

We can verify the first few partial sums:
- n=1: `1/2 = 1 - 1/2` ✓
- n=2: `1/2 + 1/6 = 2/3 = 1 - 1/3` ✓
- n=3: `2/3 + 1/12 = 3/4 = 1 - 1/4` ✓
- n=4: `3/4 + 1/20 = 4/5 = 1 - 1/5` ✓

Each partial sum is `n/(n+1)`, steadily approaching 1!

## The Proof Technique

Your induction proof had two key steps:
1. **Base case:** The empty sum equals `0 = 1 - 1/1` (after checking carefully!)
2. **Inductive step:** Split off the last term with `sum_range_succ`, apply the hypothesis, and let `field_simp` and `ring_nf` handle the algebra.

Lean's automation made the algebraic manipulation painless!

---

**Historical note:** Leibniz studied many such telescoping series in his work on infinite series in the 1670s-1680s, alongside his development of calculus!
"
