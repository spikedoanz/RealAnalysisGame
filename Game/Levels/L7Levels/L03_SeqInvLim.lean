import Game.Levels.L7Levels.L02_SeqOfAbs

World "Lecture7"
Level 4
Title "SeqInvLim"

Introduction "
# Level 4: Reciprocals of Convergent Sequences — Big Boss Level

One of the most important limit theorems concerns reciprocals: if a sequence converges to
a nonzero limit, then the sequence of reciprocals converges to the reciprocal of the limit.
This result is crucial for proving theorems about quotients and rational functions.

This is a **Big Boss level**—it will require you to synthesize multiple techniques you've
developed throughout this lecture: working with nonzero limits, manipulating complex
algebraic expressions, and carefully choosing your epsilon strategy.

## What We're Proving

**Theorem:** If `a : ℕ → ℝ` converges to `L` with `L ≠ 0`, and `b : ℕ → ℝ` is defined
by `b n = 1 / a n` for all `n`, then `b` converges to `1 / L`.

This is the most technically challenging proof in this lecture.

## New Tools You'll Need

### `abs_div`
For any real numbers `x` and `y` (with `y ≠ 0`), we have `|x / y| = |x| / |y|`.

### `nonzero_of_abs_pos`
If `0 < |x|`, then `x ≠ 0`.

## Hints

Think about what you've proven in the previous levels:
- How can you ensure that `a n ≠ 0` eventually, so the reciprocals are well-defined?
- What happens when you try to bound `|1/a n - 1/L|`? Can you get a common denominator?
- How should you choose your epsilon when applying the convergence of `a` to `L`?
- What role does the lower bound on `|a n|` play in controlling the reciprocals?

The key is finding the right epsilon and carefully managing the algebraic manipulations
involving fractions. You have all the tools you need—now it's time to put them together!
"

/-- For any real numbers `x` and `y`, we have `|x / y| = |x| / |y|`. -/
TheoremDoc abs_div as "abs_div" in "|x|"


theorem nonzero_of_abs_pos {x : ℝ} (h : 0 < |x|) : x ≠ 0 :=
abs_pos.mp h

/-- If `0 < |x|`, then `x ≠ 0`. -/
TheoremDoc nonzero_of_abs_pos as "nonzero_of_abs_pos" in "|x|"

NewTheorem nonzero_of_abs_pos abs_div

/-- If `a : ℕ → ℝ` converges to `L`, and `b : ℕ → ℝ` is its inverse, `b n = 1 / a n` for all `n`, then `b` converges to `1 / L`, provided `L ≠ 0`. -/
TheoremDoc InvLim as "InvLim" in "aₙ"

/-- Prove this
-/
Statement InvLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (LneZero : L ≠ 0) (b : ℕ →
ℝ) (bEqInva : ∀ n, b n = 1 / a n) :
    SeqLim b (1 / L) := by
choose NhalfL hNhalfL using EventuallyGeHalfLimPos a L aToL LneZero
intro ε hε
have : 0 < |L| := by apply abs_pos_of_nonzero LneZero
specialize aToL (ε * |L| * |L| / 2) (by bound)
choose Na hNa using aToL
use Na + NhalfL
intro n hn
specialize bEqInva n
rewrite [bEqInva]
have hnHalfL : NhalfL ≤ n := by bound
have hna : Na ≤ n := by bound
specialize hNhalfL n hnHalfL
specialize hNa n hna
have : 0 < |a n| := by bound
have : a n ≠ 0 := by apply nonzero_of_abs_pos this
have l1 : |1 / a n - 1 / L| = |(L - a n) / (a n * L)| := by field_simp
have l2 :  |(L - a n) / (a n * L)| =  |(L - a n)| / |(a n * L)| := by apply abs_div
have l3 : |(L - a n)| / |(a n * L)| = |(L - a n)| / (|a n| * |L|) := by bound
have l4 : |L - a n| = |-(a n - L)| := by ring_nf
have l5 : |-(a n - L)| = |(a n - L)| := by apply abs_neg
have l6 : |a n - L| / (|a n| * |L|) < (ε * |L| * |L| / 2) / (|a n| * |L|) := by field_simp; bound
have l10 : |(L - a n)| / (|a n| * |L|) = |-(a n - L)| / (|a n| * |L|) := by rewrite [l4]; rfl
have l11 : |-(a n - L)| / (|a n| * |L|) = |(a n - L)| / (|a n| * |L|) := by rewrite [l5]; rfl
have l13 : ε * |L| * |L| / 2 / (|a n| * |L|) = ε * |L| / 2 / |a n| := by field_simp
have l14 : ε * |L| / 2 / |a n| ≤ ε := by field_simp; bound
linarith [l1, l2, l3, l10, l11, l6, l13, l14]

Conclusion "
## Congratulations, Big Boss Defeated!

You've just completed one of the most challenging proofs in elementary analysis! The
reciprocal limit theorem is a major milestone—you've proven that reciprocals preserve
convergence (when the limit is nonzero).

## What You Accomplished

This proof required you to orchestrate multiple sophisticated techniques:
- Using `EventuallyGeHalfLim` to ensure denominators stay bounded away from zero
- Choosing a carefully calibrated epsilon (`ε · |L|² / 2`) to make the algebra work
- Manipulating complex fractional expressions with common denominators
- Applying `abs_div` to separate absolute values across division
- Chaining together a sequence of inequalities to reach the final bound

Each step built on the previous levels, showing how mathematical proofs are constructed
from carefully assembled building blocks.

## Applications and Extensions

With this theorem in hand, you now have a complete toolkit for limits of **rational
functions**. Combined with earlier results on sums and products, you can now prove:

**If `a n → L` and `c n → M` with `M ≠ 0`, then `a n / c n → L / M`.**

The proof is straightforward: first show `1/c n → 1/M` using the reciprocal theorem you
just proved, then use the product theorem to show `a n · (1/c n) → L · (1/M) = L/M`.

This completes the fundamental arithmetic of limits: sums, products, and quotients. These
are the building blocks for analyzing limits of polynomials, rational functions, and much
more complex expressions throughout calculus and analysis.

## Mastery of Technique

The reciprocal theorem showcases a crucial lesson in mathematical proof: sometimes the
\"right\" epsilon isn't the obvious choice. The expression `ε · |L|² / 2` might seem
mysterious at first, but it's precisely engineered to make the final inequalities work out.
This kind of strategic thinking—working backwards from what you need to figure out what
you should assume—is at the heart of mathematical problem-solving.

You've now mastered the essential techniques for proving limit theorems. Well done!
"
