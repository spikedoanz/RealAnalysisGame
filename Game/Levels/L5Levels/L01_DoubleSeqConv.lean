import Game.Levels.L4PsetIntro

World "Lecture5"
Level 1
Title "Doubling a Convergent Sequence"

Introduction "
# Level 1: Doubling Convergence

After conquering the constant sequence, let's up our game: if a sequence converges, then doubling that sequence also converges, and converges to double the original limit.

## The Factory Scaling Challenge

Imagine our Machinist receives a challenge from the Engineer: 'Please double all the lengths, but maintain the same quality standards.' How should the Machinist respond?

If the Engineer demands the doubled lengths be within $\\varepsilon$ of $2L$, the Machinist can't just demand that the original process meet the original tolerance $\\varepsilon$, because

`|2 * a (n) - 2 * L| < 2 * ε`,

not `ε`. Instead, we must be more clever. Can you think of what to do?

That's right, the `ε` in the original process
is *arbitrary*, so we can play with it!
If we could get the original process can guarantee output within $\\varepsilon/2$ of $L$, then doubling that output will be within $\\varepsilon$ of $2L$.

This is the key insight: **when scaling by a constant, we need to scale our tolerance demands inversely**.

## The Mathematical Setup

Suppose we have:
- A sequence $a : \\mathbb{N} \\to \\mathbb{R}$ that converges to $L$
- A sequence $b : \\mathbb{N} \\to \\mathbb{R}$ with the property that $b(n) = 2 \\cdot a(n)$ for all $n$

We want to prove that $b$ converges to $2 \\cdot L$.

## Key Insight: Inverse Tolerance Scaling

The crucial observation is that:

$|b(n) - 2L| = |2 \\cdot a(n) - 2L| = 2 \\cdot |a(n) - L|$

So if we want $|b(n) - 2L| < \\varepsilon$, we need $2 \\cdot |a(n) - L| < \\varepsilon$, which means $|a(n) - L| < \\varepsilon/2$.

This is exactly what we can get from the convergence of $a$!

## New Tools You'll Need

**Absolute Value of Products**:
You'll need the new theorem `abs_mul` which states that for any real numbers $x$ and $y$:

$|x \\cdot y| = |x| \\cdot |y|$.

To use this theorem, you may find it convenient to
make a new hypothesis using `have` and then `rewrite` by that hypothesis. That is, you can say,

`have NewFact : |Something * SomethingElse| =
|Something| * |SomethingElse| :=
by apply abs_mul`

and then `rewrite [NewFact]` will replace `|Something * SomethingElse|` by `|Something| * |SomethingElse|` (either at the Goal, or `at` a hypothesis, if you so specify).

## Your Strategic Approach

1. Unfold the definition of convergence for the goal
2. Given any $\\varepsilon > 0$, use the convergence of $a$ with tolerance $\\varepsilon/2$. You may find it useful to separately prove the inequality `0 < ε / 2` -- which
tactic do you think will help with that?
3. Extract the witness $N$ from the convergence of $a$
4. Use the same $N$ for your sequence $b$
5. Apply the scaling hypothesis and use `abs_mul` to relate $|b(n) - 2L|$ to $|a(n) - L|$
6. Use the convergence bound for $a$ to conclude

## Why This Pattern Matters

This proof introduces the important technique of **inverse scaling** for tolerances. When you scale a sequence by a constant $c$, you need to scale your tolerance demands by $1/c$. This principle will appear again when you study:
- Products of sequences (where both factors contribute to the error)
- Derivatives (where the limit definition involves scaling by $h$)
- Integration (where Riemann sums involve scaling by partition widths)

The ability to manage how constants affect convergence is fundamental to all of analysis!
"



/-- For any real numbers `x` and `y`, we have `|x * y| = |x| * |y|`. -/
TheoremDoc abs_mul as "abs_mul" in "|x|"

NewTheorem abs_mul


/-- Prove that constant multiples of convergent sequences converge to the constant multiple of the limit.
This is the Machinist's response to scaling demands: 'If you want double the output with the same tolerance, I need half the tolerance on the original process!' -/
Statement (a b : ℕ → ℝ) (L : ℝ)
    (h : SeqLim a L) (b_scaled : ∀ n, b n = 2 * a n) :
    SeqLim b (2 * L) := by
  Hint (hidden := true) "Start by unfolding the definition: `change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |b n - 2 * L| < ε`"
  change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |b n - 2 * L| < ε
  intro ε hε
  Hint (hidden := true) "Also try unfolding the definition in `h`: `change ∀ ε₁ > 0, ∃ N₁ : ℕ, ∀ n ≥ N₁, |a n - L| < ε₁ at h`"
  change ∀ ε₁ > 0, ∃ N₁ : ℕ, ∀ n ≥ N₁, |a n - L| < ε₁ at h
  Hint (hidden := true) "Apply the convergence of `a` with tolerance `ε / 2`. Try: `specialize h (ε / 2)`"
  specialize h (ε / 2)
  Hint (hidden := true) (strict := true) "Now we'll need to show that `0 < ε / 2`. Try: `have eps_half_pos : 0 < ε / 2 := by linarith [hε]`"
  have eps_half_pos : 0 < ε / 2 := by bound --linarith [hε]
  specialize h eps_half_pos
  choose N hN using h
  use N
  intro n hn
  specialize b_scaled n
  rewrite [b_scaled]
  clear b b_scaled eps_half_pos
  Hint (strict := true) (hidden := true) "You can't use `abs_mul` just yet, because you don't have a product of things inside the absolute values! So first factor out the 2: `have factor : 2 * a n - 2 * L = 2 * (a n - L) := by ring_nf`"
  have factor : 2 * a n - 2 * L = 2 * (a n - L) := by ring_nf
  rewrite [factor]
  clear factor
  Hint (hidden := true) (strict := true) "Apply the absolute value of products: `have abs_factor : |2 * (a n - L)| = |2| * |a n - L| := by apply abs_mul`"
  have abs_factor : |2 * (a n - L)| = |2| * |a n - L| := by apply abs_mul
  rewrite [abs_factor]
  clear abs_factor
  specialize hN n hn
  clear hn
  Hint (hidden := true) (strict := true) "The `linarith` tactic won't work
  yet, because it'll get stuck on that `|2|`; do you remember what to do
  to normalize the numerical value to just `2`?"
  norm_num
  Hint (hidden := true) (strict := true) "And finally, this is where the powerful `linarith` tactic can take over. Remember to feed it (in brackets) the hypothesis (or hypotheses, separated by commas) which you want to manipulate to turn into the Goal."
  bound --linarith [hN]

Conclusion "
# 🎉 Brilliant Work! 🎉

You've mastered your first true theorem of analysis! Let's celebrate what you accomplished and understand the deeper patterns.

**What you just proved:**
If a sequence converges to a limit, then any constant multiple of that sequence converges to the constant multiple of the limit. In factory terms: 'If I can meet quality standards, I can also meet those same standards when scaling my output—I just need to be more precise with my inputs!'

**The Elegant Strategy:**
Your proof used the **inverse scaling** principle:
1. **Tolerance inversion**: To achieve tolerance ε for doubled output, demand tolerance ε/2 for original input
2. **Algebraic factoring**: `2 * a n - 2 * L = 2 * (a n - L)` revealed the structure
3. **Absolute value scaling**: `|2 * x| = |2| * |x|`, followed by `norm_num`, converted the factored form to the needed bound
4. **Linear arithmetic**: The final `linarith [hN]` combined `2 * |a n - L| < 2 * (ε / 2) = ε`

## Check in, in Natural Language

Let's again step back from the formal Lean proof and understand what we just proved in plain English.

**Theorem (in natural language):** If a sequence of real numbers converges to some limit, then the sequence formed by doubling each term converges to double the original limit.

**Proof:** Suppose sequence $a_n$ converges to $L$, and we want to show that $b_n = 2 \\cdot a_n$ converges to $2L$.

By definition, we need to show that for any tolerance $\\varepsilon > 0$, we can find a point $N$ such that for all $n \\geq N$, we have $|b_n - 2L| < \\varepsilon$.

Here's the key insight: Since $a_n$ converges to $L$, we can make $|a_n - L|$ arbitrarily small. Specifically, we can find an $N$ such that $|a_n - L| < \\varepsilon/2$ for all $n \\geq N$.

Now, for any $n \\geq N$:
$$|b_n - 2L| = |2a_n - 2L| = |2(a_n - L)| = 2|a_n - L| < 2 \\cdot \\frac{\\varepsilon}{2} = \\varepsilon$$

Therefore, $b_n$ converges to $2L$, completing the proof.
**QED**

So what do you think? Do you prefer the natural langauge version, or the formal version? (It's a real question! Please tell me.)

"
