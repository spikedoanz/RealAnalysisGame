import Game.Levels.L22Levels.L02
import Mathlib.Tactic.Rify

open Finset

attribute [grind] inv_lt_of_inv_lt₀
attribute [grind] one_mul
attribute [grind] Mathlib.Tactic.Zify.natCast_le._simp_1
attribute [grind] Mathlib.Tactic.Qify.intCast_le._simp_1
attribute [grind] Mathlib.Tactic.Rify.ratCast_le._simp_1
attribute [grind] Int.cast_natCast
attribute [grind] Rat.cast_natCast

World "Lecture22"
Level 3
Title "Integration"
Introduction "
# Level 3: Integration!

Welcome to the grand finale of our uniformity journey! After mastering function composition and uniform convergence, we're ready to tackle one of calculus's crown jewels: **integration**. But this isn't your typical calculus course—we're going to build integration from the ground up using the rigorous foundations you've been developing.

## From Continuous Functions to Areas

You've spent this lecture understanding how functions behave under various kinds of limits. Now we're going to use sequences in a completely different way: to define what it means to find the area under a curve.

The beautiful connection? Integration is fundamentally about taking a limit of approximations—and everything you've learned about when limits preserve nice properties will be crucial here.

## The Riemann Revolution

In the 1850s, Bernhard Riemann formalized what we intuitively think of as \"area under a curve.\" His insight was brilliant: approximate the area using rectangles, make the rectangles thinner and thinner, and take the limit.

But here's the key question: **does this limit always exist?** And when it does exist, **is it unique?**

These questions connect directly to everything you've been learning about convergence!

## Our Approach: Right Endpoints

We'll use **Riemann sums with right endpoints**:

`RiemannSum (f : ℝ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  (b - a) / N * ∑ i ∈ range N, f (a + (i + 1) * (b - a) / N)`

**Translation**: We divide $[a,b]$ into $N$ equal pieces of width $(b-a)/N$. For each piece, we make a rectangle whose height is the function value at the **right endpoint** of that piece. The Riemann sum is the total area of all these rectangles.

## The Fundamental Definitions

**HasIntegral**: A function has integral $I$ if the sequence of Riemann sums converges to $I$:

`HasIntegral (f : ℝ → ℝ) (a b : ℝ) (I : ℝ) : Prop :=
  SeqLim (fun N ↦ RiemannSum f a b N) I`

**IntegrableOn**: A function is integrable on $[a,b]$ if *some* integral exists:

`IntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ I, SeqLim (fun N ↦ RiemannSum f a b N) I`

Notice the beautiful parallel to our earlier work: we're asking when a sequence (of Riemann sums) has a limit!

## Your Mission: Compute $\\int_a^b x \\, dx$

You're going to prove that $f(x) = x$ is integrable on $[a,b]$, and find the exact value of its integral. From calculus, you expect this to be $\\frac{b^2 - a^2}{2}$, but now you'll **prove** it rigorously using the definition.

## The Summation Toolkit

To work with Riemann sums, you'll need several key identities about finite sums:

- `sum_add_distrib`: $\\sum_{i \\in s} (f(i) + g(i)) = \\sum_{i \\in s} f(i) + \\sum_{i \\in s} g(i)$
- `sum_const`: $\\sum_{i \\in s} c = c \\cdot |s|$
- `card_range`: $|\\{0, 1, \\ldots, n-1\\}| = n$
- `sum_div`: $\\sum_{i \\in s} (f(i) / c) = (\\sum_{i \\in s} f(i)) / c$
- `sum_mul`: $\\sum_{i \\in s} (f(i) \\cdot c) = (\\sum_{i \\in s} f(i)) \\cdot c$

And the crucial identity you'll need:
- `sum_range_add_one`: $\\sum_{i=0}^{n-1} (i + 1) = \\frac{n(n+1)}{2}$

## The Strategy: Exact Computation

Unlike our previous proofs where we estimated errors, here you'll compute the Riemann sums **exactly**. You'll show that:

$$\\text{RiemannSum}(f, a, b, n) = \\frac{b^2 - a^2}{2} + \\frac{(b-a)^2}{2n}$$

As $n \\to \\infty$, the error term $\\frac{(b-a)^2}{2n}$ vanishes, giving you the integral $\\frac{b^2 - a^2}{2}$.

## The Connection to Earlier Work

This integration problem brings together everything you've learned:
- **Sequence limits**: The integral is defined as a limit
- **Careful estimation**: You need to show the error term approaches zero
- **Algebraic precision**: The summation identities must be applied carefully
- **Archimedean property**: To show you can make the error arbitrarily small

## Why This Matters

You're not just computing one integral—you're seeing how the entire theory of integration is built on the foundation of limits. Every time you integrate a function in calculus, you're implicitly using this limiting process.

Moreover, the question of **when** functions are integrable connects deeply to continuity, and ultimately to the uniform convergence concepts you've mastered.

## A Historical Note

In 1675, Leibniz conceived of integration as the sum of infinitely many infinitesimally thin rectangles. His insight was profound, but his methods lacked the rigorous foundation we need today. In the 1850s, Riemann formalized Leibniz's intuitive idea using the theory of limits, giving us the precise definition we now use.
Before Riemann, integration was largely based on \"obvious\" geometric intuition—but Riemann showed how to make the notion of \"area\" precise using limits.

Your proof will follow in Riemann's footsteps, showing that even something as \"simple\" as $\\int x \\, dx$ requires careful analysis when done rigorously.

## Your Challenge

Prove that $f(x) = x$ is integrable on $[a,b]$ for $a < b$:

**Lean signature**: `IntegrableOn (fun x ↦ x) a b`

Ready to compute your first rigorous integral? The Riemann sums are waiting, and the arithmetic (while intricate) will lead you to a beautiful conclusion!

*Hint*: Use $(b^2-a^2)/2$ as your proposed integral value, and be prepared for some satisfying algebraic manipulations! 📐
"

noncomputable def RiemannSum (f : ℝ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  (b - a) / N * ∑ i ∈ range N, f (a + (i + 1) * (b - a) / N)

/-- `(f : ℝ → ℝ) (a b : ℝ) (N : ℕ) :=
  (b - a) / N * ∑ i ∈ range N, f (a + (i + 1) * (b - a) / N)`


The Riemann sum of `f` from `a` to `b` with `N` subintervals.
-/
DefinitionDoc RiemannSum as "RiemannSum"

def HasIntegral (f : ℝ → ℝ) (a b : ℝ) (I : ℝ) : Prop :=
  SeqLim (fun N ↦ RiemannSum f a b N) I


/-- `(f : ℝ → ℝ) (a b : ℝ) (I : ℝ) := SeqLim (fun N ↦ RiemannSum f a b N) I`

A function `f : ℝ → ℝ` has integral `I` from `a` to `b` if the sequence of Riemann sums converges to `I`.
-/
DefinitionDoc HasIntegral as "HasIntegral"

def IntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ I, HasIntegral f a b I

/-- `(f : ℝ → ℝ) (a b : ℝ) := ∃ I, HasIntegral f a b I`

A function `f : ℝ → ℝ` is `IntegrableOn` the interval `a` to `b` if there exists some `I` so that the integral $\\int_a^b f(x)dx$ converges and equals `I`.
-/
DefinitionDoc IntegrableOn as "IntegrableOn"


NewDefinition RiemannSum HasIntegral IntegrableOn

/--
Summation distributes: `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i`
-/
TheoremDoc Finset.sum_add_distrib as "sum_add_distrib" in "∑aₙ"

/--
Summation of a constant: `∑ i ∈ s, c = c * s.card`.
-/
TheoremDoc Finset.sum_const as "sum_const" in "∑aₙ"

/--
Range cardinality: `card (range n) = n`.
-/
TheoremDoc Finset.card_range as "card_range" in "∑aₙ"


/--
Summation division: `∑ i ∈ s, (f i / c) = (∑ i ∈ s, f i) / c`.
-/
TheoremDoc Finset.sum_div as "sum_div" in "∑aₙ"


/--
Summation multiplication: `∑ i ∈ s, (f i * c) = (∑ i ∈ s, f i) * c`.
-/
TheoremDoc Finset.sum_mul as "sum_mul" in "∑aₙ"

theorem sum_range_add_one (n : ℕ) : ∑ i ∈ range n, ((i : ℝ) + 1) = (n * (n + 1)) / 2 := by
  induction' n with n hn
  bound
  rewrite [sum_range_succ]
  rewrite [hn]
  field_simp
  push_cast
  ring_nf

/--
The sum `∑ i ∈ range n, ((i : ℝ) + 1) = (n * (n + 1)) / 2`.
-/
TheoremDoc sum_range_add_one as "sum_range_add_one" in "∑aₙ"

NewTheorem Finset.sum_add_distrib Finset.sum_const Finset.card_range Finset.sum_div
  Finset.sum_mul sum_range_add_one


Statement {a b : ℝ} (hab : a < b) :
    IntegrableOn (fun x ↦ x) a b := by
use (b^2-a^2)/2
intro ε hε
have bnd : 0 < 2 * ε / (b - a) ^ 2 := by bound
have bndinv : 0 < 1 / (2 * ε / (b - a) ^ 2) := by bound
choose N hN using ArchProp bnd
use N
intro n hn
have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
have Npos : (0 : ℝ) < N := by linarith [bndinv, hN]
have npos : (0 : ℝ) < n := by linarith [Npos, hn']
have f1 : (fun N => RiemannSum (fun x => x) a b N) n - (b ^ 2 - a ^ 2) / 2  = (b-a)^2 / (2 * n) := by
  change ((b - a) / n * (∑ i ∈ range n, (a + (i + 1) * (b - a) / n))) - (b ^ 2 - a ^ 2) / 2  = _
  rewrite [show ∑ i ∈ range n, (a + (i + 1) * (b - a) / n) =
    (∑ i ∈ range n, a) +
    ∑ i ∈ range n, ((i + 1) * (b - a) / n) by apply sum_add_distrib]
  rewrite [show ∑ i ∈ range n, a = #(range n) • a by apply sum_const]
  rewrite [show #(range n) = n by apply card_range]
  rewrite [show ∑ i ∈ range n, ((i + 1) * (b - a) / n) = (∑ i ∈ range n, (i + 1) * (b - a)) / n by rewrite [← sum_div]; rfl]
  rewrite [show (∑ i ∈ range n, (i + 1) * (b - a)) / n = (∑ i ∈ range n, (i + 1 : ℝ)) * (b - a) / n by rewrite [← sum_mul]; rfl]
  rewrite [show ∑ i ∈ range n, ((i : ℝ) + 1) = n * (n + 1) / 2  by apply sum_range_add_one]
  field_simp
  ring_nf
rewrite [f1]
have f2 : 0 ≤ (b - a) ^ 2 / (2 * n) := by bound
rewrite [abs_of_nonneg f2]
field_simp
field_simp at hN
have f3 : 2 * ε * N ≤ 2 * ε * n := by bound
rewrite [show 2 * ε * n = 2 * n * ε by ring_nf] at f3
linarith [hN, f3]

Conclusion "
# Level 3 Conclusion: The Art of Exact Computation

Bravo! You've just completed your first rigorous integration proof—and what a journey it was! You didn't just compute an integral; you built it from the ground up using the fundamental definition, proving that the intuitive notion of \"area under a curve\" has a precise mathematical meaning.

## What You Just Accomplished

You proved that $\\int_a^b x \\, dx = \\frac{b^2 - a^2}{2}$ using nothing but:
- The definition of integration as a limit of Riemann sums
- Careful algebraic manipulation of finite sums
- The Archimedean property to control convergence

This is **pure mathematics**—no hand-waving, no appeals to geometric intuition, just rigorous logical reasoning.

## The Beauty of Exact Computation

Look back at your proof's centerpiece calculation:

`RiemannSum (fun x ↦ x) a b n - (b² - a²)/2 = (b - a)²/(2n)`

This isn't an approximation or estimate—it's an **exact formula**. You showed that the error between the $n$-th Riemann sum and the true integral is precisely $(b-a)^2/(2n)$. As $n \\to \\infty$, this error vanishes at the predictable rate of $1/n$.

This kind of exact computation is one of the most satisfying experiences in mathematics!

## The Summation Symphony

Your proof orchestrated a beautiful sequence of summation identities:

1. **Decomposition**: `sum_add_distrib` split the Riemann sum into manageable pieces
2. **Constant handling**: `sum_const` and `card_range` evaluated the trivial sum
3. **Factor extraction**: `sum_div` and `sum_mul` isolated the interesting terms
4. **The grand finale**: `sum_range_add_one` gave you the exact value $\\frac{n(n+1)}{2}$

Each step was essential, and the final algebraic simplification revealed the beautiful error term $(b-a)^2/(2n)$.

## Riemann's Vision Realized

You've just walked in Riemann's footsteps! In the 1850s, he revolutionized calculus by showing that \"area under a curve\" could be defined precisely using limits. Your proof demonstrates exactly how this works for the simple but fundamental case $f(x) = x$.

Before Riemann, integration was largely geometric intuition. After Riemann (and after your proof!), integration is **analysis**—the rigorous study of limits.

## The Connection to Uniformity

Notice something beautiful: this integration proof connects to everything you've learned about convergence. The sequence of Riemann sums converges to the integral, and the rate of convergence is **uniform** across all intervals $[a,b]$ with the same length $(b-a)$.

The error term $(b-a)^2/(2n)$ depends only on the interval length, not on the specific location or any pathological behavior. This uniformity is why integration of continuous functions works so cleanly.

## Technical Mastery: The Archimedean Finale

Your use of the Archimedean property at the end was masterful:

`choose N hN using ArchProp (show 0 < 2 * ε / (b - a)^2 by bound)`

This single line encapsulates a profound idea: for any desired accuracy $\\varepsilon$, you can find $N$ large enough that $\\frac{(b-a)^2}{2N} < \\varepsilon$. The Archimedean property guarantees that such an $N$ exists—completing the rigorous proof that your sequence converges.

## From Specific to General

While you proved integrability for just $f(x) = x$, you've learned the **method** that works for all \"nice\" functions:

1. Compute the Riemann sum exactly using summation identities
2. Show the difference from the proposed integral has a specific form
3. Use properties of real numbers (like the Archimedean property) to show this difference vanishes

This template will serve you well for more complex integrals!

## The Deeper Mathematical Lesson

This level taught you that rigorous mathematics often involves:
- **Exact computation** rather than just estimation
- **Algebraic virtuosity** with summation formulas
- **Patience** with detailed calculations that reveal deeper truths

The final result $\\int_a^b x \\, dx = \\frac{b^2-a^2}{2}$ is the same as in calculus, but now you **know why it's true** at the foundational level.

## A Moment of Historical Perspective

You've just completed work that would have impressed the great analysts of the 19th century. The transition from intuitive calculus to rigorous analysis was one of the major mathematical achievements of that era, and you've experienced this transition firsthand.

## Looking Forward: The Integration Universe

Your success with $\\int x \\, dx$ opens the door to the entire theory of integration:
- More complex polynomials (using similar summation techniques)
- Transcendental functions (requiring different approaches)
- Functions that aren't integrable (where the Riemann sum limits don't exist)
- Advanced integration theories (Lebesgue integration, measure theory)

You now understand integration not as a collection of techniques, but as a profound concept about **limits and convergence**.

## The Ultimate Achievement

You've proven that one of the most basic operations in calculus—computing $\\int x \\, dx$—rests on sophisticated foundations involving:
- Sequence convergence
- Algebraic manipulation
- Properties of real numbers
- Careful logical reasoning

This is **analysis**—the art of making calculus rigorous. And you've mastered a beautiful piece of it.

## Final Reflection

Integration bridges the discrete (Riemann sums) and the continuous (the integral). Your proof shows exactly how this bridge is built: through the limiting process that you've now seen in multiple contexts throughout this lecture.

From function composition to uniform convergence to integration, you've seen the theme repeated: **the right kind of limit preserves the properties we care about**.

Congratulations on completing this mathematical journey! You've moved from calculus student to analyst. The precise, rigorous, beautiful world of real analysis is now yours to explore. 🎯✨

*Ready for even more challenging integrals? The techniques you've mastered will serve as your foundation!*
"
