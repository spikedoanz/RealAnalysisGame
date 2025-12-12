import Game.Levels.L12Lecture

World "Lecture13"
Level 1
Title "Monotone Subsequence"

Introduction "
# Level 1 **Big Boss:**  Monotone Subsequence

Every sequence has hidden order within it. No matter how chaotic a sequence may appear, we can always extract a subsequence that moves consistently in one direction—either always increasing (monotone) or always decreasing (antitone). This beautiful result, part of the classical Bolzano-Weierstrass theory, reveals that disorder is never complete.

Our strategy hinges on a key observation: some positions in a sequence are **peaks**—places from which the sequence never rises again. Either there are arbitrarily many such peaks (unbounded peaks), or there aren't. We'll prove that if peaks are *not* unbounded, then we can construct a monotone (non-decreasing) subsequence by cleverly avoiding the peaks entirely.

## New Definitions

**IsAPeak:** Standing at position `n`, we say it's a peak if we can look down at all future values:

`def IsAPeak {X : Type*} [LinearOrder X] (a : ℕ → X) (n : ℕ) : Prop := ∀ m > n, a m ≤ a n`

**UnBddPeaks:** A sequence has unbounded peaks if for any bound `k`, there's always another peak beyond it:

`def UnBddPeaks {X : Type*} [LinearOrder X] (a : ℕ → X) : Prop := ∀ k, ∃ n > k, IsAPeak a n`

**Conditional definition:** We can define functions by cases using `if h : condition then value₁ else value₂`. The proof `h` of the condition (or its negation) becomes available in each branch.

## The Goal

Prove that if a sequence `a : ℕ → X` does **not** have unbounded peaks, then it has a **monotone** (non-decreasing) subsequence.

The intuition: if peaks eventually stop appearing, the sequence must eventually start climbing. By taking an orbit starting beyond the last peak, each step moves to a position that's not a peak—meaning there's always somewhere higher to go next.

(In the homework, you'll prove the complementary result: sequences *with* unbounded peaks have **antitone** subsequences. Just pick the peaks themselves!)

## New Theorem

**lt_of_not_ge:** If it's not true that `m ≤ n`, then `n < m`.

This simple fact lets us convert a failed inequality into a strict one—essential for working with our conditional definition of the auxiliary sequence.

## Strategy Outline

1. **Extract witnesses:** Use `choose` to get a bound `k` beyond which there are no peaks, and for each `n > k`, get a witness `τ(n) > n` where `a(τ(n)) > a(n)`

2. **Build auxiliary sequence:** Define `τ'(n) = if n ≤ k then n+1 else τ(n)` that grows faster than identity everywhere

3. **Take the orbit:** Let `σ(n) = τ'^[n](k+1)` be the n-fold iteration starting from `k+1`

4. **Verify monotonicity:** Since `σ(n) > k` always, we're always beyond the peaks, so `a(σ(n)) ≤ a(τ'(σ(n))) = a(σ(n+1))`

Each piece builds on techniques from Lecture 12: `choose` for extracting witnesses, orbits for building subsequences, and induction for verification. Now let's make it rigorous!
"

/-- If you have a proposition `P`, you can say `if P then x else y`. -/
DefinitionDoc «if» as "if then else"

/-- `(a : ℕ → X) (n : ℕ) := ∀ m > n, a m ≤ a n`

For a sequence `a : ℕ → X` (where `X` is `ℚ` or `ℝ`) and `n : ℕ`, we say that `IsAPeak a n` if: `∀ m > n, a m ≤ a n`. -/
DefinitionDoc IsAPeak as "IsAPeak"

def IsAPeak {X : Type*} [LinearOrder X] (a : ℕ → X) (n : ℕ) : Prop := ∀ m > n, a m ≤ a n

/-- `(a : ℕ → X) := ∀ k, ∃ n > k, IsAPeak a n`

We say that a sequence `a : ℕ → X` (where `X` is `ℚ` or `ℝ`)
satisfies `UnBddPeaks a`, if its set of peaks is unbounded.-/
DefinitionDoc UnBddPeaks as "UnBddPeaks"

def UnBddPeaks {X : Type*} [LinearOrder X] (a : ℕ → X) : Prop := ∀ k, ∃ n > k, IsAPeak a n

NewDefinition IsAPeak UnBddPeaks  «if»

/-- If `¬ (m ≤ n)`, then `n < m`. -/
TheoremDoc lt_of_not_ge as "lt_of_not_ge" in "Theorems"

NewTheorem lt_of_not_ge

/--
If a sequence `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) does not have unbounded peaks, then it has a `Monotone` subsequence.
-/
TheoremDoc MonotoneSubseq_of_BddPeaks as "MonotoneSubseq_of_BddPeaks" in "aₙ"

/-- Prove this
-/
Statement MonotoneSubseq_of_BddPeaks {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (ha : ¬ UnBddPeaks a) : ∃ σ, Subseq σ ∧ Monotone (a ∘ σ) := by
change ¬ (∀ k, ∃ n > k, ∀ m > n, a m ≤ a n) at ha
push_neg at ha
choose k hk using ha
choose τ τ_gt hτ using hk
let τ' : ℕ → ℕ := fun n => if h : n ≤ k then n + 1 else τ n (lt_of_not_ge h)
have τ'_eq : ∀ n, τ' n = if h : n ≤ k then n + 1 else τ n (lt_of_not_ge h) := by intro n; rfl
have τ'_gt : ∀ n, n < τ' n := by
  intro n;
  by_cases hn : n ≤ k;
  rewrite [τ'_eq];
  bound;
  rewrite [τ'_eq];
  bound
let σ : ℕ → ℕ := fun n ↦ τ'^[n] (k+1)
have σ_eq : ∀ n, σ n = τ'^[n] (k+1) := by intro n; rfl
have hσ : ∀ n, k < σ n := by
  intro n;
  induction' n with n hn;
  rewrite [σ_eq];
  bound;
  rewrite [σ_eq];
  rewrite [← show τ' (τ'^[n] (k + 1)) = τ'^[n + 1] (k + 1) by apply succ_iterate];
  rewrite [← σ_eq];
  specialize τ'_gt (σ n);
  linarith [τ'_gt, hn]
use σ
split_ands
apply Subseq_of_Iterate
apply τ'_gt
apply Monotone_of_succ
intro n
specialize hσ n
specialize hτ (σ n) hσ
change a (σ n) ≤ a (σ (n + 1))
rewrite [show σ (n + 1) = τ'^[n+1] (k + 1) by apply σ_eq]
rewrite [← show τ' (τ'^[n] (k + 1)) = τ'^[n + 1] (k + 1) by apply succ_iterate]
rewrite [← show σ (n) = τ'^[n] (k + 1) by apply σ_eq]
rewrite [τ'_eq]
bound

Conclusion "

# 🎉 Congratulations!

You've just proved one of the most elegant results in real analysis: sequences without unbounded peaks have monotone subsequences. Let's appreciate what you accomplished.

## What You Built

Starting with just the hypothesis that peaks don't go on forever, you:

1. **Extracted structure from negation** - Used `choose` to get a bound `k` and witnesses `τ(n)` beyond which no peaks exist

2. **Patched together a global function** - Combined `n+1` (for `n ≤ k`) and `τ(n)` (for `n > k`) using `if-then-else` to create `τ'` that grows everywhere

3. **Leveraged orbits** - Applied the Lecture 12 technique of iterating `τ'` to build a strictly increasing subsequence `σ`

4. **Extracted monotonicity** - Showed that beyond the peak bound, each step must climb: `a(σ(n)) ≤ a(σ(n+1))`

The proof is a masterclass in constructive mathematics: you didn't just show a subsequence *exists*—you *built* it explicitly using orbits and witnesses.

## The Bigger Picture: A Fundamental Dichotomy

Every sequence falls into exactly one of two camps:

- **Unbounded peaks:** Infinitely many positions from which the sequence never recovers → You can extract a **non-increasing** (antitone) subsequence (your homework!)

- **Bounded peaks:** Eventually, no more peaks appear → You just proved there's a **non-decreasing** (monotone) subsequence

This dichotomy is profound: *chaos is impossible*. No matter how wild a sequence appears, somewhere within it lies monotonic order. Either it keeps hitting new peaks (descending order), or it eventually runs out of peaks (ascending order). There is no third option.

## The Technique: Conditional Construction

The `if-then-else` construct was crucial here. We needed a single function `τ'` that:
- Works for *all* natural numbers (not just those beyond `k`)
- Grows faster than identity everywhere
- Matches our witness function `τ` where it matters (beyond `k`)

The conditional definition elegantly threaded this needle. Combined with `lt_of_not_ge` to handle the logic, we converted a partially-defined witness into a globally-defined building block for our orbit.

This pattern—patching together local information into global constructions—appears throughout analysis. You've now mastered a fundamental technique.

## Looking Ahead: Bolzano-Weierstrass

In your homework, you'll prove the complementary result for sequences with unbounded peaks. The proof is actually simpler: just take the peaks themselves as your subsequence!

Then in Lecture 14, we'll combine both results with the bounded monotone sequence theorem (Lecture 12) to prove the **Bolzano-Weierstrass Theorem**:

**Every bounded sequence has a Cauchy subsequence.**

That's right—boundedness alone guarantees convergent behavior. This is one of the crown jewels of real analysis, and you've just built half of its foundation.

## What You've Mastered

✓ **Proof by cases:** Using negation and `choose` to extract witnesses from non-existence

✓ **Conditional definitions:** Building functions with `if-then-else` to patch local into global

✓ **Orbit construction:** Iterating functions to force monotonic growth

✓ **Strategic thinking:** Breaking complex proofs into: unpack hypothesis → build auxiliary objects → extract desired properties

These aren't just tricks for one theorem—they're fundamental tools you'll use throughout mathematics.

## Final Thought

You stood at the crossroads of chaos and order. You proved that beyond a certain point, if peaks cease to exist, then climbing never stops. The sequence may not increase at every step, but along some carefully chosen path—an orbit through phase space—it marches upward inexorably.

This is the power of subsequences: they let us *choose* our vantage point, focusing only on the moments that matter. And it's the power of formal proof: what seems intuitively obvious (\"if there are no peaks, something must be going up\") becomes a rigorous construction you can trust completely.

Next up: What happens when peaks *don't* stop? Spoiler: they fall forever.

**Ready for the homework? Time to make those peaks tumble down!**
"
