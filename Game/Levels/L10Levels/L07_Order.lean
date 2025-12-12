import Game.Levels.L10Levels.L06_Prod

World "Lecture10"
Level 2
Title "Order Limit Theorem"

Introduction "
# Level 2: Order Limit Theorem

So far we've focused on algebraic operations with limits. Now we explore how limits interact with **inequalities**.

**The Question:** If every term of a sequence satisfies `a n ≤ K`, does the limit also satisfy `L ≤ K`?

The answer is **YES**! Limits preserve weak inequalities. This is intuitive: if a sequence is always below some ceiling `K`, it can't suddenly jump above `K` in the limit.

**New Definition: `SeqBddBy`**

We say a sequence `a` is **bounded by** `M` if `a n ≤ M` for all `n`.

Note the difference:
- `SeqBdd a`: sequence is bounded (both above and below), i.e., `|a n| ≤ M`
- `SeqBddBy a M`: sequence is bounded **above** by `M`, i.e., `a n ≤ M`

**The Theorem:** If `a n → L` and `a n ≤ K` for all `n`, then `L ≤ K`.

**Proof Strategy: Contradiction!**

Assume `L > K`. Then `L - K > 0`. Use this as your `ε` in the definition of convergence:
- There exists `N` such that `|a N - L| < L - K`
- This means `a N > L - (L - K) = K`
- But we know `a N ≤ K` by hypothesis
- **Contradiction!**

The key insight: if the limit were strictly above `K`, then eventually the terms would have to be above `K` too (by convergence). But they're not!

**Warning:** Strict inequalities are NOT preserved! If `a n < K` for all `n`, we can only conclude `L ≤ K`, not `L < K`.

Example: `a n = 1/n` satisfies `a n > 0` for all `n`, but `lim a n = 0`, which is not strictly positive.

This theorem can also be used to prove the **Squeeze Theorem** (which we already did directly).
"

/-- `(a : ℕ → ℝ) (M : ℝ) := ∀ n, a n ≤ M`

A sequence `a : ℕ → ℝ` is *bounded by* (`SeqBddBy` holds) `M : ℝ` if, for all `n`, `a n ≤ M`, for all `n`. -/
DefinitionDoc SeqBddBy as "SeqBddBy"

NewDefinition SeqBddBy

def SeqBddBy (a : ℕ → ℝ) (M : ℝ) : Prop :=
  ∀ n, a n ≤ M

/--
If a sequence `a` converges to `L` and `a n ≤ K` for all `n`, then `L ≤ K`.
-/
TheoremDoc OrderLimLe as "OrderLimLe" in "aₙ"

/-- Prove this
-/
Statement OrderLimLe (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (K : ℝ) (hK : SeqBddBy a K) :
    L ≤ K := by
by_contra hL
have hL' : K < L := by bound
have hLK : 0 < (L - K) := by linarith [hL']
choose N hN using ha (L - K) hLK
specialize hN N (by bound)
rewrite [abs_lt] at hN
have f1 : L - (L - K) < a N := by linarith [hN.1]
have f2 : K = L - (L - K) := by ring_nf
specialize hK N
linarith [f2, hK, f1]

Conclusion "
Excellent work! You've proven that limits respect inequalities.

**What We Learned:**

The Order Limit Theorem tells us that **weak inequalities pass to the limit**:
- If `a n ≤ K` for all `n` and `a n → L`, then `L ≤ K`

**Why Contradiction Works Here:**

This is a great example of when proof by contradiction is the natural approach. We want to prove `L ≤ K`, which is hard to show directly. But assuming `L > K` gives us a concrete positive number `L - K` that we can use as `ε` in the convergence definition. The contradiction writes itself!

**The Symmetric Result:**

There's a symmetric version (left as an exercise): if `K ≤ a n` for all `n` and `a n → L`, then `K ≤ L`. This says sequences bounded **below** have limits bounded below.

**Important Limitation:**

Remember: **strict inequalities don't pass to the limit!**

If `a n < K` for all `n`, we can only conclude `L ≤ K`, not `L < K`.

Counter-example: `a n = 1/n` satisfies `0 < a n` for all `n`, but `lim a n = 0`.

The limit can equal the boundary even when the sequence never touches it!

**Coming Up: Applications**

The Order Limit Theorem is the foundation for:
- **Squeeze Theorem (Sandwich Theorem):** If `a n ≤ b n ≤ c n` and `a n → L` and `c n → L`, then `b n → L`
- **Monotone Convergence Theorem:** Bounded monotone sequences converge
- **Comparison tests** for series
- Many other fundamental results in analysis

This theorem lets us compare sequences and transfer information about one sequence to another via inequalities. Very powerful!
"
