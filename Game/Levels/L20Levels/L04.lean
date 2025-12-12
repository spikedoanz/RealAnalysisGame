import Game.Levels.L20Levels.L03

World "Lecture20"
Level 4
Title "Sequential Criterion for Limits (Forward Direction)"
Introduction "
# Level 4: Sequential Criterion for Limits

We now have two notions of limits in our arsenal:
1. **Function limits:** `FunLimAt f L c` means `f(x) → L` as `x → c`
2. **Sequence limits:** `SeqLim x L` means `xₙ → L` as `n → ∞`

Could these concepts be connected? It's **mathematics**, how could they not!

In this level, we'll prove the first half of the **Sequential Criterion for Limits**.

## The Sequential Criterion (Forward Direction)

**Theorem:** If `f` has limit `L` at `c`, then for *every* sequence `(xₙ)` with `xₙ → c` and `xₙ ≠ c`, we have `f(xₙ) → L`.

In other words: function limits can be **tested** using sequences!

## Why This Matters

This theorem is incredibly useful because:
- It connects two different limit concepts
- It lets us use sequence intuition to understand function limits
- It may be easier to work with certain sequences than with the `ε-δ` definition

## The Proof Strategy

**Given:** `FunLimAt f L c` and a sequence `(xₙ)` with `xₙ → c` and `xₙ ≠ c`.

**Want:** To show `f(xₙ) → L`, i.e., for all ε > 0, eventually `|f(xₙ) - L| < ε`.

**How:**
1. Given ε > 0, use `FunLimAt` to get δ > 0 such that `|x - c| < δ` and `x ≠ c` implies `|f(x) - L| < ε`
2. Use `SeqLimit` to get N such that for all n ≥ N, we have `|xₙ - c| < δ`
3. For n ≥ N, we know `xₙ ≠ c` and `|xₙ - c| < δ`, so `|f(xₙ) - L| < ε`

## Your Challenge

Prove the forward direction of the sequential criterion:

`FunLimAt f L c → (∀ x : ℕ → ℝ, (∀ n, x n ≠ c) → SeqLimit x c → SeqLimit (fun n ↦ f (x n)) L)`

**Hint:** After introducing all the hypotheses, introduce `ε` and `hε`. Use `hf` with `ε` to get `δ` and its properties. Then use `hx` with `δ` to get `N`. Use this `N` to show that the sequence `f(xₙ)` converges to `L`.

"

/--
If a function `f` has limit `L` at point `c`, then for every sequence `(xₙ)` converging to `c` with `xₙ ≠ c`, the sequence `f(xₙ)` converges to `L`.
-/
TheoremDoc SeqLim_of_FunLimAt as "SeqLim_of_FunLimAt" in "f(x)"

Statement SeqLim_of_FunLimAt {f : ℝ → ℝ} {L c : ℝ}
    (hf : FunLimAt f L c) :
    ∀ x : ℕ → ℝ, (∀ n, x n ≠ c) → SeqLim x c → SeqLim (fun n ↦ f (x n)) L := by
intro x hxc hx
intro ε hε
choose δ hδ hfδ using hf ε hε
choose N hN using hx δ hδ
use N
intro n hn
specialize hN n hn
specialize hxc n
apply hfδ (x n) hxc hN

Conclusion "
## What We've Learned

This theorem is a **bridge between two worlds**: sequences and functions!

### Why This Matters

The Sequential Criterion gives us two powerful tools:

1. **Testing function limits with sequences**: Instead of wrestling with `ε`-`δ`, we can use specific sequences
2. **Connecting different areas of analysis**: Sequence convergence and function limits are deeply related

### The Proof Strategy: Composing Guarantees

The proof elegantly chains together two limit definitions:

1. **Function limit** gives us: `ε → δ` (tolerance on output gives tolerance on input)
2. **Sequence limit** gives us: `δ → N` (tolerance on distance from `c` gives a threshold index)
3. **Composition**: `ε → δ → N` (tolerance on output gives threshold for the sequence `f(xₙ)`)

This is a beautiful example of **modular reasoning**: we use the guarantees from each definition without re-proving them!

### Looking Ahead

There's a converse to this theorem (the backward direction): if `f(xₙ) → L` for **every** sequence `xₙ → c` with `xₙ ≠ c`, then `FunLimAt f L c`.

Together, these give us a complete equivalence:

`FunLimAt f L c ⟺ (for all sequences xₙ → c with xₙ ≠ c, we have f(xₙ) → L)`

This means we can choose our weapon: use `ε`-`δ` when convenient, or use sequences when that's easier!

**Key insight:** Different formulations of the same concept give us flexibility in proofs. The sequential characterization often provides better intuition than the abstract `ε`-`δ` definition.
"
