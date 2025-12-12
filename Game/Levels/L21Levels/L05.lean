import Game.Levels.L20Lecture

World "Lecture21"
Level 1
Title "Sequential Criterion for Limits (Backward Direction)"
Introduction "
# Level 1: Sequential Criterion for Limits (Backward Direction)

Previously, we proved that function limits imply sequential limits. Now we prove the **converse**: if function values converge for *every* appropriate sequence, then the function has a limit!

## The Sequential Criterion (Backward Direction)

**Theorem:** Suppose that for *every* sequence `(xₙ)` with `xₙ → c` and `xₙ ≠ c`, we have `f(xₙ) → L`. Then `FunLimAt f L c`.

This says: if sequences **test** the limit and all tests pass, then the function limit exists!

## Why This Direction Is Harder

The forward direction was straightforward: we had `δ` from the function limit and used it directly.

For the backward direction, we use **proof by contradiction**:
- Assume `FunLimAt f L c` is false
- Then `∃ ε > 0` such that `∀ δ > 0`, `∃ x` with `|x - c| < δ`, `x ≠ c`, but `|f(x) - L| ≥ ε`
- We'll construct a **problematic sequence** by choosing such an `x` for each `δ = 1/(n+1)`
- This sequence converges to `c` but `f(xₙ)` does *not* converge to `L`, contradicting our hypothesis!

## The Proof Strategy

**Given:** `∀ x : ℕ → ℝ, (∀ n, x n ≠ c) → SeqLim x c → SeqLim (fun n ↦ f (x n)) L`

**Want:** `FunLimAt f L c`, i.e., `∀ ε > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f(x) - L| < ε`

**Proof by contradiction:**
1. **Assume negation:** `∃ ε > 0` such that `∀ δ > 0`, the implication fails
2. **Extract witnesses:** Use `choose` to get `ε` and a function `g` that produces counterexamples
3. **Construct sequence:** Define `xₙ = g(1/(n+1))` with `|xₙ - c| < 1/(n+1)` and `|f(xₙ) - L| ≥ ε`
4. **Show convergence:** Prove `xₙ → c` (since `|xₙ - c| < 1/(n+1) → 0`)
5. **Apply hypothesis:** Get `f(xₙ) → L` from our assumption
6. **Derive contradiction:** This contradicts `|f(xₙ) - L| ≥ ε > 0`

## Your Challenge

Prove the backward direction of the sequential criterion:

`(∀ x : ℕ → ℝ, (∀ n, x n ≠ c) → SeqLim x c → SeqLim (fun n ↦ f (x n)) L) → FunLimAt f L c`

**Key tactics to use:**
- `by_contra` to assume the negation
- `push_neg` to simplify the negated statement
- `choose` to extract witnesses from existential statements
- The Archimedean property to handle `1/(n+1) → 0`

**Hint:** The trickiest part is proving that your constructed sequence `xₙ` actually converges to `c`. You'll need to use the Archimedean property to find `N` such that `1/N < δ`, then show that for `n ≥ N`, we have `1/(n+1) ≤ δ`.

"

/--
If for every sequence `(xₙ)` converging to `c` with `xₙ ≠ c`, the sequence `f(xₙ)` converges to `L`, then the function `f` has limit `L` at point `c`.
-/
TheoremDoc FunLim_of_SeqLim as "FunLim_of_SeqLim" in "f(x)"

Statement FunLim_of_SeqLim {f : ℝ → ℝ} {L c : ℝ}
    (h : ∀ x : ℕ → ℝ, (∀ n, x n ≠ c) → SeqLim x c → SeqLim (fun n ↦ f (x n)) L) :
    FunLimAt f L c := by
by_contra hf
change ¬ (∀ ε > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x - L| < ε) at hf
push_neg at hf
choose ε hε hδ using hf
choose g hg_ne_c hg_lt_δ hg using hδ
let x : ℕ → ℝ := fun n ↦ (g (1 / (n + 1)) (by bound))
have hxc : ∀ n, x n ≠ c := by
    intro n;
    apply (hg_ne_c (1 / (n + 1)) (by bound))
have hx_lim : SeqLim x c := by
    intro δ hδ_pos
    choose N hN using ArchProp hδ_pos
    use N
    intro n hn
    have f : |x n - c| < 1 / (n + 1) := by apply hg_lt_δ (1 / (n + 1)) (by bound)
    have f2 : 1 / (n + 1) ≤ δ := by
        have hn' : (N : ℝ) ≤ n := by norm_cast
        have f2' : 0 < 1 / δ := by bound
        have hN' : (0 : ℝ) < N := by linarith [hN, f2']
        have npos : (0 : ℝ) < n := by linarith [hN', hn']
        have hn'' : (1 : ℝ) / n ≤ 1 / N := by bound
        have hn''' : (1 : ℝ) / (n + 1) ≤ 1 / n := by field_simp; bound
        have ff : (1 : ℝ) / N < δ := by field_simp at ⊢ hN; apply hN
        linarith [hn''', hn'', ff]
    linarith [f, f2]
choose N hN using h x hxc hx_lim ε hε
specialize hN N (by bound)
specialize hg (1 / (N + 1)) (by bound)
linarith [hN, hg]

Conclusion "
# Congratulations!

You've just proved one of the most powerful and elegant results connecting sequences and function limits!

## What You Accomplished

The **Sequential Criterion (Backward Direction)** establishes that:

*If every sequence test passes, then the function limit exists.*

This is remarkable because it gives us a **sequential characterization** of function limits. We can now think about function limits in two equivalent ways:
- **ε-δ definition:** Traditional analytical approach
- **Sequential approach:** Test with all possible sequences

## The Power of Proof by Contradiction

Your proof showcased a beautiful contradiction argument:
1. **Assume** the function limit doesn't exist
2. **Construct** a problematic sequence using the failure of the ε-δ definition
3. **Show** this sequence converges to `c` but `f(xₙ)` doesn't converge to `L`
4. **Contradiction!** This violates our sequential hypothesis

This technique - constructing counterexample sequences from ε-δ failures - is a fundamental tool in real analysis.

## Why This Matters

Combined with the forward direction, we now have:

**Sequential Criterion for Function Limits (Complete):**
`FunLimAt f L c ↔ (∀ x : ℕ → ℝ, (∀ n, x n ≠ c) → SeqLim x c → SeqLim (fun n ↦ f (x n)) L)`

This equivalence is incredibly useful because:
- Sometimes sequences are easier to work with than ε-δ arguments
- It connects the discrete world (sequences) with the continuous world (functions)
- It provides a bridge between different areas of analysis

## Looking Ahead

This sequential criterion will be essential for:
- Proving properties of continuous functions
- Understanding derivatives (coming up next!)
- Advanced topics like uniform convergence and compactness

You've mastered a fundamental tool that working mathematicians use regularly. Well done!

"
