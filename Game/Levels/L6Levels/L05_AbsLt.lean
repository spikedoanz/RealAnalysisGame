import Game.Levels.L6Levels.L04_Cases'

World "Lecture6"
Level 6
Title "AbsLe"

Introduction "
# Level 6: AbsLe - Working with Absolute Values in Convergence

Now that you've mastered the complete And/Or toolkit, it's time to apply these skills to a fundamental aspect of real analysis: working with absolute values in the context of sequence convergence. This level introduces you to one of the most useful tools for manipulating absolute value inequalities.

You now have the full And/Or matrix \"Cheat Sheet\":

|           | ∧        | ∨      |
|-----------|----------|--------|
| **Goal**  | `split_ands`    | `left`/`right`  |
| **Hypothesis** | `h.1`, `h.2` | `cases'` |

Remember our definition of sequence convergence: `SeqLim a L` means that for any `ε > 0`, there exists an `N` such that for all `n ≥ N`, we have `|a n - L| < ε`. The absolute value here captures the idea that the sequence terms can approach the limit from either direction—they might be slightly above L or slightly below L, but either way, they're getting close.

However, sometimes we need to extract more specific information from this absolute value condition. We might need to know that the sequence terms are not just close to L, but specifically that they're bounded below by `L - ε` or bounded above by `L + ε`. This is where the `abs_lt` theorem becomes invaluable.

The key insight is that `|x| < y` is equivalent to saying both `-y < x` AND `x < y`. This gives us a way to \"unpack\" absolute value statements into more manageable pieces that we can work with using our And/Or toolkit.

## New Tools You'll Need

**`abs_lt`**: This theorem states that `|x| < y` if and only if `-y < x ∧ x < y`. This allows you to convert between absolute value inequalities and conjunction of regular inequalities, making them easier to work with in proofs.

"


/-- This says that `|x| < y` if and only if `-y < x ∧ x < y`. -/
TheoremDoc abs_lt as "abs_lt" in "|x|"

NewTheorem abs_lt


/-- Prove this
-/
Statement (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) :
  ∃ N, ∀ n ≥ N, a n ≥ L - 1 := by
specialize ha 1 (by bound)
choose N hN using ha
use N
intro n hn
specialize hN n hn
rewrite [abs_lt] at hN
have : -1 < a n - L := by apply hN.1
bound

Conclusion "
# 📐 Absolute Value Mastery Achieved! 📐

Outstanding! You've just completed a proof that demonstrates the power of combining logical reasoning with analytical techniques. This type of argument—extracting bounds from convergence conditions—is absolutely fundamental in real analysis.

**Why This Matters:**
What you just proved is that any convergent sequence is eventually bounded below (relative to its limit). This might seem like a small technical detail, but it's actually a building block for many major theorems. For instance, this type of reasoning is crucial in proving that convergent sequences are bounded, and that continuous functions on compact sets achieve their minima.

**The Strategic Breakdown:**
Notice the elegant flow of your proof: you started with the abstract convergence condition, chose a specific `ε` (namely `1`), extracted the absolute value condition, unpacked it using `abs_lt` to get both bounds, and then focused on just the bound you needed. This is mathematical reasoning at its finest—systematic, precise, and efficient.

**Technical Insight:**
The `abs_lt` theorem is your gateway between the world of absolute values (which are natural for expressing \"closeness\") and the world of ordinary inequalities (which are easier to manipulate algebraically). Learning to move fluently between these representations is a key skill in analysis.

**Looking Forward:**
As we progress to more advanced topics, you'll find yourself using this pattern repeatedly: taking convergence hypotheses, specializing them to specific epsilons, and then extracting the directional information you need. The techniques you've mastered here will be essential for proving results about monotonic sequences, bounded sequences, and much more.

You're not just learning tactics—you're developing the analytical intuition that separates novice proof-writers from experienced mathematicians. Keep building on these foundations!
"
