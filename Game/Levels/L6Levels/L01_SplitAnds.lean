import Game.Levels.L6Levels.L00_SumOfSeqs

World "Lecture6"
Level 2
Title "Split Ands"

Introduction "
# Level 2: Split Ands - Breaking Down Complex Goals

Now that you've conquered the Big Boss and proven that sums of convergent sequences converge, you've experienced firsthand how mathematical proofs often require us to establish multiple related facts simultaneously. In our previous proof, we needed to show that both individual sequences satisfied their epsilon conditions, and then combine these results.

This pattern -- needing to prove several statements at once -- appears constantly in mathematics. Fortunately, Lean provides us with powerful tools to handle such situations elegantly. When your goal involves proving multiple statements connected by \"and\" (`∧`), the `split_ands` tactic becomes your best friend.

Think of `split_ands` as a way to break down a complex manufacturing specification into individual quality checks. Instead of trying to verify that a product meets three different standards all at once, we can tackle each standard separately and systematically.

## New Tools You'll Need

- `split_ands`

The `split_ands` tactic breaks apart \"and\" Goals into individual pieces. If your goal is `h₁ ∧ h₂ ∧ h₃`, then calling `split_ands` will break that into three separate goals, the first being
`h₁`, the second `h₂`, and of course `h₃`
"

/-- The `split_ands` tactic breaks apart \"and\" Goals into individual pieces. If your goal is `h₁ ∧ h₂ ∧ h₃`, then calling `split_ands` will break that into three separate goals, the first being
`h₁`, the second `h₂`, and of course `h₃`. -/
TacticDoc split_ands

NewTactic split_ands

/-- Prove this
-/
example (x y : ℝ) (hx : x = 2) (hy : y = 3) :
    x = 2 ∧ y = 3 := by
    split_ands
    exact hx
    exact hy

Conclusion "🎯 Tactical Mastery Achieved! 🎯

Perfect! You've just learned one of the most practical tactics in your Lean toolkit. The `split_ands` tactic might seem simple, but it's incredibly powerful for organizing complex proofs.

## Why This Matters:

Many important mathematical theorems have conclusions that are conjunctions—statements of the form \"A and B and C\". Being able to break these down systematically makes proofs much more manageable and readable.

## Looking Ahead:

As we continue building our arsenal of proof techniques, you'll find that `split_ands` combines beautifully with the convergence arguments we've been developing. Often in analysis, we need to prove that multiple sequences converge, or that a single sequence satisfies multiple properties simultaneously.
The beauty of mathematical proof lies not just in reaching the destination, but in breaking the journey into clear, logical steps. `split_ands` is your tool for taking that first crucial step: turning one complex goal into several simpler ones.
"
