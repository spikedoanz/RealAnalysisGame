import Game.Levels.L18Pset.L07
open Finset

World "L18Pset"
Level 8
Title "BddSeriesEven"
Introduction "
# Level 8: `BddSeriesEven`

Prove `BddSeriesEven`:

You might find the theorem `sum_range_succ'` useful. It is like `sum_range_succ`, but
pulls out the first term instead of the last.

"

/--
`∑ k ∈ range (m + 1), f k = f 0 + ∑ k ∈ range m, f (k+1)`. This pulls out the first
term in the sum instead of `sum_range_succ`, which pulls out the last term.
-/
TheoremDoc Finset.sum_range_succ' as "sum_range_succ'" in "∑aₙ"

NewTheorem Finset.sum_range_succ'

DisabledTheorem BddSeriesEven

/-- Prove `BddSeriesEven`
-/
Statement {a : ℕ → ℝ} (ha : Antitone a) (apos : ∀ n, 0 ≤ a n) (n : ℕ) : ∑ k ∈ range (2 * n), (-1)^k * a k ≤ a 0 := by
have shift : ∀ m, ∑ x ∈ range (2 * (m + 1)), (-1) ^ x * a x =
             a 0 + ∑ k ∈ range (2 * m + 1), (-1) ^ (k + 1) * a (k + 1) := by
  intro m
  rewrite [show 2 * (m + 1) = 2 * m + 2 by ring_nf]
  rewrite [sum_range_succ']
  ring_nf
have f1 : ∀ m, ∑ k ∈ range (2 * (m + 1)), (-1) ^ k * a k =
        (∑ k ∈ range (2 * m), (-1) ^ (k + 1) * a (k + 1)) + a 0 - a (2 * m + 1) := by
  intro m
  rewrite [shift, sum_range_succ]
  ring_nf
  bound
have f2 : ∀ m, ∑ k ∈ range (2 * m), (-1) ^ (k + 1) * a (k + 1) ≤ 0 := by
  intro m
  induction' m with m hm
  bound
  rewrite [show 2 * (m + 1) = 2 * m + 2 by ring_nf]
  rewrite [sum_range_succ, sum_range_succ]
  rewrite [show  ∑ x ∈ range (2 * m), (-1) ^ (x + 1) * a (x + 1) + (-1) ^ (2 * m + 1) * a (2 * m + 1) +
    (-1) ^ (2 * m + 1 + 1) * a (2 * m + 1 + 1) =  ∑ x ∈ range (2 * m), (-1) ^ (x + 1) * a (x + 1) + ((-1) ^ (2 * m + 1) * a (2 * m + 1) +
    (-1) ^ (2 * m + 1 + 1) * a (2 * m + 1 + 1)) by ring_nf]
  rewrite [show ((-1) ^ (2 * m + 1) * a (2 * m + 1) + (-1) ^ (2 * m + 1 + 1) * a (2 * m + 1 + 1))
    = (-a (2 * m + 1) + a (2 * m + 1 + 1)) by ring_nf; bound]
  have ham : a (2 * m + 1 + 1) ≤ a (2 * m + 1) := by apply ha (by bound)
  linarith [ham, hm]
induction' n with n hn
rewrite [show ∑ k ∈ range (2 * 0), (-1) ^ k * a k = 0 by bound]
apply apos 0
rewrite [f1]
have f3 : 0 ≤ a (2 * n + 1) := by apply apos
linarith [f2 n, f3]

Conclusion "
"
