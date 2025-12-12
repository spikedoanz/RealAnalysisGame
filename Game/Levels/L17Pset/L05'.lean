import Game.Levels.L17Pset.L05
open Finset

World "L17Pset"
Level 2
Title "Monotone Limit Bound"
Introduction "
# Level 2: Monotone Limit Bound

Prove the theorem `MonotoneLimitBound`:
Suppose that a sequence `a : ℕ → ℝ` is `Monotone` and has limit `L`. Then
for every `n`, `a n ≤ L`.

"
/-- If `a : ℕ → ℝ` is `Monotone` and has limit `L`, then for all `n`, `a n ≤ L`.
-/
TheoremDoc MonotoneLimitBound as "MonotoneLimitBound" in "aₙ"

Statement MonotoneLimitBound {a : ℕ → ℝ} (amono : Monotone a) {L : ℝ} (ha : SeqLim a L) : ∀ n,
  a n ≤ L := by
intro n
by_contra h
push_neg at h
let ε := (a n - L)
have εis : ε = a n - L := by rfl
have εpos : 0 < ε := by bound
choose N hN using ha ε εpos
let m := N + n
have anm := amono (show n ≤ m by bound)
specialize hN m (by bound)
have hm : 0 ≤ a m - L := by bound
rewrite [show |a m - L| = a m - L by apply abs_of_nonneg hm] at hN
rewrite [εis] at hN
linarith [anm, hN]

Conclusion "
"
