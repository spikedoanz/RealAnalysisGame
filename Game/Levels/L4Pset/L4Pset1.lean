import Game.Levels.L4Lecture
import Game.Levels.L3PsetIntro

World "L4Pset"
Level 1
Title "Problem 1"

Introduction "# Problem 1

Let `a (n)` be a sequence that alternates between
`3 - 1 / n` and `1 + 1 / n`. Prove that this sequence diverges.

**Hint:** You may wish to argue using `N` that's slightly
larger than the smallest possible value.

**Hint 2:** If your desired `have` is a consequence of two facts put together,
*you can separate them by a semicolon. For example, if you know that `h : X = Y
*+ Z`,
and you want to add a hypothesis `h' : |X - Y| = |Z|`, which is a combination of
rewriting by `h` and a ring operation, then you can say:

`have h' : |X - Y| = |Z| := by rewrite [h]; ring_nf`.

This might come in handy!...
"

/-- Prove that this sequence diverges. -/
example
  (a : ℕ → ℝ)
  (ha2n   : ∀ n, a (2 * n)      = 3 - 1 / n)
  (ha2np1 : ∀ n, a (2 * n + 1)  = 1 + 1 / n)
  : ¬ SeqConv a := by
  intro h
  choose L hL using h
  change ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε at hL
  specialize hL (1/2)
  simp at hL
  choose N hN using hL

  -- Use M = N + 2 to ensure M ≥ 2
  let M := N + 2
  have hMN : N ≤ M := by simp [M]
  have hM2 : M ≥ 2 := by simp [M]

  have h2m    := ha2n   M
  have h2mp1  := ha2np1 M

  have := hN (2*M)
  have hleft_ineq : N <= 2*M := by simp[M] ; linarith
  apply this at hleft_ineq

  have := hN (2*M+1)
  have hright_ineq : N <= 2*M+1 := by simp[M] ; linarith
  apply this at hright_ineq

  have flipped : |a (2 * M + 1) - L| = |-a (2 * M + 1) + L| := by
    have h' : -a (2 * M + 1) + L = -(a (2 * M + 1) - L) := by ring
    rw [h', abs_neg]
  rw [flipped] at hright_ineq

  rw [h2m]    at hleft_ineq
  rw [h2mp1]  at hright_ineq

  have triangle : |(3 - 1 / ↑M - L) + (-(1 + 1 / ↑M) + L)|
    <= |(3 - 1 / ↑M - L)| + |(-(1 + 1 / ↑M) + L)| := abs_add _ _

  have upper_triangle : |(3 - 1 / ↑M - L)| + |(-(1 + 1 / ↑M) + L)| < 1 := by
    linarith [hleft_ineq, hright_ineq]
  have : M = N + 2 := by rfl
  have f0 : M >= 2 := by
    rw [this]
    linarith
  have f0' : ↑M >= (2:ℝ) := by exact_mod_cast f0

  have f1 : 1 <= 2 - (↑M:ℝ)⁻¹ * 2 := by
    field_simp
    linarith [f0']
  have f2 : (2 - (↑M:ℝ)⁻¹ * 2) <= |(2 - (↑M:ℝ)⁻¹ * 2)| := by
    apply le_abs_self

  have f3 : 1 <= |(2 - (↑M:ℝ)⁻¹ * 2)| := by
    linarith [f1, f2]

  have f4 : |(2 - (↑M:ℝ)⁻¹ * 2)| = |3 - 1 / ↑M - L + (-(1 + 1 / ↑M) + L)| := by
    ring_nf

  rw [←f4] at triangle

  have f5 : 1 <= |3 - 1 / ↑M - L| + |-(1 + 1 / ↑M) + L| := by
    linarith [f3, triangle]

  have f6 : 1 < 1 := by
    linarith [f5, upper_triangle]
  linarith [f6]


Conclusion "Done."
