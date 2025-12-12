import Game.Levels.L23Lecture

open Set

World "Lecture24"
Level 1
Title "Heine-Borel Theorem: Part 1a"
Introduction "
# Level 1: Heine-Borel Theorem: Part 1a

**The Goal**: We're starting our formal proof of the famous Heine-Borel theorem. First up: every compact set is bounded.

**The Strategy**: Remember that compactness means \"every open cover has a finite subcover.\" To show a set is bounded, we need to trap it inside some big ball. Here's the clever idea:

1. **Create an infinite cover**: Cover the entire real line with balls `Ball(0, 1)`, `Ball(0, 2)`, `Ball(0, 3)`, etc. These definitely cover any set `S`.

2. **Extract a finite subcover**: Since `S` is compact, only finitely many of these balls are needed to cover `S`.

3. **Take the maximum**: The largest radius among these finitely many balls gives us our bound!

**Why This Works**: If `S` can be covered by balls of radii `1, 3, 7, 12` (for example), then every point in `S` has absolute value less than `max(1, 3, 7, 12) = 12`.

**Key Tool**: The `FinMax` lemma guarantees that any finite collection of real numbers has a maximum:

`lemma FinMax (ι : Type) (V : Finset ι) (δs : ι → ℝ) :
    ∃ δ, ∀ i ∈ V, δs i ≤ δ`

**Your Mission**: Formalize this intuitive argument. Use the balls `Ball(0, n+1)` for `n : ℕ`, apply compactness to get a finite subcover, then use `FinMax` to extract the bound!
"

namespace RealAnalysisGame

lemma FinMax (ι : Type) (V : Finset ι) (δs : ι → ℝ) :
    ∃ δ, ∀ i ∈ V, δs i ≤ δ := by
  by_cases h_nonempty : V.Nonempty
  let δ := Finset.sup' V h_nonempty δs
  use δ
  intro i hi
  exact Finset.le_sup' δs hi
  use 1
  intro i hi
  exfalso
  simp only [Finset.not_nonempty_iff_eq_empty] at h_nonempty
  rewrite [h_nonempty] at hi
  contradiction

/--
A finite list has a maximum element.
-/
TheoremDoc RealAnalysisGame.FinMax as "FinMax" in "Theorems"

NewTheorem RealAnalysisGame.FinMax

/--
A compact set is bounded.
-/
TheoremDoc RealAnalysisGame.Bdd_of_Compact as "Bdd_of_Compact" in "x∈U"

Statement Bdd_of_Compact (S : Set ℝ) (hcomp : IsCompact S) : ∃ M, ∀ s ∈ S, |s| < M := by
let ι := ℕ
let xs : ι → ℝ := fun n ↦ 0
let δs : ι → ℝ := fun n ↦ n + 1
have δspos : ∀ n, 0 < δs n := by
  intro n
  change 0 < (n : ℝ) + 1
  linarith
have hcover : S ⊆ ⋃ i, Ball (xs i) (δs i) := by
  intro s hs
  rewrite [mem_Union]
  use ⌈|s|⌉₊
  change s ∈ Ioo ((0 : ℝ) - ((⌈|s|⌉₊ + 1))) (0 + ((⌈|s|⌉₊ + 1)))
  rewrite [mem_Ioo]
  rewrite [show (0 : ℝ) - (⌈|s|⌉₊ + 1) = - (⌈|s|⌉₊ + 1) by ring_nf]
  rewrite [show (0 : ℝ) + (⌈|s|⌉₊ + 1) = (⌈|s|⌉₊ + 1) by ring_nf]
  rewrite [← abs_lt]
  have f : ∀ x ≥ (0 : ℝ), x ≤ ⌈x⌉₊ := by
    intro x hx
    bound
  specialize f (|s|) (by bound)
  linarith [f]
choose V hV using hcomp ι xs δs δspos hcover
choose M hM using FinMax ι V δs
use M
intro s hs
specialize hV hs
rewrite [mem_Union] at hV
choose i ball_i i_in_V s_in_Ball using hV
rewrite [mem_range] at i_in_V
choose hi hi' using i_in_V
specialize hM i hi
rewrite [← hi'] at s_in_Ball
change s ∈ Ioo ((0 : ℝ) - (i + 1)) (0 + (i + 1)) at s_in_Ball
rewrite [show (0 : ℝ) - (i + 1) = - (i + 1) by ring_nf] at s_in_Ball
rewrite [show (0 : ℝ) + (i + 1) = (i + 1) by ring_nf] at s_in_Ball
rewrite [mem_Ioo] at s_in_Ball
rewrite [← abs_lt] at s_in_Ball
change i + 1 ≤ M at hM
linarith [s_in_Ball, hM]

end RealAnalysisGame

Conclusion "
# First Half Complete!

You've just proved that **compact ⟹ bounded**! This is the first half of one direction of the Heine-Borel theorem.

**What Made This Proof Beautiful**:
- **Infinite to Finite Magic**: You started with infinitely many balls covering all of ℝ, but compactness let you reduce to just finitely many balls covering your set `S`.
- **Constructive Bound**: Your proof doesn't just say \"a bound exists\" - it gives you an explicit bound as the maximum radius of the finite subcover.
- **Archimedean Foundation**: The proof relies on the fact that balls `Ball(0, n+1)` eventually cover any point, which is essentially the Archimedean property of ℝ.

**The Bigger Picture**: You've shown that compactness prevents sets from \"escaping to infinity.\" No matter how a compact set tries to spread out, it must stay within some finite ball.

**What's Next**: In Level 2, you'll prove that compact sets are also **closed**. This is trickier - you'll need to show that if a point is outside your compact set, then there's a whole ball around that point that stays outside. The key insight will be using compactness to create \"uniform separation\" between the outside point and your set.

**Historical Note**: This direction (compact ⟹ closed and bounded) is actually the easier direction of Heine-Borel. The hard work comes later when we prove the converse: closed and bounded ⟹ compact. That's where we'll need the deep structure of ℝ!

You're building the foundation for understanding why [a,b] intervals are so special in calculus!
"
