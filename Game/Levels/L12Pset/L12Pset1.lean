import Game.Levels.L12Lecture
import Game.Levels.L11PsetIntro

World "L12Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

In lecture, we proved `IsCauchy_of_MonotoneBdd`: if a sequence is `Monotone` and bounded (from above),
then it `IsCauchy`. Here you'll prove the same thing but going down: if a sequence is `Antitone` (that
is, non-increasing -- so decreasing but not necessarily strictly so; `i ≤ j → a j ≤ a i) and bounded
from *below*, then it's Cauchy.

Theorem: `IsCauchy_of_AntitoneBdd`.

## New definition: `Antitone`

Hint: You don't need to reprove everything from scratch! I'll give you two tools:

## New theorems:

- `MonotoneNeg_of_Antitone`: if `a` is `Antitone`, then `-a` is `Monotone`.

- `IsCauchyNeg`: if `IsCauchy a`, then so is `IsCauchy (-a)`.

"

/-- `(a : X → Y) {i j} (hij : i ≤ j) : a j ≤ a i`

A sequence `a : X → Y` is said to be `Antitone` if `a m ≤ a n` whenever `n ≤ m` (note that `n` and `m` were reversed).
 -/
DefinitionDoc Antitone as "Antitone"

NewDefinition Antitone

theorem MonotoneNeg_of_Antitone {X : Type*} [LinearOrder X] [AddCommGroup X] [IsOrderedAddMonoid X]
(a : ℕ → X) (ha : Antitone a) : Monotone (-a) :=
fun i j hij ↦ neg_le_neg (ha hij)

/-- If `a` is `Antitone`, then `-a` is `Monotone`. -/
TheoremDoc MonotoneNeg_of_Antitone as "MonotoneNeg_of_Antitone" in "aₙ"

theorem IsCauchyNeg {X : Type*} [NormedField X] [Lattice X]
(a : ℕ → X) (ha : IsCauchy a) : IsCauchy (-a) := by
intro ε hε
choose N hN using ha ε hε
use N
intro n hn m hm
change |(- a m) - (- a n)| < ε
rewrite [show (- a m) - (- a n) = -(a m - a n) by ring_nf]
rewrite [show |-(a m - a n)| = |(a m - a n)| by apply abs_neg]
apply hN n hn m hm

/-- If `a` satisfies `IsCauchy`, then `-a` does too. -/
TheoremDoc IsCauchyNeg as "IsCauchyNeg" in "aₙ"


NewTheorem MonotoneNeg_of_Antitone IsCauchyNeg


/-- Prove `IsCauchy_of_AntitoneBdd`
-/
Statement  {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X]
    {a : ℕ → X} {M : X} (ha : Antitone a) (hM : ∀ n, M ≤ a n)
    : IsCauchy a := by
let b := -a
have hb : Monotone b := by apply MonotoneNeg_of_Antitone a ha
have b_bdd : ∀ n, b n ≤ -M := by intro n; change -a n ≤ - M; linarith [hM n]
have bCauchy : IsCauchy b := IsCauchy_of_MonotoneBdd hb b_bdd
have negbCauchy : IsCauchy (-b) := IsCauchyNeg b bCauchy
change IsCauchy (- -a) at negbCauchy
rewrite [show - - a = a by ring_nf] at negbCauchy
apply negbCauchy

Conclusion ""
