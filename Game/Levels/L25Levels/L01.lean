import Game.Levels.L24Lecture
import Game.Levels.L24PsetIntro

open Set


World "Lecture25"
Level 1
Title "Uniform Convergence Implies Integrability"

Introduction "
# Level 1: Uniform Convergence Implies Integrability

We finally prove the fundamental theorem that justifies Newton's bold term-by-term integration of infinite series! If a sequence of integrable functions `fₙ` converges uniformly to `F`, then `F` is also integrable, and crucially:

$$\\int F = \\lim (\\int fₙ)$$

or equivalently: $$\\int(\\lim fₙ) = \\lim (\\int fₙ)$$

This theorem is the rigorous foundation behind Newton's calculation from Lecture 2, where he integrated the binomial series term-by-term to compute π.

**Why uniform convergence?** As Socrates showed with his examples, pointwise convergence alone fails spectacularly:
- Step functions shifting to infinity: `∫ fₙ = 1` but `∫(lim fₙ) = 0`
- Spike functions on `[0,1]`: `∫ fₙ = 1` but `∫(lim fₙ) = 0`
- Even continuous tent functions: `∫ fₙ = 1` but `∫(lim fₙ) = 0`

The key insight is that uniform convergence gives us simultaneous control over all function values. If `|fₙ(x) - F(x)| < ε/(b-a)` for all `x` and large `n`, then Riemann sum differences are bounded by `ε`, allowing us to interchange limits and integrals.

**Remarkable fact**: We assume *nothing* about continuity! Integrability is strictly weaker than continuity, yet suffices for this profound result.

This theorem bridges the gap between finite and infinite processes, making rigorous what Newton intuited centuries ago.
"

namespace RealAnalysisGame

/--
If `fₙ` converges uniformly to `F`, and each `fₙ` is integrable on `[a, b]`, then `F` is integrable on `[a, b]`, and the integral of `F` equals the limit of the integrals of `fₙ`.
-/
TheoremDoc RealAnalysisGame.Integrable_of_UnifConv as "Integrable_of_UnifConv" in "∫f"

Statement Integrable_of_UnifConv {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    {a b : ℝ} (hab : a < b)
    {ℓ : ℕ → ℝ}
    (hfint : ∀ n, HasIntegral (f n) a b (ℓ n))
    (hfF : UnifConv f F) :
    ∃ (L : ℝ), SeqLim ℓ L ∧ HasIntegral F a b L
 := by
have RSdiff : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ M, |RiemannSum (f n) a b M - RiemannSum F a b M| < ε := by
  intro ε hε
  choose N hN using hfF (ε / (b - a)) (by bound)
  use N
  intro n hn M
  specialize hN n hn
  sorry
have Lconv : SeqConv ℓ := by
  apply SeqConv_of_IsCauchy
  intro ε hε
  choose N hN using RSdiff (ε / 4) (by bound)
  use N
  intro n hn m hmn
  choose M1 hM1 using hfint n (ε / 4) (by bound)
  choose M2 hM2 using hfint m (ε / 4) (by bound)
  let M := M1 + M2
  specialize hM1 M (by bound)
  specialize hM2 M (by bound)
  have hNn := hN n hn M
  have hNm := hN m (by bound) M
  have b1 : |ℓ m - ℓ n| ≤ |RiemannSum (f n) a b M - ℓ n| + |RiemannSum (f n) a b M - RiemannSum F a b M| +
    |RiemannSum (f m) a b M - RiemannSum F a b M| + |RiemannSum (f m) a b M - ℓ m| := by
    sorry
  linarith [b1, hM1, hM2, hNn, hNm]
choose L hL using Lconv
use L, hL
intro ε hε
choose N1 hN1 using hL (ε / 3) (by bound)
choose N2 hN2 using RSdiff (ε / 3) (by bound)
let N := N1 + N2
have Nbnd1 : N1 ≤ N := by bound
have Nbnd2 : N2 ≤ N := by bound
specialize hN1 N (by bound)
specialize hN2 N (by bound)
choose Mmax hMmax using hfint N (ε / 3) (by bound)
use Mmax
intro M hM
specialize hMmax M hM
specialize hN2 M
have b2 : |RiemannSum F a b M - L| ≤ |RiemannSum (f N) a b M - RiemannSum F a b M| +
  |RiemannSum (f N) a b M - ℓ N| + |ℓ N - L| := by
  sorry
linarith [b2, hMmax, hN1, hN2, Nbnd1, Nbnd2]

end RealAnalysisGame

Conclusion "
**Victory!** You've just proven one of the most important theorems in real analysis. This result:

- **Validates Newton's genius**: His term-by-term integration of power series, done purely by intuition in the 1660s, now has rigorous justification
- **Bridges finite and infinite**: Extends the linearity of integrals from finite sums to infinite series (under uniform convergence)
- **Enables modern analysis**: Makes possible the rigorous treatment of Fourier series, differential equations with series solutions, and much of mathematical physics

The proof strategy you used—controlling Riemann sum differences via uniform convergence—is a masterclass in how sophisticated mathematical concepts work together. You leveraged:
- The completeness of ℝ (Cauchy sequences converge)
- The definition of integrability (Riemann sums)
- Uniform convergence (simultaneous control over all function values)

**Historical note**: This theorem wasn't rigorously proven until the late 1800s, over 200 years after Newton used it! Mathematicians like Weierstrass, Riemann, and others had to develop the very foundations of real analysis to make Newton's intuitive leaps rigorous.

You've now mastered the deep connection between limits and integrals. In Level 2, we'll use all the machinery we've built to prove the most 'obvious' theorem in mathematics—one so intuitive that it was assumed without proof for over 2000 years!
"
