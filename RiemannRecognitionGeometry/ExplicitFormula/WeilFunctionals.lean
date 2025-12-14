/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn, Gemini
-/
import RiemannRecognitionGeometry.ExplicitFormula.WeilTestFunction
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.VonMangoldt

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace WeilFunctionals

open Complex Real MeasureTheory SchwartzMap Topology Filter Set ArithmeticFunction WeilTestFunction

variable (f : WeilTestFunction)

/--
Logarithmic derivative of the Gamma factor for Zeta, `Γℝ(s) = π^{-s/2} Γ(s/2)`.
Note: The factor π^{-s/2} adds a -1/2 log π term to the derivative.
-/
def GammaLogDeriv (s : ℂ) : ℂ :=
  (logDeriv Complex.Gamma) s

/--
Archimedean term for Zeta.
`𝒜(g) = \frac{1}{4\pi} \int_{-\infty}^\infty g(x) \Psi_{arch}(x) dx`
Derived from the Gamma factor in the functional equation.
-/
def archimedeanTerm : ℂ :=
  let h := fourierTransformCLM ℂ f.toSchwartz
  let term1 := (1 / (2 * π)) * ∫ x : ℝ, f.toSchwartz x *
    (GammaLogDeriv (1/4 + Complex.I * (x/2)) + GammaLogDeriv (1/4 - Complex.I * (x/2)))
  let term2 := - h 0 * Real.log π
  term1 + term2

/--
Prime power contribution:
`∑_{n} \frac{\Lambda(n)}{\sqrt{n}} (g(\log n) + g(-\log n))`
-/
def primeTerm : ℂ :=
  - ∑' n : ℕ, if n = 0 then 0 else
    ((vonMangoldt n : ℂ) / Real.sqrt n) *
      (f.toSchwartz (Real.log n) + f.toSchwartz (-Real.log n))

/--
Geometric side: Sum of prime term, archimedean term, and boundary terms (poles).
This corresponds to the "Arithmetic Side" in the Lagarias formulation (explicit formula).
`Warith(f) = W_primes + W_arch + W_poles`.
-/
def Warith : ℂ :=
  f.weilTransform 1 +
  f.weilTransform 0 +
  primeTerm f +
  archimedeanTerm f

/--
The Weil Positivity Gate (Concrete).
The Riemann Hypothesis is equivalent to `Warith (f.convolution f.conjugation.reflection) ≥ 0`
for all Weil test functions `f`.
-/
def WeilGate : Prop :=
  ∀ f : WeilTestFunction, 0 ≤ (Warith (f.convolution f.conjugation.reflection)).re

end WeilFunctionals
end ExplicitFormula
end RiemannRecognitionGeometry
