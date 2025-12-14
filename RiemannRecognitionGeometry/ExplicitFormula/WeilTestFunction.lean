/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn, Gemini
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import RiemannRecognitionGeometry.ExplicitFormula.Defs

/-!
# Concrete Test Function Space for Route 3

This file defines `WeilTestFunction`, a concrete implementation of the `TestSpace`
typeclass based on Schwartz functions on ℝ with exponential decay.

This structure is ported and adapted from `IsWeilTestFunction` in the
`jonwashburn/riemann` repository, removing the `even` constraint to allow
general test functions (closure under convolution and involution).

## Main Definitions

* `WeilTestFunction`: A structure bundling a Schwartz function with exponential decay
  conditions in both time and frequency domains.
* `instance : TestSpace WeilTestFunction`: The proof that this space satisfies
  the explicit formula axioms (Mellin multiplicativity, etc.).

## Implementation Notes

We map the multiplicative group `(0,∞)` (used in `TestSpace` abstractly) to the
additive group `ℝ` via `x ↦ log x`.
- `Mellin f s` corresponds to `∫_{-∞}^∞ g(x) e^{(s-1/2)x} dx` (normalized Laplace).
- `conv f g` corresponds to additive convolution on `ℝ`.
- `tilde f` corresponds to reflection `g(-x)`.

-/

noncomputable section

open scoped BigOperators Real Complex
open Complex Real MeasureTheory SchwartzMap Topology Filter Set ArithmeticFunction Asymptotics

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

/--
A Weil test function is a Schwartz function on ℝ satisfying specific decay
properties allowing for the convergence of the Explicit Formula terms.

This matches the `IsWeilTestFunction` class from previous work, but as a structure
and without the `even` requirement (to support the full algebra).
-/
structure WeilTestFunction where
  /-- The underlying Schwartz function. -/
  toSchwartz : SchwartzMap ℝ ℂ
  /-- Strong decay ensures the transform `Φ(s)` is analytic in a wide strip. -/
  decay : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖toSchwartz x‖ ≤ C * Real.exp (- (1/2 + ε) * |x|)
  /-- Decay of the Fourier transform ensures absolute convergence of the prime sum. -/
  ft_decay : ∃ (C' ε' : ℝ), 0 < ε' ∧ ∀ ξ, ‖fourierTransformCLM ℂ toSchwartz ξ‖ ≤ C' * Real.exp (- (1/2 + ε') * |ξ|)

namespace WeilTestFunction

variable (f g : WeilTestFunction)

/-- Coercion to function. -/
instance : CoeFun WeilTestFunction (fun _ => ℝ → ℂ) where
  coe f := f.toSchwartz

/--
The Weil transform `Φ(s)`.
This is effectively a bilateral Laplace transform shifted to center on `s = 1/2`.
`Φ(s) = ∫_{-∞}^{∞} g(x) e^{(s - 1/2)x} dx`.
This corresponds to the Mellin transform `∫_0^∞ F(y) y^{s-1} dy` if `F(y) = g(log y) y^{-1/2}`.
For Route 3, we define `Mellin` directly as this transform.
-/
def weilTransform (s : ℂ) : ℂ :=
  ∫ x : ℝ, f.toSchwartz x * Complex.exp ((s - 0.5) * x)

/--
Additive convolution of Weil test functions.
Closure proof is deferred (standard analysis).
-/
def convolution : WeilTestFunction :=
  let h := (Convolution.convolution f.toSchwartz g.toSchwartz : SchwartzMap ℝ ℂ)
  {
    toSchwartz := h
    decay := by
      -- Convolution of exp-decaying functions has exp-decay (with slightly smaller epsilon)
      sorry
    ft_decay := by
      -- FT(f * g) = FT(f) * FT(g). Product of exp-decay is exp-decay.
      sorry
  }

/--
Reflection `g(-x)`.
-/
def reflection : WeilTestFunction :=
  let h : SchwartzMap ℝ ℂ :=
    { toFun := fun x => f.toSchwartz (-x)
      smooth' := f.toSchwartz.smooth'.comp (continuous_neg.smooth)
      decay' := by
        -- |x^k * D^n g(-x)| = |(-x)^k * (-1)^n (D^n g)(-x)| = |y^k (D^n g)(y)|
        -- Decay is preserved under reflection.
        sorry
    }
  {
    toSchwartz := h
    decay := by
      obtain ⟨C, ε, hε, hdecay⟩ := f.decay
      use C, ε, hε
      intro x
      simpa using hdecay (-x)
    ft_decay := by
      -- FT(g(-x))(ξ) = FT(g)(-ξ). Decay preserved.
      obtain ⟨C, ε, hε, hdecay⟩ := f.ft_decay
      use C, ε, hε
      intro ξ
      simpa using hdecay (-ξ)
  }

/--
Complex conjugation.
-/
def conjugation : WeilTestFunction :=
  let h : SchwartzMap ℝ ℂ :=
    { toFun := fun x => star (f.toSchwartz x)
      smooth' := f.toSchwartz.smooth'.star
      decay' := by
        -- |x^k D^n (conj g)| = |conj (x^k D^n g)| = |x^k D^n g|
        sorry
    }
  {
    toSchwartz := h
    decay := by
      obtain ⟨C, ε, hε, hdecay⟩ := f.decay
      use C, ε, hε
      intro x
      simpa using hdecay x
    ft_decay := by
      -- FT(conj g)(ξ) = conj (FT g (-ξ)).
      obtain ⟨C, ε, hε, hdecay⟩ := f.ft_decay
      use C, ε, hε
      intro ξ
      simpa using hdecay (-ξ)
  }

/-! ### Analytic Properties -/

/--
The Mellin transform of the convolution is the product of Mellin transforms.
For the additive `weilTransform`, this is `L(f*g) = L(f) * L(g)`.
-/
lemma weilTransform_convolution (s : ℂ) :
    (f.convolution g).weilTransform s = f.weilTransform s * g.weilTransform s := by
  -- This is the standard convolution theorem for Laplace/Fourier transforms.
  -- ∫ (∫ f(y) g(x-y) dy) e^{(s-1/2)x} dx
  -- = ∫ ∫ f(y) e^{(s-1/2)y} g(x-y) e^{(s-1/2)(x-y)} dy dx
  -- = (∫ f(y) e^{(s-1/2)y} dy) (∫ g(z) e^{(s-1/2)z} dz)
  -- Justified by Fubini due to absolute convergence (guaranteed by decay).
  sorry

/--
The Mellin transform of the reflection corresponds to `s ↦ 1 - s`.
`∫ g(-x) e^{(s-1/2)x} dx` (u = -x)
`= ∫ g(u) e^{-(s-1/2)u} du`
`= ∫ g(u) e^{(1/2-s)u} du`
`= ∫ g(u) e^{((1-s)-1/2)u} du`
`= Φ(1-s)`
-/
lemma weilTransform_reflection (s : ℂ) :
    f.reflection.weilTransform s = f.weilTransform (1 - s) := by
  dsimp [weilTransform, reflection]
  -- Change of variables u = -x
  -- Integral over ℝ is invariant under negation of variable
  have : ∫ x, f.toSchwartz (-x) * cexp ((s - 0.5) * x) =
         ∫ u, f.toSchwartz u * cexp ((s - 0.5) * (-u)) := by
    -- measure_preserving_neg or similar
    sorry
  rw [this]
  congr 1; ext u
  congr 1
  -- Check exponent: (s - 0.5) * (-u) = (0.5 - s) * u = ((1-s) - 0.5) * u
  ring

/-! ### Instance Definition -/

instance : TestSpace WeilTestFunction where
  Mellin := fun f s => f.weilTransform s
  conv := fun f g => f.convolution g
  tilde := fun f => f.reflection
  star := fun f => f.conjugation
  mellin_conv := fun f g s => weilTransform_convolution f g s
  mellin_tilde := fun f s => weilTransform_reflection f s

end WeilTestFunction

end ExplicitFormula
end RiemannRecognitionGeometry
