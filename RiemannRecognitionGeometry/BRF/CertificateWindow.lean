/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BRF Route: Concrete Certificate Windows

Ported from: reality/IndisputableMonolith/NumberTheory/RiemannHypothesis/CertificateWindow.lean

This file defines the actual **window functions** used in the certificate layer:

- a **flat-top window** built from a profile `ψ` with a unit plateau on `[-1,1]`,
  scaled to mass `1` by `1/L`;
- a **Poisson-plateau window** (abstractly) as a Poisson-kernel convolution of the profile,
  also scaled by `1/L`.

We then instantiate the B1 bridge from `WindowBridge`:

`(∫ φ_{L,t0} d(-w') ≤ D) + (φ_{L,t0} ≥ c on Ioo(t0-L,t0+L))  ⇒  oscOn w (Icc(t0-L,t0+L)) ≤ D / c`.
-/

import RiemannRecognitionGeometry.BRF.WindowBridge

namespace RiemannRecognitionGeometry
namespace BRF

open scoped Real Topology ENNReal MeasureTheory
open MeasureTheory Filter Set

/-!
## Flat-top window
-/

/-- The (nonnegative) flat-top window associated to a profile `ψ : ℝ → ℝ` at scale `L>0`
and center `t0`:
\[
  \varphi_{L,t0}(t) := \mathrm{ofReal}\Big(\frac{\psi((t-t0)/L)}{L}\Big).
\]

This matches the manuscript's `L^{-1} ψ((t-t0)/L)` when `ψ ≥ 0`.
-/
noncomputable def certificateWindowFlat (ψ : ℝ → ℝ) (L t0 : ℝ) : ℝ → ℝ≥0∞ :=
  fun t => ENNReal.ofReal (ψ ((t - t0) / L) / L)

namespace certificateWindowFlat

variable {ψ : ℝ → ℝ} {L t0 : ℝ}

lemma lower_of_plateau_one (hL : 0 < L)
    (hψ : ∀ x : ℝ, |x| ≤ 1 → ψ x = 1) :
    ∀ t, t ∈ Set.Ioo (t0 - L) (t0 + L) →
      ENNReal.ofReal (1 / L) ≤ certificateWindowFlat ψ L t0 t := by
  intro t ht
  have hlt : |t - t0| < L := by
    have h1 : t - t0 < L := by linarith [ht.2]
    have h2 : -L < t - t0 := by linarith [ht.1]
    exact abs_lt.2 ⟨h2, h1⟩
  have habs : |(t - t0) / L| ≤ 1 := by
    have habs' : |(t - t0) / L| < 1 := by
      -- `|(t-t0)/L| = |t-t0|/L < 1` since `|t-t0| < L` and `L>0`.
      have : |t - t0| / L < 1 := by
        -- rewrite as `|t-t0| < 1*L`.
        have : |t - t0| < 1 * L := by simpa using hlt
        -- `b / c < a ↔ b < a*c`
        exact (div_lt_iff₀ hL).2 (by simpa [one_mul] using this)
      simpa [abs_div, abs_of_pos hL] using this
    exact le_of_lt habs'
  have hψ1 : ψ ((t - t0) / L) = 1 := hψ _ habs
  -- On the plateau, the window equals `ofReal (1/L)`.
  simp [certificateWindowFlat, hψ1, one_div]

end certificateWindowFlat

/-!
## Poisson kernel and Poisson-plateau window (scaled)

We define the normalized Poisson kernel on `ℝ` (as an `ℝ≥0∞`-valued function).

The Poisson convolution `(P_b * ψ)(x) = ∫ P_b(x-y) ψ(y) dy` is defined abstractly
via an `ℝ≥0∞`-valued Lebesgue integral.

This is set up so the manuscript constant
`c0(ψ) := inf_{0<b≤1, |x|≤1} (P_b * ψ)(x)` can be plugged in later.
-/

/-- Normalized Poisson kernel on `ℝ` (as a nonnegative `ℝ≥0∞` function). -/
noncomputable def poissonKernel (b : ℝ) : ℝ → ℝ≥0∞ :=
  fun x => ENNReal.ofReal ((1 / Real.pi) * (b / (b ^ 2 + x ^ 2)))

/-- Poisson convolution of a profile `ψ : ℝ → ℝ≥0∞` at height `b`.

This is defined as the Lebesgue integral:
`(P_b * ψ)(x) = ∫ P_b(x-y) ψ(y) dy`
-/
noncomputable def poissonConv (b : ℝ) (ψ : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun x => ∫⁻ y, poissonKernel b (x - y) * ψ y

/-- The value-set used to define the manuscript constant
\[
  c_0(ψ) := \inf_{0<b\le 1,\ |x|\le 1} (P_b * ψ)(x).
\]

We store the infimum in `ℝ≥0∞` since `poissonConv` is `ℝ≥0∞`-valued. -/
def poissonPlateauValSet (ψ : ℝ → ℝ≥0∞) : Set ℝ≥0∞ :=
  { y | ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∃ x : ℝ, |x| ≤ 1 ∧ y = poissonConv b ψ x }

/-- The Poisson plateau constant `c0(ψ)` as an `ℝ≥0∞` infimum. -/
noncomputable def c0PoissonENN (ψ : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  sInf (poissonPlateauValSet ψ)

/-- Convenience real-valued version `c0(ψ)` defined as `toReal` of the `ℝ≥0∞` infimum.

To use it as a genuine plateau constant (rather than defaulting to `0` when `= ⊤`),
you will typically assume `c0PoissonENN ψ ≠ ⊤` and `0 < c0Poisson ψ`. -/
noncomputable def c0Poisson (ψ : ℝ → ℝ≥0∞) : ℝ :=
  (c0PoissonENN ψ).toReal

lemma c0PoissonENN_le_poissonConv {ψ : ℝ → ℝ≥0∞} {b x : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hx : |x| ≤ 1) :
    c0PoissonENN ψ ≤ poissonConv b ψ x := by
  -- `Inf S ≤ a` for any `a ∈ S`.
  unfold c0PoissonENN
  refine sInf_le ?_
  exact ⟨b, hb0, hb1, x, hx, rfl⟩

lemma ofReal_c0Poisson_le_poissonConv {ψ : ℝ → ℝ≥0∞} {b x : ℝ}
    (hc0_top : c0PoissonENN ψ ≠ ⊤) (hb0 : 0 < b) (hb1 : b ≤ 1) (hx : |x| ≤ 1) :
    ENNReal.ofReal (c0Poisson ψ) ≤ poissonConv b ψ x := by
  have h0 : c0PoissonENN ψ ≤ poissonConv b ψ x :=
    c0PoissonENN_le_poissonConv (ψ := ψ) (b := b) (x := x) hb0 hb1 hx
  -- Rewrite `ofReal (toReal (c0PoissonENN ψ))` back to `c0PoissonENN ψ`.
  have hrew : ENNReal.ofReal (c0Poisson ψ) = c0PoissonENN ψ := by
    simpa [c0Poisson] using (ENNReal.ofReal_toReal (a := c0PoissonENN ψ) hc0_top)
  simpa [hrew] using h0

lemma hpoisson_plateau_of_c0Poisson {ψ : ℝ → ℝ≥0∞} {b : ℝ}
    (hc0_top : c0PoissonENN ψ ≠ ⊤) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∀ x : ℝ, |x| ≤ 1 → ENNReal.ofReal (c0Poisson ψ) ≤ poissonConv b ψ x := by
  intro x hx
  exact ofReal_c0Poisson_le_poissonConv (ψ := ψ) (b := b) (x := x) hc0_top hb0 hb1 hx

/-- The scaled Poisson-plateau window at scale `L` and center `t0`:
\[
  \varphi^{P}_{L,t0}(t) := \frac{1}{L}\,(P_b * ψ)\big((t-t0)/L\big),
\]
encoded in `ℝ≥0∞` using `ENNReal.ofReal`.

This matches the user-facing "`c0(ψ)/L` plateau" behavior on `t ∈ (t0-L,t0+L)` when
`(P_b*ψ)(x) ≥ c0(ψ)` for `|x|≤1`.
-/
noncomputable def certificateWindowPoisson (b : ℝ) (ψ : ℝ → ℝ≥0∞) (L t0 : ℝ) : ℝ → ℝ≥0∞ :=
  fun t => (ENNReal.ofReal (1 / L)) * (poissonConv b ψ ((t - t0) / L))

/-!
## Instantiations of the B1 bridge (`window` ⇒ `oscOn`) on a Whitney interval
-/

theorem oscOn_Icc_whitney_le_mul_L_of_flatTop
    {w : ℝ → ℝ} (hw : Antitone w) (hw_rc : ∀ x, ContinuousWithinAt w (Ici x) x)
    {ψ : ℝ → ℝ} {L t0 D : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (hψ : ∀ x : ℝ, |x| ≤ 1 → ψ x = 1)
    (hlin :
      ∫⁻ t, certificateWindowFlat ψ L t0 t ∂(stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc))
        ≤ ENNReal.ofReal D) :
    oscOn w (Set.Icc (t0 - L) (t0 + L)) ≤ D * L := by
  have hab : (t0 - L) < (t0 + L) := by linarith
  have hc : 0 < (1 / L) := one_div_pos.2 hL
  have hφ_lower :
      ∀ t, t ∈ Set.Ioo (t0 - L) (t0 + L) → ENNReal.ofReal (1 / L) ≤ certificateWindowFlat ψ L t0 t :=
    certificateWindowFlat.lower_of_plateau_one (ψ := ψ) (L := L) (t0 := t0) hL hψ
  have hosC :
      oscOn w (Set.Icc (t0 - L) (t0 + L)) ≤ D / (1 / L) := by
    simpa [Set.Ioo] using
      oscOn_Icc_le_div_of_window_lintegral_bound (w := w) hw hw_rc (a := t0 - L) (b := t0 + L)
        (D := D) (c := (1 / L)) hab hD hc hφ_lower hlin
  -- simplify `D / (1/L)` to `D*L`
  simpa [div_div, one_div] using (le_trans hosC (le_of_eq (by field_simp [hL.ne'])))

theorem oscOn_Icc_whitney_le_div_c0_mul_L_of_poissonPlateau
    {w : ℝ → ℝ} (hw : Antitone w) (hw_rc : ∀ x, ContinuousWithinAt w (Ici x) x)
    {ψ : ℝ → ℝ≥0∞} {b L t0 D c0 : ℝ} (hL : 0 < L) (hD : 0 ≤ D) (hc0 : 0 < c0)
    (hpoisson_plateau :
      ∀ x : ℝ, |x| ≤ 1 → ENNReal.ofReal c0 ≤ poissonConv b ψ x)
    (hlin :
      ∫⁻ t, certificateWindowPoisson b ψ L t0 t
          ∂(stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc))
        ≤ ENNReal.ofReal D) :
    oscOn w (Set.Icc (t0 - L) (t0 + L)) ≤ (D / c0) * L := by
  have hab : (t0 - L) < (t0 + L) := by linarith
  -- lower bound `c0/L` on `Ioo`.
  have hφ_lower :
      ∀ t, t ∈ Set.Ioo (t0 - L) (t0 + L) →
        ENNReal.ofReal (c0 / L) ≤ certificateWindowPoisson b ψ L t0 t := by
    intro t ht
    have hlt : |t - t0| < L := by
      have h1 : t - t0 < L := by linarith [ht.2]
      have h2 : -L < t - t0 := by linarith [ht.1]
      exact abs_lt.2 ⟨h2, h1⟩
    have habs : |(t - t0) / L| ≤ 1 := by
      have habs' : |(t - t0) / L| < 1 := by
        have : |t - t0| / L < 1 := by
          have : |t - t0| < 1 * L := by simpa using hlt
          exact (div_lt_iff₀ hL).2 (by simpa [one_mul] using this)
        simpa [abs_div, abs_of_pos hL] using this
      exact le_of_lt habs'
    have hconv : ENNReal.ofReal c0 ≤ poissonConv b ψ ((t - t0) / L) := hpoisson_plateau _ habs
    -- multiply by `1/L` to get `c0/L`.
    -- `ofReal (c0/L) = ofReal c0 * ofReal (1/L)` (since both nonnegative).
    have hrew : ENNReal.ofReal (c0 / L) = ENNReal.ofReal c0 * ENNReal.ofReal (1 / L) := by
      -- `c0 / L = c0 * (1/L)`
      simpa [div_eq_mul_inv] using (ENNReal.ofReal_mul (p := c0) (q := (1 / L)) (le_of_lt hc0))
    have hrew' : ENNReal.ofReal (c0 / L) = ENNReal.ofReal (1 / L) * ENNReal.ofReal c0 := by
      simpa [mul_comm] using hrew
    -- Now: multiply the plateau inequality by `ofReal (1/L)`.
    have hmul :
        ENNReal.ofReal (1 / L) * ENNReal.ofReal c0
          ≤ ENNReal.ofReal (1 / L) * poissonConv b ψ ((t - t0) / L) :=
      mul_le_mul' le_rfl hconv
    -- Repackage as the window lower bound.
    simpa [certificateWindowPoisson, hrew', mul_assoc] using hmul
  -- Apply the generic B1 bridge with `c = c0/L`.
  have hc : 0 < (c0 / L) := by exact div_pos hc0 hL
  have hosC :
      oscOn w (Set.Icc (t0 - L) (t0 + L)) ≤ D / (c0 / L) := by
    simpa using
      oscOn_Icc_le_div_of_window_lintegral_bound (w := w) hw hw_rc (a := t0 - L) (b := t0 + L)
        (D := D) (c := (c0 / L)) hab hD hc hφ_lower hlin
  -- simplify `D / (c0/L) = (D/c0) * L`.
  have : D / (c0 / L) = (D / c0) * L := by
    field_simp [hL.ne', (ne_of_gt hc0)]
  simpa [this, mul_assoc] using hosC

theorem oscOn_Icc_whitney_le_div_c0Poisson_mul_L_of_poissonPlateau
    {w : ℝ → ℝ} (hw : Antitone w) (hw_rc : ∀ x, ContinuousWithinAt w (Ici x) x)
    {ψ : ℝ → ℝ≥0∞} {b L t0 D : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hc0_top : c0PoissonENN ψ ≠ ⊤) (hc0 : 0 < c0Poisson ψ)
    (hlin :
      ∫⁻ t, certificateWindowPoisson b ψ L t0 t
          ∂(stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc))
        ≤ ENNReal.ofReal D) :
    oscOn w (Set.Icc (t0 - L) (t0 + L)) ≤ (D / (c0Poisson ψ)) * L := by
  -- This is the previous theorem, with `hpoisson_plateau` derived from the definition of `c0Poisson`.
  refine
    oscOn_Icc_whitney_le_div_c0_mul_L_of_poissonPlateau (w := w) hw hw_rc (ψ := ψ) (b := b)
      (L := L) (t0 := t0) (D := D) (c0 := c0Poisson ψ) hL hD hc0
      (hpoisson_plateau := hpoisson_plateau_of_c0Poisson (ψ := ψ) (b := b) hc0_top hb0 hb1)
      (hlin := hlin)

end BRF
end RiemannRecognitionGeometry
