/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# John-Nirenberg Inequality for BMO Functions

This module provides the John-Nirenberg inequality, which is the key tool
for proving the Fefferman-Stein BMO→Carleson embedding.

## Main Results

- `johnNirenberg_exp_decay`: The exponential distribution bound for BMO functions
- `bmo_Lp_bound`: BMO functions are in L^p for all p < ∞

## Mathematical Background

The John-Nirenberg inequality (1961) states that for f ∈ BMO:

  |{x ∈ I : |f(x) - f_I| > λ}| ≤ C₁ · |I| · exp(-C₂ · λ / ‖f‖_BMO)

This exponential decay is the key property that distinguishes BMO from L^∞.
It implies:
1. f ∈ L^p(loc) for all p < ∞
2. The Poisson extension gradient is controlled

## References

- John & Nirenberg (1961), "On functions of bounded mean oscillation", CPAM 14
- Garnett, "Bounded Analytic Functions", Chapter VI
- Stein, "Harmonic Analysis", Chapter IV
-/

import RiemannRecognitionGeometry.Basic
import RiemannRecognitionGeometry.FeffermanStein
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Real MeasureTheory Set

namespace RiemannRecognitionGeometry

/-! ## Dyadic Intervals

Dyadic intervals are the building blocks for the Calderón-Zygmund decomposition.
-/

/-- A dyadic interval of generation n starting at k · 2^(-n). -/
structure DyadicInterval where
  generation : ℕ  -- n: the "level" (higher = smaller intervals)
  index : ℤ       -- k: which interval at this level
  deriving DecidableEq

/-- The left endpoint of a dyadic interval. -/
def DyadicInterval.left (D : DyadicInterval) : ℝ :=
  D.index * (2 : ℝ)^(-(D.generation : ℤ))

/-- The right endpoint of a dyadic interval. -/
def DyadicInterval.right (D : DyadicInterval) : ℝ :=
  (D.index + 1) * (2 : ℝ)^(-(D.generation : ℤ))

/-- The length of a dyadic interval is 2^(-n). -/
def DyadicInterval.length (D : DyadicInterval) : ℝ :=
  (2 : ℝ)^(-(D.generation : ℤ))

/-- The interval as a set. -/
def DyadicInterval.toSet (D : DyadicInterval) : Set ℝ :=
  Icc D.left D.right

/-- Dyadic interval length is positive. -/
lemma DyadicInterval.length_pos (D : DyadicInterval) : D.length > 0 := by
  unfold length
  exact zpow_pos_of_pos (by norm_num : (2:ℝ) > 0) _

/-- The parent of a dyadic interval (one level up). -/
def DyadicInterval.parent (D : DyadicInterval) : DyadicInterval :=
  { generation := D.generation - 1
    index := D.index / 2 }

/-- The left child of a dyadic interval. -/
def DyadicInterval.leftChild (D : DyadicInterval) : DyadicInterval :=
  { generation := D.generation + 1
    index := 2 * D.index }

/-- The right child of a dyadic interval. -/
def DyadicInterval.rightChild (D : DyadicInterval) : DyadicInterval :=
  { generation := D.generation + 1
    index := 2 * D.index + 1 }

/-! ## Average and Oscillation on Sets -/

/-- The average of f over a set S with finite positive measure. -/
def setAverage (f : ℝ → ℝ) (S : Set ℝ) (μ : Measure ℝ := volume) : ℝ :=
  if h : μ S ≠ 0 ∧ μ S ≠ ⊤ then
    (μ S).toReal⁻¹ * ∫ x in S, f x ∂μ
  else 0

/-- The mean oscillation of f over a set S. -/
def setMeanOscillation (f : ℝ → ℝ) (S : Set ℝ) (μ : Measure ℝ := volume) : ℝ :=
  if h : μ S ≠ 0 ∧ μ S ≠ ⊤ then
    (μ S).toReal⁻¹ * ∫ x in S, |f x - setAverage f S μ| ∂μ
  else 0

/-- f is in BMO' if all its mean oscillations are bounded by some M > 0. -/
def InBMO' (f : ℝ → ℝ) : Prop :=
  ∃ M : ℝ, M > 0 ∧ ∀ a b : ℝ, a < b → setMeanOscillation f (Icc a b) ≤ M

/-! ## Calderón-Zygmund Decomposition

The CZ decomposition splits a function at level λ into "good" and "bad" parts.
-/

/-- For a locally integrable function f and level t > 0, the Calderón-Zygmund
    decomposition finds maximal dyadic intervals where the average exceeds t.

    **Mathematical Statement**:
    Given f ∈ L¹(I₀) and t > (1/|I₀|)∫_{I₀}|f|, there exists a collection
    {Qⱼ} of disjoint dyadic subintervals of I₀ such that:
    1. t < (1/|Qⱼ|)∫_{Qⱼ}|f| ≤ 2t  (selection criterion)
    2. |f(x)| ≤ t for a.e. x ∈ I₀ \ ⋃ⱼQⱼ  (good part bound)
    3. Σⱼ|Qⱼ| ≤ (1/t)∫_{I₀}|f|  (total measure bound)
-/
structure CZDecomposition (f : ℝ → ℝ) (I₀ : Set ℝ) (t : ℝ) where
  /-- The "bad" dyadic intervals where average > t -/
  badIntervals : Set DyadicInterval
  /-- The bad intervals are pairwise disjoint -/
  disjoint : ∀ D₁ D₂ : DyadicInterval, D₁ ∈ badIntervals → D₂ ∈ badIntervals →
             D₁ ≠ D₂ → Disjoint D₁.toSet D₂.toSet
  /-- Each bad interval has average between t and 2t -/
  avgBound : ∀ D ∈ badIntervals,
             t < setAverage (|f ·|) D.toSet ∧ setAverage (|f ·|) D.toSet ≤ 2 * t
  /-- On the good part, |f| ≤ t a.e. -/
  goodBound : ∀ᵐ x ∂volume, x ∈ I₀ →
              (∀ D ∈ badIntervals, x ∉ D.toSet) → |f x| ≤ t

/-- The Calderón-Zygmund decomposition exists for any locally integrable function
    and level t above the average. -/
axiom czDecomposition_exists (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_int : IntegrableOn f (Icc a b))
    (t : ℝ) (ht_pos : t > 0)
    (ht_above_avg : t > (b - a)⁻¹ * ∫ x in Icc a b, |f x|) :
    ∃ cz : CZDecomposition f (Icc a b) t, True

/-! ## The John-Nirenberg Inequality -/

/-- **The John-Nirenberg Constants**.
    The inequality holds with C₁ = e and C₂ = 1/(2e). -/
def JN_C1 : ℝ := Real.exp 1  -- e ≈ 2.718
def JN_C2 : ℝ := 1 / (2 * Real.exp 1)  -- 1/(2e) ≈ 0.184

lemma JN_C1_pos : JN_C1 > 0 := Real.exp_pos 1
lemma JN_C2_pos : JN_C2 > 0 := by unfold JN_C2; positivity

/-- **THEOREM (John-Nirenberg Inequality)**:
    For f ∈ BMO and any interval I, the distribution of |f - f_I| decays exponentially:

    |{x ∈ I : |f(x) - f_I| > t}| ≤ C₁ · |I| · exp(-C₂ · t / ‖f‖_BMO)

    **Proof Outline** (following Garnett, Chapter VI):
    1. Fix I and let M = ‖f‖_BMO
    2. For t = k·M (k ∈ ℕ), apply CZ decomposition at level t
    3. The bad intervals at level k are contained in bad intervals at level k-1
    4. By induction: measure decays geometrically with ratio ≤ 1/2
    5. This gives exponential decay in t

    **Key Lemma**: If J ⊂ I is a maximal bad interval at level t, then
    |J| ≤ (1/t) ∫_J |f - f_I| ≤ M·|I|/t
-/
theorem johnNirenberg_exp_decay (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b' : ℝ, a' < b' → meanOscillation f a' b' ≤ M)
    (t : ℝ) (ht_pos : t > 0) :
    volume {x ∈ Icc a b | |f x - intervalAverage f a b| > t} ≤
    ENNReal.ofReal (JN_C1 * (b - a) * Real.exp (-JN_C2 * t / M)) := by
  -- The proof uses the Calderón-Zygmund decomposition iteratively.
  -- At each level k·M, the measure of the "bad" set shrinks by a factor of at least 1/2.
  --
  -- **Step 1**: For t ≤ M, use the trivial bound |{...}| ≤ |I|
  -- **Step 2**: For t > M, use induction on k = ⌊t/M⌋
  --
  -- The key insight is that on each maximal bad interval Q at level k·M:
  -- - |Q| ≤ (1/(k·M)) ∫_Q |f - f_I|
  -- - The BMO condition gives ∫_Q |f - f_Q| ≤ M·|Q|
  -- - So the bad intervals at level (k+1)·M within Q have total measure ≤ |Q|/2
  --
  -- This geometric decay gives: measure at level k·M ≤ |I|·2^(-k)
  -- Converting to continuous t: measure ≤ C·|I|·exp(-c·t/M)
  sorry

/-- **COROLLARY**: BMO functions are in L^p for all p < ∞.

    For f ∈ BMO and any interval I:
    (1/|I|) ∫_I |f - f_I|^p ≤ C_p · ‖f‖_BMO^p

    **Proof**: Integrate the distribution function bound from John-Nirenberg.
    |{|f - f_I| > t}| ≤ C·|I|·exp(-c·t/M) implies the L^p bound via:
    ∫|f - f_I|^p = p ∫_0^∞ t^{p-1} |{|f - f_I| > t}| dt

    The integral ∫_0^∞ t^{p-1} C₁|I|exp(-C₂t/M) dt = C₁|I| · (M/C₂)^p · Γ(p)
    which gives C_p = C₁ · (1/C₂)^p · Γ(p) for the normalized bound. -/
theorem bmo_Lp_bound (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b' : ℝ, a' < b' → meanOscillation f a' b' ≤ M)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C_p : ℝ, C_p > 0 ∧
    (b - a)⁻¹ * ∫ x in Icc a b, |f x - intervalAverage f a b|^p ≤ C_p * M^p := by
  -- The constant depends on p through the gamma function integral
  -- C_p = C₁ · (1/C₂)^p · Γ(p) where C₁ = e, C₂ = 1/(2e)
  -- So (1/C₂)^p = (2e)^p and Γ(p) ≤ p! for integer p
  --
  -- For the proof:
  -- 1. Use the layer cake formula: ∫|f-f_I|^p = p ∫_0^∞ t^{p-1} μ({|f-f_I|>t}) dt
  -- 2. Apply johnNirenberg_exp_decay: μ({|f-f_I|>t}) ≤ C₁|I|exp(-C₂t/M)
  -- 3. Compute: p ∫_0^∞ t^{p-1} exp(-C₂t/M) dt = p · (M/C₂)^p · Γ(p)/p = (M/C₂)^p · Γ(p)
  -- 4. Divide by |I| to get the normalized bound
  use JN_C1 * (2 * Real.exp 1)^p * Real.Gamma (p + 1) / p
  constructor
  · -- Positivity of the constant
    apply div_pos
    · apply mul_pos
      apply mul_pos JN_C1_pos
      apply Real.rpow_pos_of_pos (by positivity : 2 * Real.exp 1 > 0)
      exact Real.Gamma_pos_of_pos (by linarith : p + 1 > 0)
    · linarith
  · -- The actual bound (uses johnNirenberg_exp_decay as black box)
    sorry

/-- **APPLICATION**: The pointwise bound for BMO functions against smooth kernels.

    For f ∈ BMO with ‖f‖_BMO ≤ M and a kernel K with ∫|K| < ∞:
    |∫ K(t) · (f(t) - c) dt| ≤ C · M · ∫|K|

    This is used in the Fefferman-Stein proof to bound Poisson extension gradients.

    **Proof outline**:
    1. For kernel K supported on interval I, use Hölder:
       |∫_I K(f-c)| ≤ ‖K‖_{L^q(I)} · ‖f-c‖_{L^p(I)}
    2. Take q close to 1, p large (using BMO ⊂ L^p from John-Nirenberg)
    3. The L^p bound gives ‖f-c‖_p ≤ C_p · M · |I|^{1/p}
    4. As p → ∞, ‖K‖_q → ‖K‖_1, giving the result

    For kernels on all of ℝ, split into dyadic shells and sum. -/
theorem bmo_kernel_bound (f : ℝ → ℝ) (K : ℝ → ℝ)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a b : ℝ, a < b → meanOscillation f a b ≤ M)
    (hK_int : Integrable K)
    (c : ℝ) :
    ∃ C : ℝ, C > 0 ∧
    |∫ t, K t * (f t - c)| ≤ C * M * ∫ t, |K t| := by
  -- The constant C comes from the BMO-to-L^p constant as p → ∞
  -- and the geometry of dyadic shell summation
  use 2 * JN_C1  -- Universal constant depending only on JN constants
  constructor
  · exact mul_pos (by norm_num : (0:ℝ) < 2) JN_C1_pos
  · -- The proof uses:
    -- 1. Split ℝ into dyadic intervals around the support of K
    -- 2. On each interval, apply Hölder with large p
    -- 3. Use bmo_Lp_bound to control ‖f - c‖_p
    -- 4. Sum the geometric series (exponential decay from JN)
    sorry

/-! ## Connection to Fefferman-Stein

The John-Nirenberg inequality is the key to proving that BMO functions have
Poisson extensions with controlled gradients, which leads to the Carleson
measure condition.
-/

/-- Using John-Nirenberg, we can prove the gradient bound from oscillation.
    This is the key lemma that `poissonExtension_gradient_bound_from_oscillation`
    in FeffermanStein.lean needs.

    **Proof**:
    1. Let I = [x - y, x + y] be the natural interval for the Poisson kernel
    2. Write ∂u/∂x = ∫ ∂P/∂x(x-t, y) · (f(t) - f_I) dt
       (Since ∫ ∂P/∂x dt = 0, adding f_I doesn't change the integral)
    3. Apply bmo_kernel_bound with K(t) = ∂P/∂x(x-t, y):
       |∂u/∂x| ≤ C · M · ∫|∂P/∂x(x-t, y)| dt
    4. Use poissonKernel_dx_integral_bound: ∫|∂P/∂x| ≤ 2/(πy)
    5. Combine: |∂u/∂x| ≤ C · M · 2/(πy) = O(M/y)

    Similar argument for ∂u/∂y gives the full gradient bound. -/
theorem poisson_gradient_bound_via_JN (f : ℝ → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a b : ℝ, a < b → meanOscillation f a b ≤ M) :
    ∃ C : ℝ, C > 0 ∧ ‖poissonExtension_gradient f x y‖ ≤ C * M / y := by
  -- Use bmo_kernel_bound with the Poisson kernel derivative as K
  -- The constant C = 2 * JN_C1 * (2/π) from the composition
  let I := Icc (x - y) (x + y)
  let f_I := intervalAverage f (x - y) (x + y)
  -- Apply bmo_kernel_bound for the x-derivative
  have hK_int : Integrable (fun t => poissonKernel_dx (x - t) y) := by
    sorry  -- Integrability of Poisson kernel derivative (standard)
  obtain ⟨C_kernel, hC_pos, h_bound⟩ := bmo_kernel_bound f (fun t => poissonKernel_dx (x - t) y)
    M hM_pos h_bmo hK_int f_I
  -- The gradient norm is bounded by the sum of partial derivative bounds
  use 2 * C_kernel * (2 / Real.pi)
  constructor
  · positivity
  · -- Combine the kernel bound with poissonKernel_dx_integral_bound
    sorry

end RiemannRecognitionGeometry
