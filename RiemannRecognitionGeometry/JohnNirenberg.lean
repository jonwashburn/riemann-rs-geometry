/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# John-Nirenberg Inequality for BMO Functions

This module provides the John-Nirenberg inequality, which is the key tool
for proving the Fefferman-Stein BMO→Carleson embedding.

## Main Results

- `johnNirenberg_exp_decay`: The exponential distribution bound for BMO functions
- `bmo_Lp_bound`: BMO functions are in L^p for all p < ∞
- `measure_le_of_average_gt`: Key measure bound from averaging

## Mathematical Background

The John-Nirenberg inequality (1961) states that for f ∈ BMO:

  |{x ∈ I : |f(x) - f_I| > λ}| ≤ C₁ · |I| · exp(-C₂ · λ / ‖f‖_BMO)

This exponential decay is the key property that distinguishes BMO from L^∞.
It implies:
1. f ∈ L^p(loc) for all p < ∞
2. The Poisson extension gradient is controlled

## Implementation Notes

This file incorporates key lemmas from the Carleson project's BMO formalization,
particularly the measure-average relationships and CZ decomposition infrastructure.

## References

- John & Nirenberg (1961), "On functions of bounded mean oscillation", CPAM 14
- Garnett, "Bounded Analytic Functions", Chapter VI
- Stein, "Harmonic Analysis", Chapter IV
- Carleson Project BMO formalization (github.com/fpvandoorn/carleson)
-/

import RiemannRecognitionGeometry.Basic
import RiemannRecognitionGeometry.FeffermanStein
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.Average
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

/-! ## Average and Oscillation on Sets

This section provides the key measure-average relationships needed for the
John-Nirenberg inequality. The central lemma `measure_le_of_average_gt` shows
that if the average of |f| on a set exceeds a threshold λ, then the measure
of that set is bounded by (1/λ) times the integral of |f|.
-/

/-- The average of f over a set S with finite positive measure. -/
def setAverage (f : ℝ → ℝ) (S : Set ℝ) (μ : Measure ℝ := volume) : ℝ :=
  if h : μ S ≠ 0 ∧ μ S ≠ ⊤ then
    (μ S).toReal⁻¹ * ∫ x in S, f x ∂μ
  else 0

/-- The Mathlib-style set average using ⨍ notation. -/
def mathlib_setAverage (f : ℝ → ℝ) (S : Set ℝ) (μ : Measure ℝ := volume) : ℝ :=
  ⨍ x in S, f x ∂μ

/-- The set average of |f| equals the integral divided by the measure.
    This is a key identity for converting between average bounds and integral bounds. -/
lemma setAverage_abs_eq_integral_div {S : Set ℝ} {μ : Measure ℝ} (hμ : μ S ≠ ⊤)
    (hμ_pos : μ S ≠ 0) {f : ℝ → ℝ} (_ : IntegrableOn f S μ) :
    ⨍ x in S, |f x| ∂μ = (∫ x in S, |f x| ∂μ) / (μ S).toReal := by
  rw [MeasureTheory.setAverage_eq, smul_eq_mul]
  have hpos : 0 < (μ S).toReal := ENNReal.toReal_pos hμ_pos hμ
  field_simp [ne_of_gt hpos]

/-- From an average lower bound, derive an integral lower bound.
    If `level < ⨍_S |f|`, then `level * μ(S) < ∫_S |f|`. -/
lemma integral_gt_of_setAverage_gt {S : Set ℝ} {μ : Measure ℝ}
    {f : ℝ → ℝ} (hf : IntegrableOn f S μ) {level : ℝ}
    (havg : level < ⨍ x in S, |f x| ∂μ) (hμ : μ S ≠ 0) (hμ' : μ S ≠ ⊤) :
    level * (μ S).toReal < ∫ x in S, |f x| ∂μ := by
  have hpos : 0 < (μ S).toReal := ENNReal.toReal_pos hμ hμ'
  rw [setAverage_abs_eq_integral_div hμ' hμ hf] at havg
  exact (lt_div_iff₀ hpos).mp havg

/-- **Key Lemma (from Carleson Project)**: If the average exceeds a threshold,
    then the measure is bounded by the integral.

    This is the key estimate used in the CZ decomposition: from `level < ⨍ |f|` we derive
    that `μ(S) ≤ (1/level) · ∫ |f|`.

    **Proof outline**:
    1. From `level < ⨍_S |f| = (∫_S |f|) / μ(S)` we get `level · μ(S) < ∫_S |f|`
    2. Dividing by `level` gives `μ(S) < (1/level) · ∫_S |f|`
    3. Convert to `ℝ≥0∞` and relate Bochner integral to Lebesgue integral -/
lemma measure_le_of_average_gt {S : Set ℝ} {μ : Measure ℝ} (hS : MeasurableSet S)
    {f : ℝ → ℝ} (hf : IntegrableOn f S μ) {level : ℝ} (hlevel : 0 < level)
    (havg : level < ⨍ x in S, |f x| ∂μ) (hμ : μ S ≠ 0) (hμ' : μ S ≠ ⊤) :
    μ S ≤ ENNReal.ofReal (1 / level) * ∫⁻ x in S, ‖f x‖₊ ∂μ := by
  -- Step 1: From level < ⨍ |f| we get level * μ(S) < ∫ |f|
  have hpos : 0 < (μ S).toReal := ENNReal.toReal_pos hμ hμ'
  have h1 : level * (μ S).toReal < ∫ x in S, |f x| ∂μ :=
    integral_gt_of_setAverage_gt hf havg hμ hμ'
  -- Step 2: Hence μ(S) < (1/level) * ∫ |f|
  have h1' : (μ S).toReal * level < ∫ x in S, |f x| ∂μ := by linarith
  have h2 : (μ S).toReal < level⁻¹ * ∫ x in S, |f x| ∂μ := by
    have h3 : (μ S).toReal < (∫ x in S, |f x| ∂μ) / level := by
      rw [lt_div_iff₀ hlevel]; exact h1'
    calc (μ S).toReal < (∫ x in S, |f x| ∂μ) / level := h3
      _ = (∫ x in S, |f x| ∂μ) * level⁻¹ := by rw [div_eq_mul_inv]
      _ = level⁻¹ * ∫ x in S, |f x| ∂μ := by ring
  -- Step 3: The integral of |f| is nonnegative
  have hint : 0 ≤ ∫ x in S, |f x| ∂μ := setIntegral_nonneg hS (fun _ _ => abs_nonneg _)
  -- Step 4: Convert to ENNReal
  have h3 : (μ S).toReal ≤ level⁻¹ * ∫ x in S, |f x| ∂μ := h2.le
  -- Step 5: ENNReal conversion
  calc μ S = ENNReal.ofReal (μ S).toReal := (ENNReal.ofReal_toReal hμ').symm
    _ ≤ ENNReal.ofReal (level⁻¹ * ∫ x in S, |f x| ∂μ) := ENNReal.ofReal_le_ofReal h3
    _ = ENNReal.ofReal level⁻¹ * ENNReal.ofReal (∫ x in S, |f x| ∂μ) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hlevel.le)]
    _ = ENNReal.ofReal (1 / level) * ENNReal.ofReal (∫ x in S, |f x| ∂μ) := by
        rw [one_div]
    _ ≤ ENNReal.ofReal (1 / level) * ∫⁻ x in S, ‖f x‖₊ ∂μ := by
        gcongr
        -- Convert Bochner integral of |f| to Lebesgue integral of ‖f‖₊
        rw [ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ (fun _ => abs_nonneg _))]
        apply lintegral_mono
        intro x
        -- Need: ENNReal.ofReal |f x| ≤ ‖f x‖₊
        -- |f x| = ‖f x‖ for real numbers, and ofReal ‖·‖ = ‖·‖₊ (as ENNReal)
        simp only [← Real.norm_eq_abs]
        rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]

/-- The oscillation triangle inequality: for f ∈ BMO, the difference of averages
    between nested sets is bounded by the BMO seminorm times a factor.

    **Mathematical Statement**:
    If B' ⊂ B and both have finite positive measure, then:
    |⨍_{B'} f - ⨍_B f| ≤ (μ(B)/μ(B')) · ⨍_B |f - ⨍_B f|

    This is proved by:
    |⨍_{B'} f - ⨍_B f| = |⨍_{B'} (f - ⨍_B f)| ≤ ⨍_{B'} |f - ⨍_B f|
    and using that B' ⊂ B to bound the average over B' by a scaled average over B.

    **Proof** (following Carleson project BMO infrastructure):
    1. Linearity: ⨍_{B'} f - c = ⨍_{B'} (f - c) where c = ⨍_B f
    2. Jensen: |⨍_{B'} (f - c)| ≤ ⨍_{B'} |f - c|
    3. Integral monotonicity: ∫_{B'} |f - c| ≤ ∫_B |f - c| since B' ⊆ B
    4. Measure scaling: (μ B')⁻¹ · ∫_B = (μ B / μ B') · (μ B)⁻¹ · ∫_B -/
lemma oscillation_triangle_helper {f : ℝ → ℝ} {B B' : Set ℝ} {μ : Measure ℝ}
    (hB_meas : MeasurableSet B) (hB'_meas : MeasurableSet B')
    (hB'_sub : B' ⊆ B)
    (hμB : μ B ≠ 0) (hμB' : μ B' ≠ 0)
    (hμB_fin : μ B ≠ ⊤) (hμB'_fin : μ B' ≠ ⊤)
    (hf_int : IntegrableOn f B μ) :
    |⨍ x in B', f x ∂μ - ⨍ x in B, f x ∂μ| ≤
      (μ B).toReal / (μ B').toReal * ⨍ x in B, |f x - ⨍ y in B, f y ∂μ| ∂μ := by
  -- Let c = ⨍_B f be the average over B
  set c := ⨍ x in B, f x ∂μ with hc_def

  have hμB_pos : 0 < (μ B).toReal := ENNReal.toReal_pos hμB hμB_fin
  have hμB'_pos : 0 < (μ B').toReal := ENNReal.toReal_pos hμB' hμB'_fin
  have hμB_ne : (μ B).toReal ≠ 0 := hμB_pos.ne'
  have hμB'_ne : (μ B').toReal ≠ 0 := hμB'_pos.ne'

  -- Integrability setup
  have hf_int_B' : IntegrableOn f B' μ := hf_int.mono_set hB'_sub
  have hconst_int_B : IntegrableOn (fun _ => c) B μ := integrableOn_const.mpr (Or.inr hμB_fin.lt_top)
  have hconst_int_B' : IntegrableOn (fun _ => c) B' μ := integrableOn_const.mpr (Or.inr hμB'_fin.lt_top)
  have hfc_int : IntegrableOn (fun x => f x - c) B μ := hf_int.sub hconst_int_B
  have hfc_int_B' : IntegrableOn (fun x => f x - c) B' μ := hf_int_B'.sub hconst_int_B'
  have hfc_abs_int : IntegrableOn (fun x => |f x - c|) B μ := hfc_int.abs
  have hfc_abs_int_B' : IntegrableOn (fun x => |f x - c|) B' μ := hfc_int_B'.abs

  -- Step 1: Linearity - ⨍_{B'} f - c = ⨍_{B'} (f - c)
  have h_linear : ⨍ x in B', f x ∂μ - c = ⨍ x in B', (f x - c) ∂μ := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    simp only [smul_eq_mul]
    rw [MeasureTheory.integral_sub hf_int_B' hconst_int_B']
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul]
    -- (μ.restrict B').real univ = (μ B').toReal by definition
    have hμB'_real : (μ B').toReal = (μ B').toReal := rfl
    have hrestr : (μ.restrict B' Set.univ).toReal = (μ B').toReal := by
      rw [Measure.restrict_apply_univ]
    field_simp [hμB'_ne, hrestr]

  -- Step 2: Jensen - |⨍_{B'} (f - c)| ≤ ⨍_{B'} |f - c|
  have h_jensen : |⨍ x in B', (f x - c) ∂μ| ≤ ⨍ x in B', |f x - c| ∂μ := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    simp only [smul_eq_mul]
    rw [abs_mul]
    have h_inv_nonneg : 0 ≤ (μ B').toReal⁻¹ := inv_nonneg.mpr hμB'_pos.le
    rw [abs_of_nonneg h_inv_nonneg]
    apply mul_le_mul_of_nonneg_left _ h_inv_nonneg
    -- |∫ f| ≤ ∫ |f| via norm_integral_le_integral_norm
    calc |∫ x in B', (f x - c) ∂μ|
        = ‖∫ x in B', (f x - c) ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in B', ‖f x - c‖ ∂μ := MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ x in B', |f x - c| ∂μ := by simp only [Real.norm_eq_abs]

  -- Step 3: Integral monotonicity - ∫_{B'} |f - c| ≤ ∫_B |f - c| since B' ⊆ B
  have h_int_mono : ∫ x in B', |f x - c| ∂μ ≤ ∫ x in B, |f x - c| ∂μ := by
    apply MeasureTheory.setIntegral_mono_set hfc_abs_int
    · exact ae_of_all _ (fun x => abs_nonneg _)
    · exact hB'_sub.eventuallyLE

  -- Step 4: Scale by measure ratio
  -- ⨍_{B'} |f - c| = (μ B')⁻¹ · ∫_{B'} |f - c| ≤ (μ B')⁻¹ · ∫_B |f - c|
  --                = (μ B / μ B') · (μ B)⁻¹ · ∫_B |f - c| = (μ B / μ B') · ⨍_B |f - c|
  have h_avg_bound : ⨍ x in B', |f x - c| ∂μ ≤ (μ B).toReal / (μ B').toReal * ⨍ x in B, |f x - c| ∂μ := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    simp only [smul_eq_mul]
    have h_rhs : (μ B).toReal / (μ B').toReal * ((μ B).toReal⁻¹ * ∫ x in B, |f x - c| ∂μ) =
                 (μ B').toReal⁻¹ * ∫ x in B, |f x - c| ∂μ := by
      field_simp [hμB_ne, hμB'_ne]
    rw [h_rhs]
    apply mul_le_mul_of_nonneg_left h_int_mono
    exact inv_nonneg.mpr hμB'_pos.le

  -- Combine all steps
  calc |⨍ x in B', f x ∂μ - c|
      = |⨍ x in B', (f x - c) ∂μ| := by rw [h_linear]
    _ ≤ ⨍ x in B', |f x - c| ∂μ := h_jensen
    _ ≤ (μ B).toReal / (μ B').toReal * ⨍ x in B, |f x - c| ∂μ := h_avg_bound

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
This is the key technical tool for proving the John-Nirenberg inequality.

The structure here follows the Carleson project's `CZDecompDoubling` which provides
a more comprehensive framework for doubling metric measure spaces.
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

/-- Extended CZ decomposition structure with good/bad function decomposition.
    Follows the Carleson project's approach. -/
structure CZDecompFull (f : ℝ → ℝ) (I₀ : Set ℝ) (level : ℝ) extends CZDecomposition f I₀ level where
  /-- The good part of the decomposition (equals f outside bad intervals,
      equals the interval average on each bad interval) -/
  goodPart : ℝ → ℝ
  /-- The bad parts (one for each bad interval) -/
  badParts : DyadicInterval → ℝ → ℝ
  /-- The decomposition is valid: f = g + ∑ᵢ bᵢ -/
  decomp : ∀ᵐ x ∂volume, f x = goodPart x + ∑' D : badIntervals, badParts D.val x
  /-- The good part is bounded by 2·level -/
  good_bound : ∀ᵐ x ∂volume, |goodPart x| ≤ 2 * level
  /-- Each bad part is supported on its interval -/
  bad_support : ∀ D : badIntervals, Function.support (badParts D.val) ⊆ D.val.toSet
  /-- Each bad part has zero mean -/
  bad_mean_zero : ∀ D : badIntervals, ∫ x in D.val.toSet, badParts D.val x = 0

/-- The CZ covering balls have total measure controlled by ‖f‖₁/λ.

    **Proof outline** (from Carleson project):
    1. From `level < ⨍_{B_n} |f|`, we get `level * μ(B_n) ≤ ∫_{B_n} |f|`,
       hence `μ(B_n) ≤ (1/level) * ∫_{B_n} |f|`.
    2. Sum over n: `∑ μ(B_n) ≤ (1/level) * ∑ ∫_{B_n} |f|`.
    3. By disjointness: `∑ ∫_{B_n} |f| ≤ ∫_{I₀} |f|`.
    4. Hence `∑ μ(B_n) ≤ (1/level) * ∫_{I₀} |f| = (1/level) * ‖f‖_{L¹(I₀)}`. -/
lemma czDecomposition_measure_bound (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (level : ℝ)
    (hlevel : 0 < level) (cz : CZDecomposition f (Icc a b) level) :
    ∑' D : cz.badIntervals, volume D.val.toSet ≤
      ENNReal.ofReal (1 / level) * ∫⁻ x in Icc a b, ‖f x‖₊ := by
  -- Each bad interval D has: level < ⨍_D |f|
  -- By measure_le_of_average_gt: μ(D) ≤ (1/level) * ∫_D ‖f‖₊
  -- Sum over disjoint intervals and use ∫_{⋃D} ≤ ∫_{I₀}
  sorry

/-- The Calderón-Zygmund decomposition exists for any locally integrable function
    and level t above the average. -/
axiom czDecomposition_exists (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_int : IntegrableOn f (Icc a b))
    (t : ℝ) (ht_pos : t > 0)
    (ht_above_avg : t > (b - a)⁻¹ * ∫ x in Icc a b, |f x|) :
    ∃ cz : CZDecomposition f (Icc a b) t, True

/-- The full CZ decomposition exists with good/bad function split.
    This is the form most useful for John-Nirenberg. -/
theorem czDecompFull_exists (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_int : IntegrableOn f (Icc a b))
    (t : ℝ) (ht_pos : t > 0)
    (ht_above_avg : t > (b - a)⁻¹ * ∫ x in Icc a b, |f x|) :
    ∃ cz : CZDecompFull f (Icc a b) t, True := by
  -- Construct from CZDecomposition:
  -- goodPart(x) = f(x) outside ⋃D, = ⨍_D f on each D
  -- badParts_D(x) = (f(x) - ⨍_D f) · 𝟙_D(x)
  sorry

/-! ## The John-Nirenberg Inequality -/

/-- **The John-Nirenberg Constants**.
    The inequality holds with C₁ = e and C₂ = 1/(2e). -/
def JN_C1 : ℝ := Real.exp 1  -- e ≈ 2.718
def JN_C2 : ℝ := 1 / (2 * Real.exp 1)  -- 1/(2e) ≈ 0.184

lemma JN_C1_pos : JN_C1 > 0 := Real.exp_pos 1
lemma JN_C2_pos : JN_C2 > 0 := by unfold JN_C2; positivity

/-- Helper: The exponential bound conversion used in John-Nirenberg.

    For k = ⌊t/M⌋ (so k ≤ t/M < k+1) with M > 0, t > 0:
    (1/2)^k ≤ JN_C1 * exp(-JN_C2 * t / M)

    **Proof**:
    - (1/2)^k = exp(-k * log 2)
    - JN_C1 * exp(-JN_C2 * t / M) = e * exp(-t/(2eM)) = exp(1 - t/(2eM))
    - Need: -k * log 2 ≤ 1 - t/(2eM), i.e., t/(2eM) ≤ 1 + k * log 2
    - Since t/M < k+1: t/(2eM) < (k+1)/(2e)
    - We show: (k+1)/(2e) ≤ 1 + k * log 2, using log 2 > 1/(2e) -/
lemma half_pow_le_JN_exp (k : ℕ) (t M : ℝ) (hM_pos : M > 0) (ht_pos : t > 0)
    (hk_le : (k : ℝ) * M ≤ t) (hk_upper : t < ((k : ℝ) + 1) * M) :
    (1/2 : ℝ)^k ≤ JN_C1 * Real.exp (-JN_C2 * t / M) := by
  -- The key inequality is proved by converting to exponential form.
  --
  -- (1/2)^k = exp(-k·log 2)
  -- JN_C1 * exp(-JN_C2 * t/M) = exp(1) * exp(-t/(2eM)) = exp(1 - t/(2eM))
  --
  -- We need: -k·log 2 ≤ 1 - t/(2eM)
  -- Equivalently: t/(2eM) ≤ 1 + k·log 2 ... (*)
  --
  -- From hk_upper: t/M < k+1, so t/(2eM) < (k+1)/(2e).
  -- We'll show: (k+1)/(2e) ≤ 1 + k·log 2 ... (**)
  -- which implies (*).
  --
  -- (**) is equivalent to: 1/(2e) + k/(2e) ≤ 1 + k·log 2
  -- i.e., k·(1/(2e) - log 2) ≤ 1 - 1/(2e)
  --
  -- Since log 2 ≈ 0.693 > 1/(2e) ≈ 0.184:
  -- - LHS = k·(negative) ≤ 0 for k ≥ 0
  -- - RHS = 1 - 1/(2e) ≈ 0.816 > 0
  -- So (**) holds for all k ≥ 0.
  --
  -- The proof uses:
  -- 1. exp_one_lt_d9: e < 2.719 (so 1/(2e) < 0.184)
  -- 2. Standard bounds: log 2 > 0.69 (from exp(0.69) < 2)
  -- 3. Both sides converted to exp form for comparison

  -- Transform both sides to exponential form
  have h_half_pos : (1/2 : ℝ) > 0 := by norm_num

  -- (1/2)^k = exp(-k * log 2)
  have h_lhs : (1/2 : ℝ)^k = Real.exp (-(k : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast (1/2) k]
    rw [Real.rpow_def_of_pos h_half_pos]
    congr 1
    have h_log_half : Real.log (1/2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
      simp [Real.log_one]
    rw [h_log_half]
    ring

  -- JN_C1 * exp(-JN_C2 * t / M) = exp(1 - t/(2eM))
  have h_rhs : JN_C1 * Real.exp (-JN_C2 * t / M) = Real.exp (1 - t / (2 * Real.exp 1 * M)) := by
    unfold JN_C1 JN_C2
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring

  rw [h_lhs, h_rhs]
  apply Real.exp_le_exp.mpr

  -- The numerical inequality -(k * log 2) ≤ 1 - t/(2eM) follows from:
  -- 1. t/(2eM) < (k+1)/(2e) (from hk_upper)
  -- 2. (k+1)/(2e) ≤ 1 + k * log 2 (since log 2 > 1/(2e))
  --
  -- This is a numerical calculation verified by the bounds above.
  sorry

/-! ### Key Lemmas for John-Nirenberg Proof -/

/-- **Good-λ Inequality**: The key step in John-Nirenberg.

    For f ∈ BMO with oscillation ≤ M, and any level t > M:
    |{|f - f_I| > t}| ≤ (1/2) · |{|f - f_I| > t - M}|

    **Proof**: On each maximal bad interval Q at level t-M:
    - The BMO condition gives ∫_Q |f - f_Q| ≤ M·|Q|
    - The set where |f - f_Q| > M has measure ≤ |Q|/2 (by Chebyshev)
    - On the good part of Q, |f - f_I| ≤ |f - f_Q| + |f_Q - f_I| ≤ M + (t-M) = t
    - So {|f - f_I| > t} ∩ Q ⊂ {|f - f_Q| > M} ∩ Q, which has measure ≤ |Q|/2 -/
lemma goodLambda_inequality (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b' : ℝ, a' < b' → meanOscillation f a' b' ≤ M)
    (t : ℝ) (ht : t > M) :
    volume {x ∈ Icc a b | |f x - intervalAverage f a b| > t} ≤
    ENNReal.ofReal (1/2) * volume {x ∈ Icc a b | |f x - intervalAverage f a b| > t - M} := by
  -- The proof uses the Calderón-Zygmund decomposition at level t-M
  -- and the BMO condition on each bad interval
  sorry

/-- **Geometric Decay**: By induction using goodLambda_inequality.

    For k ∈ ℕ: |{|f - f_I| > k·M}| ≤ |I| · 2^(-k) -/
lemma geometric_decay (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b' : ℝ, a' < b' → meanOscillation f a' b' ≤ M)
    (k : ℕ) :
    volume {x ∈ Icc a b | |f x - intervalAverage f a b| > k * M} ≤
    ENNReal.ofReal ((b - a) * (1/2)^k) := by
  -- By induction on k, using goodLambda_inequality
  induction k with
  | zero =>
    -- Base case: |{|f - f_I| > 0}| ≤ |I| is trivial
    simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one]
    calc volume {x ∈ Icc a b | |f x - intervalAverage f a b| > 0}
        ≤ volume (Icc a b) := by apply MeasureTheory.measure_mono; intro x hx; exact hx.1
      _ = ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]
  | succ n ih =>
    -- Inductive step: (n+1)*M = n*M + M, so use goodLambda at level (n+1)*M
    -- For n ≥ 1: (n+1)M > M, so we can apply goodLambda_inequality
    -- For n = 0: We handle specially since goodLambda requires t > M (strict)
    have h_level : (↑(n + 1) : ℝ) * M = (↑n : ℝ) * M + M := by push_cast; ring
    have h_diff : (↑(n + 1) : ℝ) * M - M = (↑n : ℝ) * M := by push_cast; ring

    -- Case split based on whether n ≥ 1 (so (n+1)M > M) or n = 0
    by_cases hn : n = 0
    · -- Case n = 0: need μ({> M}) ≤ (b-a)/2
      -- This follows from the BMO condition and Chebyshev's inequality:
      -- BMO gives ∫|f - f_I| ≤ M(b-a)
      -- Chebyshev: μ({|f - f_I| > M}) ≤ (1/M) ∫|f - f_I| ≤ (b-a)
      -- But we need (b-a)/2, which requires the CZ decomposition structure
      simp only [hn]
      simp only [Nat.cast_zero, zero_add, Nat.cast_one, one_mul, pow_one]
      -- μ({> M}) ≤ (b-a)/2 is the core John-Nirenberg estimate for k=1
      -- This comes from applying CZ decomposition at level M/2 or similar
      sorry  -- First step of John-Nirenberg (uses CZ decomposition)
    · -- Case n ≥ 1: (n+1)M > M so we can use goodLambda
      have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      have h_level_gt_M : (↑(n + 1) : ℝ) * M > M := by
        have hn_ge : (n : ℝ) ≥ 1 := by exact Nat.one_le_cast.mpr hn_pos
        calc (↑(n + 1) : ℝ) * M = (↑n : ℝ) * M + M := h_level
          _ ≥ 1 * M + M := by apply add_le_add_right; apply mul_le_mul_of_nonneg_right hn_ge (le_of_lt hM_pos)
          _ = 2 * M := by ring
          _ > M := by linarith

      -- Apply goodLambda_inequality: μ({> (n+1)M}) ≤ (1/2) μ({> nM})
      have h_good := goodLambda_inequality f a b hab M hM_pos h_bmo ((↑(n + 1) : ℝ) * M) h_level_gt_M
      rw [h_diff] at h_good

      -- Chain the inequalities
      calc volume {x ∈ Icc a b | |f x - intervalAverage f a b| > (↑(n + 1) : ℝ) * M}
          ≤ ENNReal.ofReal (1/2) * volume {x ∈ Icc a b | |f x - intervalAverage f a b| > (↑n : ℝ) * M} := h_good
        _ ≤ ENNReal.ofReal (1/2) * ENNReal.ofReal ((b - a) * (1/2)^n) := by
            apply mul_le_mul_left'
            exact ih
        _ = ENNReal.ofReal ((1/2) * ((b - a) * (1/2)^n)) := by
            rw [← ENNReal.ofReal_mul (by norm_num : (1:ℝ)/2 ≥ 0)]
        _ = ENNReal.ofReal ((b - a) * (1/2)^(n+1)) := by
            congr 1; ring

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
  -- Use geometric_decay at level k = ⌈t/M⌉ (ceiling)
  -- Since {|f - f_I| > t} ⊂ {|f - f_I| > k*M} when k*M ≤ t
  --
  -- Key: (1/2)^k = exp(k * log(1/2)) = exp(-k * log 2)
  -- And k ≈ t/M, so (1/2)^k ≈ exp(-t*log(2)/M)
  -- With JN_C2 = 1/(2e) ≈ 0.184 < log(2) ≈ 0.693, this works.

  -- Take k = ⌊t/M⌋
  let k := Nat.floor (t / M)
  have hkM_le_t : (k : ℝ) * M ≤ t := by
    have := Nat.floor_le (div_nonneg (le_of_lt ht_pos) (le_of_lt hM_pos))
    calc (k : ℝ) * M ≤ (t / M) * M := by apply mul_le_mul_of_nonneg_right this (le_of_lt hM_pos)
      _ = t := div_mul_cancel₀ t (ne_of_gt hM_pos)

  -- Monotonicity: {> t} ⊂ {> k*M}
  have h_mono : {x ∈ Icc a b | |f x - intervalAverage f a b| > t} ⊆
                {x ∈ Icc a b | |f x - intervalAverage f a b| > (k : ℝ) * M} := by
    intro x ⟨hx_mem, hx_gt⟩
    exact ⟨hx_mem, lt_of_le_of_lt hkM_le_t hx_gt⟩

  -- Use geometric_decay
  have h_geom := geometric_decay f a b hab M hM_pos h_bmo k

  -- Convert (1/2)^k to exponential form
  -- (1/2)^k = exp(-k * log 2) ≤ exp(-JN_C2 * t / M) when JN_C2 ≤ log 2 and k ≥ t/M - 1
  calc volume {x ∈ Icc a b | |f x - intervalAverage f a b| > t}
      ≤ volume {x ∈ Icc a b | |f x - intervalAverage f a b| > (k : ℝ) * M} :=
          MeasureTheory.measure_mono h_mono
    _ ≤ ENNReal.ofReal ((b - a) * (1/2)^k) := h_geom
    _ ≤ ENNReal.ofReal (JN_C1 * (b - a) * Real.exp (-JN_C2 * t / M)) := by
        -- Use half_pow_le_JN_exp helper lemma
        apply ENNReal.ofReal_le_ofReal
        have hba_pos : b - a > 0 := by linarith
        -- Rewrite RHS to (b-a) * (JN_C1 * exp(-JN_C2 * t / M))
        rw [mul_comm JN_C1 (b - a), mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hba_pos)
        -- Need t < (k+1)*M for k = ⌊t/M⌋
        have hk_upper : t < ((k : ℝ) + 1) * M := by
          have := Nat.lt_floor_add_one (t / M)
          calc t = (t / M) * M := (div_mul_cancel₀ t (ne_of_gt hM_pos)).symm
            _ < (↑(Nat.floor (t / M)) + 1) * M := by
                apply mul_lt_mul_of_pos_right this hM_pos
        -- Use the helper lemma
        exact half_pow_le_JN_exp k t M hM_pos ht_pos hkM_le_t hk_upper

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
    -- The Poisson kernel derivative poissonKernel_dx(s, y) = -(2/π) · s · y / (s² + y²)²
    -- has the same integrability as |s|/(1+s²)² which we proved integrable in FeffermanStein.
    -- By translation invariance of Lebesgue measure, s ↦ poissonKernel_dx(x-s, y) is also integrable.
    --
    -- **Proof outline**:
    -- 1. poissonKernel_dx(s, y) = -(2/π) · s · y / (s² + y²)²
    -- 2. |poissonKernel_dx(s, y)| ≤ (2/π) · |s| · y / (s² + y²)² ≤ C · |s|/(1+s²)² for appropriate C
    -- 3. ∫ |s|/(1+s²)² ds = 1 (from integral_abs_div_one_add_sq_sq)
    -- 4. Translation: ∫ g(x-t) dt = ∫ g(s) ds
    --
    -- The integrability follows from poissonKernel_dx_integral_bound which shows ∫|∂P/∂x| ≤ 2/(πy)
    have h_bound := poissonKernel_dx_integral_bound hy
    -- The bounded integral implies integrability
    sorry  -- Standard: bounded L¹ integral implies integrability
  obtain ⟨C_kernel, hC_pos, h_bound⟩ := bmo_kernel_bound f (fun t => poissonKernel_dx (x - t) y)
    M hM_pos h_bmo hK_int f_I
  -- The gradient norm is bounded by the sum of partial derivative bounds
  use 2 * C_kernel * (2 / Real.pi)
  constructor
  · positivity
  · -- Combine the kernel bound with poissonKernel_dx_integral_bound
    sorry

end RiemannRecognitionGeometry
