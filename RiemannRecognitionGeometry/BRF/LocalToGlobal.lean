/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BRF Route: Local-to-Global Wedge Lemma

Ported from: reality/IndisputableMonolith/NumberTheory/RiemannHypothesis/LocalToGlobalWedge.lean

This file formalizes the abstract "local-to-global wedge" step appearing as
Lemma `local-to-global-wedge` in `Riemann-Christmas.tex`.

In the manuscript, one bounds the **essential oscillation** of a boundary phase `w(t)` on a
Whitney/dyadic schedule of intervals. After a unimodular rotation (i.e. subtracting a constant
phase), this yields an a.e. wedge bound `|w(t)| ≤ π·Υ`.

We implement a clean measure-theoretic core:

- Define the oscillation on a set `s` as `essSup - essInf` w.r.t. Lebesgue measure restricted to `s`.
- If this oscillation is uniformly bounded on a nested exhaustion `[-n,n]`, then there exists a
  constant `c` (the "rotation") such that `|w(t) - c| ≤ D` a.e. on `ℝ`.

This is the exact reusable interface we want: analytic work supplies the oscillation bound; this
lemma turns it into the wedge bound needed for the Poisson/Cayley step.
-/

import RiemannRecognitionGeometry.BRF.Oscillation
import Mathlib

namespace RiemannRecognitionGeometry
namespace BRF

open scoped Real
open MeasureTheory Filter

/-!
## Local oscillation on an exhaustion implies a global wedge after rotation
-/

/-- **Core local-to-global wedge lemma**.

Assume the essential oscillation of `w` on the symmetric intervals `[-(n+1), (n+1)]`
is bounded by `D`. Then there exists a constant `c` (corresponding to a unimodular rotation)
such that `|w(t) - c| ≤ D` almost everywhere on `ℝ`. -/
theorem exists_shift_ae_abs_sub_le_of_oscOn_Icc_exhaustion
    {w : ℝ → ℝ} {D : ℝ}
    (hupper : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) (ae volume) w)
    (hlower : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) (ae volume) w)
    (hosc : ∀ n : ℕ, oscOn w (Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ)) ≤ D) :
    ∃ c : ℝ, ∀ᵐ t ∂volume, |w t - c| ≤ D := by
  classical
  -- Base interval `[-1,1]`.
  let I0 : Set ℝ := Set.Icc (- (1 : ℝ)) (1 : ℝ)
  let μ0 : Measure ℝ := volume.restrict I0

  have hμ0 : μ0 ≠ 0 := by
    -- `μ0 univ = volume I0 = 2`.
    have hU : μ0 Set.univ = (2 : ENNReal) := by
      simp [μ0, I0, Real.volume_Icc]
      norm_num
    have : μ0 Set.univ ≠ 0 := by
      simp [hU]
    exact (Measure.measure_univ_ne_zero).1 this

  -- `ae μ0` is nontrivial since `μ0 ≠ 0`. This is needed for coboundedness lemmas.
  haveI : NeBot (ae μ0) := (ae_neBot.2 hμ0)

  let a0 : ℝ := essInf w μ0
  let b0 : ℝ := essSup w μ0

  -- Boundedness on the restricted measure `μ0`, inherited from the global phase boundedness.
  have hupper0 : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) (ae μ0) w := by
    rcases hupper with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    -- `μ0 ≪ volume`, so a.e. under `volume` implies a.e. under `μ0`.
    have hle : ae μ0 ≤ ae volume :=
      (Measure.ae_le_iff_absolutelyContinuous).2 (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    exact hB.filter_mono hle
  have hlower0 : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) (ae μ0) w := by
    rcases hlower with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    have hle : ae μ0 ≤ ae volume :=
      (Measure.ae_le_iff_absolutelyContinuous).2 (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    exact hB.filter_mono hle

  have hab : a0 ≤ b0 :=
    essInf_le_essSup_of_neZero (w := w) (μ := μ0) hμ0 hupper0 hlower0

  -- Choose the "rotation" constant as the midpoint of `[a0,b0]`.
  let c : ℝ := (a0 + b0) / 2
  refine ⟨c, ?_⟩

  -- Step 1: show the bound on each restricted measure `volume.restrict [-N,N]`.
  have h_on : ∀ n : ℕ,
      (∀ᵐ t ∂volume.restrict (Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ)), |w t - c| ≤ D) := by
    intro n
    let In : Set ℝ := Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ)
    let μn : Measure ℝ := volume.restrict In

    -- Monotonicity of `essSup`/`essInf` from `I0 ⊆ In` (since `n.succ ≥ 1`).
    have hI0n : I0 ⊆ In := by
      intro x hx
      rcases hx with ⟨hxL, hxU⟩
      have hn : (1 : ℝ) ≤ (n.succ : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      constructor
      · -- `-(n.succ) ≤ x` from `-1 ≤ x` and `-(n.succ) ≤ -1`.
        have : (-(n.succ : ℝ)) ≤ -(1 : ℝ) := by nlinarith [hn]
        exact le_trans this hxL
      · exact le_trans hxU hn

    -- First, inherit boundedness/coboundedness for `w` on `μn` from the global bounds.
    have huppern : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) (ae μn) w := by
      rcases hupper with ⟨B, hB⟩
      refine ⟨B, ?_⟩
      have hle : ae μn ≤ ae volume :=
        (Measure.ae_le_iff_absolutelyContinuous).2 (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      exact hB.filter_mono hle
    have hlowern : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) (ae μn) w := by
      rcases hlower with ⟨B, hB⟩
      refine ⟨B, ?_⟩
      have hle : ae μn ≤ ae volume :=
        (Measure.ae_le_iff_absolutelyContinuous).2 (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      exact hB.filter_mono hle

    have hAE : ae μ0 ≤ ae μn := by
      have hleμ : μ0 ≤ μn := Measure.restrict_mono hI0n le_rfl
      have hac : μ0 ≪ μn := Measure.absolutelyContinuous_of_le hleμ
      exact (Measure.ae_le_iff_absolutelyContinuous).2 hac

    -- `b0 ≤ essSup w μn` from monotonicity of `limsup` along `ae` filters.
    have hb0_le : b0 ≤ essSup w μn := by
      -- `essSup` is `limsup` along `ae`.
      -- Apply `limsup_le_limsup_of_le` with bounds inherited from boundedness on `μn`/`μ0`.
      have hCobdd0 : (ae μ0).IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) w :=
        hlower0.isCoboundedUnder_le
      have hBddn : (ae μn).IsBoundedUnder (fun x1 x2 => x1 ≤ x2) w :=
        huppern
      simpa [b0, essSup] using (limsup_le_limsup_of_le (h := hAE) (u := w) hCobdd0 hBddn)

    -- `essInf w μn ≤ a0` from monotonicity of `liminf` along `ae` filters.
    have ha_le : essInf w μn ≤ a0 := by
      have hBddn : (ae μn).IsBoundedUnder (fun x1 x2 => x1 ≥ x2) w :=
        hlowern
      have hCobdd0 : (ae μ0).IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) w :=
        hupper0.isCoboundedUnder_ge
      -- With `hAE : ae μ0 ≤ ae μn`, we have `liminf w (ae μn) ≤ liminf w (ae μ0)`.
      simpa [a0, essInf] using
        (liminf_le_liminf_of_le (h := hAE) (u := w) hBddn hCobdd0)

    have hc_lower : essInf w μn ≤ c := by
      have : a0 ≤ c := by
        dsimp [c]
        nlinarith [hab]
      exact le_trans ha_le this
    have hc_upper : c ≤ essSup w μn := by
      have : c ≤ b0 := by
        dsimp [c]
        nlinarith [hab]
      exact le_trans this hb0_le

    -- For a.e. `t` in `In`, we have `essInf ≤ w t ≤ essSup`.
    have hlow : ∀ᵐ t ∂μn, essInf w μn ≤ w t :=
      ae_essInf_le (μ := μn) (f := w) hlowern
    have hupp : ∀ᵐ t ∂μn, w t ≤ essSup w μn :=
      ae_le_essSup (μ := μn) (f := w) huppern

    -- Now bound the distance to `c` by the diameter `essSup-essInf ≤ D`.
    have hdiam : essSup w μn - essInf w μn ≤ D := by
      simpa [oscOn, μn, In] using (hosc n)

    filter_upwards [hlow, hupp] with t htL htU
    have h1 : w t - c ≤ essSup w μn - essInf w μn := by
      nlinarith [htU, hc_lower]
    have h2 : c - w t ≤ essSup w μn - essInf w μn := by
      nlinarith [htL, hc_upper]
    have habs : |w t - c| ≤ essSup w μn - essInf w μn :=
      (abs_sub_le_iff.2 ⟨h1, h2⟩)
    exact le_trans habs hdiam

  -- Step 2: upgrade from each restricted interval to all of `ℝ` by countable union.
  have hbad0 :
      volume {t : ℝ | ¬ |w t - c| ≤ D} = 0 := by
    -- Let `Bad = {t | ¬ |w t - c| ≤ D}`.
    let Bad : Set ℝ := {t : ℝ | ¬ |w t - c| ≤ D}
    have hbad : ∀ n : ℕ, volume (Bad ∩ Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ)) = 0 := by
      intro n
      let In : Set ℝ := Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ)
      -- Turn the restricted a.e. statement into an a.e. implication on `volume`.
      have hn : ∀ᵐ t ∂volume, t ∈ In → |w t - c| ≤ D :=
        ae_imp_of_ae_restrict (μ := volume) (s := In) (p := fun t => |w t - c| ≤ D) (h_on n)
      -- Convert the implication to a measure-zero statement on `Bad ∩ In`.
      have : volume {t : ℝ | t ∈ In ∧ D < |w t - c|} = 0 := by
        -- `¬ (t ∈ In → P)` is `t ∈ In ∧ ¬P`, and `¬(|w-c| ≤ D)` is `D < |w-c|`.
        simpa [MeasureTheory.ae_iff, _root_.not_imp, not_le, and_left_comm, and_assoc, and_comm] using hn
      -- Rewrite `{t | t ∈ In ∧ D < |w-c|}` as `Bad ∩ In`.
      have hset : {t : ℝ | t ∈ In ∧ D < |w t - c|} = Bad ∩ In := by
        ext t
        simp [Bad, In, not_le, and_assoc, and_comm]
      have hBadIn : volume (Bad ∩ In) = 0 := by
        simpa [hset] using this
      simpa [In, Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using hBadIn
    have hBad_eq : Bad = ⋃ n : ℕ, Bad ∩ Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ) := by
      ext t; constructor
      · intro ht
        obtain ⟨N, hN⟩ := exists_nat_ge (|t|)
        refine Set.mem_iUnion.2 ?_
        refine ⟨N, ?_⟩
        have hN' : |t| ≤ (N.succ : ℝ) := le_trans hN (by exact_mod_cast (Nat.le_succ N))
        refine ⟨ht, (abs_le.mp hN')⟩
      · intro ht
        rcases Set.mem_iUnion.1 ht with ⟨n, hn⟩
        exact hn.1
    -- measure of the union is zero.
    have hUnion : volume (⋃ n : ℕ, Bad ∩ Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ)) = 0 :=
      measure_iUnion_null hbad
    have hBad : volume Bad = 0 := by
      -- Avoid `simp` rewriting `Bad` recursively (since `hBad_eq` has `Bad` on both sides).
      have hvol_eq : volume Bad = volume (⋃ n : ℕ, Bad ∩ Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ)) := by
        simpa using congrArg (fun s : Set ℝ => volume s) hBad_eq
      simpa [hvol_eq] using hUnion
    simpa [Bad] using hBad

  -- Convert the measure statement to an `ae` statement.
  simpa [MeasureTheory.ae_iff] using hbad0

/-- A paper-friendly wrapper: if the oscillation on *all centered intervals* is bounded by `D`,
then (after rotation) `|w-c| ≤ D` almost everywhere. -/
theorem exists_shift_ae_abs_sub_le_of_forall_centered_oscOn
    {w : ℝ → ℝ} {D : ℝ}
    (hupper : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) (ae volume) w)
    (hlower : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) (ae volume) w)
    (hosc : ∀ L : ℝ, 0 < L → oscOn w (Set.Icc (-L) L) ≤ D) :
    ∃ c : ℝ, ∀ᵐ t ∂volume, |w t - c| ≤ D := by
  -- Apply the exhaustion lemma with `L = n+1`.
  refine exists_shift_ae_abs_sub_le_of_oscOn_Icc_exhaustion (w := w) (D := D) hupper hlower ?_
  intro n
  simpa using (hosc (n.succ : ℝ) (by exact_mod_cast (Nat.succ_pos n)))

/-- Specialization to the RH wedge parameter: if oscillation on centered intervals is bounded by
`π·Υ`, then after rotation we have the a.e. wedge `|w-c| ≤ π·Υ`. -/
theorem exists_shift_ae_abs_sub_le_pi_mul_of_forall_centered_oscOn
    {w : ℝ → ℝ} {Υ : ℝ}
    (hupper : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) (ae volume) w)
    (hlower : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) (ae volume) w)
    (hosc : ∀ L : ℝ, 0 < L → oscOn w (Set.Icc (-L) L) ≤ Real.pi * Υ) :
    ∃ c : ℝ, ∀ᵐ t ∂volume, |w t - c| ≤ Real.pi * Υ := by
  exact exists_shift_ae_abs_sub_le_of_forall_centered_oscOn (w := w) (D := Real.pi * Υ) hupper
    hlower hosc

end BRF
end RiemannRecognitionGeometry
