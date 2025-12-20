import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RiemannRecognitionGeometry.FeffermanStein

noncomputable section

open Real MeasureTheory

namespace RiemannRecognitionGeometry

/-!
## Sanity: affine functions are not in (global) BMO

This file is a **sanity tool** for debugging `OscillationTarget`.

It proves a basic fact: an affine function with nonzero slope has unbounded mean oscillation
over longer and longer intervals, hence cannot satisfy `InBMOWithBound`.

This is the exact kind of lemma we want whenever the boundary datum carries an
unremoved **linear drift** term: if some candidate `f` satisfies
`f = (nonzero slope affine) + (bounded remainder)`, then `f` cannot be in global BMO,
so any global-BMO `OscillationTarget` phrased in terms of `f` is automatically false.
-/

namespace BMOSanity

open scoped Interval

/-!
### Strategy note

We only need a **very coarse** lower bound of the form

`meanOscillation (fun t => t) (-L) L ≥ c * L`

for some fixed `c > 0` and all `L > 0`, to conclude that `t ↦ t` is not in global BMO.

To keep the proof robust and low-tech, we:
- compute the average of `t` on `[-L,L]` using `intervalIntegral` + FTC,
- lower bound `∫_{-L}^L |t|` by restricting to `[L/2, L]` where `|t| ≥ L/2`,
- avoid any delicate “measure monotonicity” API by doing the restriction via `setIntegral_mono_on`.
-/

/-! ### A concrete lower bound for mean oscillation of `t ↦ t` on symmetric intervals -/

lemma intervalAverage_id_symm (L : ℝ) (hL : 0 < L) :
    intervalAverage (fun t : ℝ => t) (-L) L = 0 := by
  -- `intervalAverage` is `(1/(b-a)) * ∫_{Icc a b} f`.
  -- For `f(t)=t` on `[-L,L]` the integral is 0, hence the average is 0.
  unfold intervalAverage
  have hlt : (-L : ℝ) < L := by linarith
  simp [hlt]
  -- Reduce the set integral over `Icc` to an interval integral over `(-L)..L`,
  -- and compute it via the fundamental theorem of calculus.
  -- We use `F(t)=t^2/2` with derivative `t`.
  have hIcc_to_interval :
      (∫ t in Set.Icc (-L) L, (fun t : ℝ => t) t) =
        (∫ t in (-L)..L, (fun t : ℝ => t) t) := by
    -- `∫_{-L..L}` is the set integral over `Ioc (-L) L`, and `Ioc`/`Icc` differ by endpoints only.
    have hle : (-L : ℝ) ≤ L := by linarith
    -- Interval integral → set integral on `Ioc`.
    have h_interval : (∫ t in (-L)..L, (fun t : ℝ => t) t) = ∫ t in Set.Ioc (-L) L, t := by
      simpa [intervalIntegral.integral_of_le hle]
    -- Swap `Ioc` to `Icc` (Lebesgue has no atoms).
    have h_Icc_Ioc : (∫ t in Set.Icc (-L) L, t) = ∫ t in Set.Ioc (-L) L, t := by
      simpa using (MeasureTheory.integral_Icc_eq_integral_Ioc (μ := (volume : Measure ℝ))
        (f := fun t : ℝ => t) (x := -L) (y := L))
    -- Combine.
    -- `∫_{Icc} = ∫_{Ioc} = intervalIntegral`.
    calc
      (∫ t in Set.Icc (-L) L, t) = ∫ t in Set.Ioc (-L) L, t := h_Icc_Ioc
      _ = (∫ t in (-L)..L, (fun t : ℝ => t) t) := by
        simpa using h_interval.symm
  -- Compute the interval integral.
  have hFTC :
      (∫ t in (-L)..L, (fun t : ℝ => t) t) = ((L ^ 2) / 2 - ((-L) ^ 2) / 2) := by
    -- `HasDerivAt` for `t ↦ t^2/2` is `t`.
    have hderiv :
        ∀ t ∈ Set.uIcc (-L) L,
          HasDerivAt (fun u : ℝ => (u ^ 2) / 2) (t) t := by
      intro t _
      -- derivative of `u^2 / 2` is `u`
      -- `d/dt (t^2/2) = t`.
      have : HasDerivAt (fun u : ℝ => (u ^ 2) / 2) ((2 * t) / 2) t := by
        -- derivative of `u^2` is `2u`, then scale by `1/2`
        simpa [div_eq_mul_inv, mul_assoc] using (hasDerivAt_pow 2 t).mul_const (1 / 2 : ℝ)
      -- simplify `(2*t)/2 = t`
      simpa using this.congr_deriv (by ring)
    -- integrability is automatic for continuous functions on compact intervals.
    have hint : IntervalIntegrable (fun t : ℝ => t) volume (-L) L := by
      simpa using (intervalIntegrable_id : IntervalIntegrable (fun t : ℝ => t) volume (-L) L)
    -- Apply FTC lemma.
    -- `integral_eq_sub_of_hasDerivAt` gives `∫ f' = F(b) - F(a)`.
    -- FTC for interval integrals.
    simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint)
  -- Finish: the integral is 0 by symmetry of squares.
  have hInt : (∫ t in Set.Icc (-L) L, (fun t : ℝ => t) t) = 0 := by
    have : (∫ t in (-L)..L, (fun t : ℝ => t) t) = 0 := by
      -- `(-L)^2 = L^2`
      have hsq : ((-L) ^ 2 : ℝ) = L ^ 2 := by
        simp
      -- simplify `((L^2)/2 - ((-L)^2)/2)`
      simpa [hFTC, hsq] using (show ((L ^ 2) / 2 - ((-L) ^ 2) / 2) = (0:ℝ) by ring)
    simpa [hIcc_to_interval] using this
  -- Plug back into the average formula: `(1/(2L))*0 = 0`.
  have hden : (L - (-L)) ≠ 0 := by nlinarith [hL]
  simp [hInt, hden]

lemma meanOscillation_id_symm_lower (L : ℝ) (hL : 0 < L) :
    (L / 8) ≤ meanOscillation (fun t : ℝ => t) (-L) L := by
  -- Unfold mean oscillation and plug in the computed average.
  unfold meanOscillation
  have hlt : (-L : ℝ) < L := by linarith
  simp [hlt]
  -- Replace `intervalAverage` by 0.
  have havg : intervalAverage (fun t : ℝ => t) (-L) L = 0 :=
    intervalAverage_id_symm L hL
  simp [havg]
  -- We lower bound `∫_{-L}^L |t|` by restricting to `[L/2, L]` where `|t| = t ≥ L/2`.
  -- Then `∫_{L/2}^L |t| ≥ (L/2) * (L/2) = L^2/4`.
  have hsubset : Set.Icc (L / 2) L ⊆ Set.Icc (-L) L := by
    intro t ht
    refine ⟨?_, ht.2⟩
    have : (-L : ℝ) ≤ L / 2 := by linarith
    exact this.trans ht.1
  have hnonneg : ∀ t ∈ Set.Icc (L / 2) L, (0 : ℝ) ≤ |t| := by
    intro t _; exact abs_nonneg t
  -- Use monotonicity of integrals of nonnegative functions under set inclusion.
  have h_int_mono :
      (∫ t in Set.Icc (L / 2) L, |t|) ≤ ∫ t in Set.Icc (-L) L, |t| := by
    have hInt_big : IntegrableOn (fun t : ℝ => |t|) (Set.Icc (-L) L) volume := by
      -- `|t|` is continuous, hence integrable on compact intervals.
      exact (continuous_abs.continuousOn.integrableOn_compact isCompact_Icc)
    -- Apply `setIntegral_mono_set` (monotonicity in the domain for nonnegative integrands).
    refine MeasureTheory.setIntegral_mono_set (μ := (volume : Measure ℝ))
      (s := Set.Icc (L / 2) L) (t := Set.Icc (-L) L) (f := fun t : ℝ => |t|)
      (hfi := hInt_big) (hf := ?_) (hst := ?_)
    · -- nonneg a.e. on the larger set
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2
        (Filter.Eventually.of_forall (fun t ht => abs_nonneg t))
    · -- subset a.e. (in fact pointwise)
      refine Filter.Eventually.of_forall ?_
      intro t ht
      exact hsubset ht
  -- Lower bound the small integral by a constant.
  have h_lower_small :
      (L ^ 2) / 4 ≤ ∫ t in Set.Icc (L / 2) L, |t| := by
    -- On `[L/2, L]`, we have `|t| = t ≥ L/2`.
    have hpoint : ∀ t ∈ Set.Icc (L / 2) L, (L / 2 : ℝ) ≤ |t| := by
      intro t ht
      have ht_nonneg : 0 ≤ t := by linarith [ht.1]
      have : |t| = t := abs_of_nonneg ht_nonneg
      simpa [this] using ht.1
    -- Compare integral with the constant function `L/2`.
    have hInt_const : IntegrableOn (fun _ : ℝ => (L / 2 : ℝ)) (Set.Icc (L / 2) L) volume := by
      rw [integrableOn_const]; right
      simp [Real.volume_Icc, hL.ne']
    have hInt_abs : IntegrableOn (fun t : ℝ => |t|) (Set.Icc (L / 2) L) volume := by
      exact (continuous_abs.continuousOn.integrableOn_compact isCompact_Icc)
    have hmono := MeasureTheory.setIntegral_mono_on hInt_const hInt_abs measurableSet_Icc hpoint
    -- Compute the integral of the constant.
    have hconst_val :
        (∫ t in Set.Icc (L / 2) L, (L / 2 : ℝ)) = (L ^ 2) / 4 := by
      -- `∫ const = const * volume`, and `volume (Icc (L/2) L) = L/2`.
      have hlen : (L - L / 2 : ℝ) = L / 2 := by ring
      have hL2_nonneg : 0 ≤ (L / 2 : ℝ) := by nlinarith [le_of_lt hL]
      -- Now compute the constant integral explicitly.
      -- `∫_{Icc a b} c = c * (b-a)` for Lebesgue measure.
      have h_toReal :
          (ENNReal.ofReal (L - L / 2)).toReal = (L / 2 : ℝ) := by
        -- `toReal (ofReal x) = x` when `x ≥ 0`.
        have hx0 : 0 ≤ (L - L / 2 : ℝ) := by
          -- since `L > 0`, `L - L/2 = L/2 ≥ 0`
          simpa [hlen] using hL2_nonneg
        have : (ENNReal.ofReal (L - L / 2)).toReal = (L - L / 2 : ℝ) := by
          simpa using (ENNReal.toReal_ofReal hx0)
        simpa [hlen] using this
      -- `volume (Icc (L/2) L) = ofReal (L - L/2)`.
      -- Reduce to `L/2 * (L/2) = L^2/4`.
      simp [MeasureTheory.setIntegral_const, Real.volume_Icc, hL.le, h_toReal, hlen,
        ENNReal.toReal_ofReal hL2_nonneg]
      ring
    -- Rearrange.
    simpa [hconst_val] using hmono
  -- Put the bounds together.
  have h_big : (L ^ 2) / 4 ≤ ∫ t in Set.Icc (-L) L, |t| :=
    le_trans h_lower_small h_int_mono
  -- Finally, divide by `2L` as in the mean oscillation definition.
  have hden_pos : 0 < (L + L : ℝ) := by nlinarith [hL]
  -- `meanOscillation = (L+L)⁻¹ * ∫ |t|` after simplification.
  -- We show `(L/8) ≤ (L+L)⁻¹ * (L^2/4)` and then use `h_big`.
  have hcalc : (L / 8 : ℝ) ≤ (L + L)⁻¹ * ((L ^ 2) / 4) := by
    have hLne : L ≠ 0 := ne_of_gt hL
    have hden_ne : (L + L : ℝ) ≠ 0 := by nlinarith [hLne]
    have heq : (L + L)⁻¹ * ((L ^ 2) / 4) = (L / 8) := by
      -- clear denominators
      field_simp [hden_ne, hLne]
      ring
    exact le_of_eq heq.symm
  have hmul_nonneg : 0 ≤ ((L + L)⁻¹ : ℝ) := by
    exact inv_nonneg.mpr (le_of_lt hden_pos)
  -- Conclude.
  calc
    (L / 8 : ℝ) ≤ (L + L)⁻¹ * ((L ^ 2) / 4) := hcalc
    _ ≤ (L + L)⁻¹ * (∫ t in Set.Icc (-L) L, |t|) := by
      exact mul_le_mul_of_nonneg_left h_big hmul_nonneg

/-! ### Consequence: no global BMO bound for nonzero slope affine functions -/

theorem not_inBMOWithBound_id (M : ℝ) : ¬ InBMOWithBound (fun t : ℝ => t) M := by
  intro h
  -- Take `L := 9*M` (note `h.1 : 0 < M`).
  set L : ℝ := 9 * M
  have hL : 0 < L := by
    -- unfold the `set`-abbreviation for `L` for the arithmetic proof
    have : 0 < 9 * M := by nlinarith [h.1]
    simpa [L] using this
  have hMO : (L / 8) ≤ meanOscillation (fun t : ℝ => t) (-L) L :=
    meanOscillation_id_symm_lower L hL
  have hbound : meanOscillation (fun t : ℝ => t) (-L) L ≤ M := by
    -- Apply the BMO bound.
    have hlt : (-L : ℝ) < L := neg_lt_self hL
    exact h.2 (-L) L hlt
  -- But `L/8 = 9M/8 > M`.
  have hLt : M < L / 8 := by
    -- `L = 9M`
    simp [L]
    nlinarith [h.1]
  -- Contradiction.
  exact (not_lt_of_ge (le_trans hMO hbound) hLt)

/-!
### Scaling lemmas

These are tiny “algebra of our concrete BMO definition” facts.
They let us turn `InBMOWithBound (fun t => a*t) M` into a (false) BMO bound for `t ↦ t`
by scaling with `1/a`.
-/

lemma intervalAverage_mul_const (a : ℝ) (f : ℝ → ℝ) (x y : ℝ) :
    intervalAverage (fun t => a * f t) x y = a * intervalAverage f x y := by
  unfold intervalAverage
  by_cases hxy : x < y
  · simp [hxy, mul_assoc, MeasureTheory.integral_mul_left]
    ac_rfl
  · simp [hxy]

lemma meanOscillation_mul_const (a : ℝ) (f : ℝ → ℝ) (x y : ℝ) :
    meanOscillation (fun t => a * f t) x y = |a| * meanOscillation f x y := by
  unfold meanOscillation
  by_cases hxy : x < y
  · simp [hxy]
    -- Use the scaling of the interval average.
    have havg : intervalAverage (fun t => a * f t) x y = a * intervalAverage f x y :=
      intervalAverage_mul_const a f x y
    -- Rewrite the integrand, pull out `|a|`, and pull it out of the integral.
    -- `|a*f - a*avg| = |a|*|f-avg|`.
    have hpoint : (fun t => |a * f t - intervalAverage (fun t => a * f t) x y|) =
        fun t => |a| * |f t - intervalAverage f x y| := by
      funext t
      -- expand `havg` and use `abs_mul` + `mul_sub`.
      -- `a*f - a*avg = a*(f-avg)`.
      calc
        |a * f t - intervalAverage (fun t => a * f t) x y|
            = |a * f t - a * intervalAverage f x y| := by simpa [havg]
        _ = |a * (f t - intervalAverage f x y)| := by
              simpa [mul_sub]
        _ = |a| * |f t - intervalAverage f x y| := by
              simpa [abs_mul]
    -- Apply `integral_mul_left` to pull `|a|` out.
    simp [hpoint, MeasureTheory.integral_mul_left, mul_assoc, mul_left_comm, mul_comm]
  · simp [hxy]

/-! ### Corollary: nonzero-slope affine functions are not in global BMO -/

theorem not_inBMOWithBound_mul_id {a : ℝ} (ha : a ≠ 0) (M : ℝ) :
    ¬ InBMOWithBound (fun t : ℝ => a * t) M := by
  intro h
  -- Scale by `1/a` to get a BMO bound for `id`.
  have hid : InBMOWithBound (fun t : ℝ => t) (|1 / a| * M) := by
    refine ⟨?_, ?_⟩
    · have hpos : 0 < |1 / a| := abs_pos.mpr (one_div_ne_zero ha)
      exact mul_pos hpos h.1
    · intro x y hxy
      -- Apply the bound for `a*t` on `[x,y]`.
      have hMO := h.2 x y hxy
      -- Convert it to a bound for `t ↦ (1/a) * (a*t) = t` using `meanOscillation_mul_const`.
      have hScaled :
          meanOscillation (fun t : ℝ => (1 / a) * (a * t)) x y ≤ |1 / a| * M := by
        -- rewrite the LHS via the scaling lemma, then use `hMO`.
        have hEq :
            meanOscillation (fun t : ℝ => (1 / a) * (a * t)) x y =
              |1 / a| * meanOscillation (fun t : ℝ => a * t) x y := by
          simpa [mul_assoc] using (meanOscillation_mul_const (1 / a) (fun t : ℝ => a * t) x y)
        have hMul :
            |1 / a| * meanOscillation (fun t : ℝ => a * t) x y ≤ |1 / a| * M :=
          mul_le_mul_of_nonneg_left hMO (abs_nonneg (1 / a))
        exact (hEq ▸ hMul)
      -- Simplify `(1/a) * (a*t) = t` (Lean will often rewrite `1/a` as `a⁻¹`).
      have hScaled' :
          meanOscillation (fun t : ℝ => a⁻¹ * (a * t)) x y ≤ |a⁻¹| * M := by
        simpa [one_div] using hScaled
      have hfun : (fun t : ℝ => a⁻¹ * (a * t)) = fun t : ℝ => t := by
        funext t
        field_simp [ha]
      simpa [hfun] using hScaled'
  exact (not_inBMOWithBound_id (|1 / a| * M)) hid

end BMOSanity
end RiemannRecognitionGeometry
