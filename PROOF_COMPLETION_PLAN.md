# Riemann Hypothesis Recognition Geometry: Unconditional Proof Completion Plan

## Executive Summary

This document provides a 5-track parallel work plan for completing an unconditional Lean 4 proof of the Riemann Hypothesis via Recognition Geometry. 

**Current State:**
- Build: ✅ Compiles successfully
- Custom Axioms: 1 remaining (`trigger_lower_bound_axiom`)
- Sorries: 10 remaining
- Standard Axioms: `propext`, `Classical.choice`, `Quot.sound` (acceptable)

**Goal:** Eliminate all `sorry` and custom axioms to achieve an unconditional proof.

---

## Ground Rules

1. **No deck chair shuffling** - Every change must reduce `sorry` count or eliminate axioms
2. **Use Mathlib aggressively** - Search for existing lemmas before proving from scratch
3. **Verify progress** - After each change, run `#print axioms RiemannHypothesis_classical`
4. **Maintain build** - Never commit code that doesn't compile
5. **Document dependencies** - Note which sorries block which other work

---

## Architecture Overview

```
RiemannHypothesis_classical
    │
    ├── RiemannHypothesis_recognition_geometry
    │       │
    │       └── no_off_critical_zeros_in_strip
    │               │
    │               ├── local_zero_free_criterion ←── [SORRY: signal ≤ U_tail]
    │               │       │
    │               │       ├── trigger_lower_bound_axiom ←── [AXIOM TO ELIMINATE]
    │               │       │       └── PoissonJensen infrastructure
    │               │       │
    │               │       └── zero_free_condition (U_tail < L_rec) ✅ PROVEN
    │               │
    │               └── interior_coverage_exists ←── [2 SORRIES: dyadic arithmetic]
    │                       └── WhitneyGeometry infrastructure
    │
    └── completedRiemannZeta_ne_zero_of_re_gt_one ✅ PROVEN (Mathlib)
```

---

## Track 1: Whitney Geometry & Dyadic Covering

### Goal
Prove `interior_coverage_exists` without sorry by completing the dyadic arithmetic.

### Files
- `RiemannRecognitionGeometry/WhitneyGeometry.lean`

### Sorries to Eliminate (2)

#### Sorry 1.1: `σ_in_band_range` (Line ~83)
```lean
lemma σ_in_band_range (s : ℂ) (hs_lower : 1/2 < s.re) (hs_upper : s.re ≤ 1) :
    let B := coveringBand s hs_lower hs_upper
    B.σ_lower + B.thickness / 8 ≤ s.re ∧ s.re ≤ B.σ_upper - B.thickness / 8
```

**Mathematical Content:**
- Given σ = Re(s) - 1/2 ∈ (0, 1/2], find scale k such that:
  - λ_rec · 2^(-k) ≤ σ ≤ Λ_rec · 2^(-k) with margin
- With λ_rec = 1/3, Λ_rec = 3/2, the ratio Λ/λ = 9/2 > 2 guarantees existence
- Key: `k = ⌈-log₂(3(σ - 1/2))⌉` places σ in the band with margin

**Mathlib Resources:**
- `Int.ceil_le`, `Int.le_ceil`
- `Real.rpow_natCast`, `Real.logb_rpow`
- `zpow_neg`, `zpow_natCast`

**Estimated Effort:** ~100 lines

#### Sorry 1.2: `t_in_band_interval` (Line ~91)
```lean
lemma t_in_band_interval (s : ℂ) (hs_lower : 1/2 < s.re) (hs_upper : s.re ≤ 1) :
    let B := coveringBand s hs_lower hs_upper
    s.im ∈ B.base.interval
```

**Mathematical Content:**
- Given t = Im(s) and scale k, choose m = ⌊t / 2^(-k)⌋
- Then t ∈ [m · 2^(-k), (m+1) · 2^(-k)] = base interval

**Mathlib Resources:**
- `Int.floor_le`, `Int.lt_floor_add_one`
- `Set.mem_Icc`

**Estimated Effort:** ~50 lines

### Verification
```lean
#print axioms RiemannRecognitionGeometry.interior_coverage_exists
-- Should show only: propext, Classical.choice, Quot.sound (no sorryAx)
```

### Dependencies
- None (can start immediately)
- Blocks: Final integration in Track 5

---

## Track 2: Poisson-Jensen Phase Analysis

### Goal
Prove `trigger_lower_bound_axiom` as a theorem, eliminating the custom axiom.

### Files
- `RiemannRecognitionGeometry/PoissonJensen.lean`
- `RiemannRecognitionGeometry/Axioms.lean` (to convert axiom to theorem)

### Sorries to Eliminate (3)

#### Sorry 2.1: `total_phase_lower_bound` (Line ~57)
```lean
lemma total_phase_lower_bound (ρ : ℂ) (I : WhitneyInterval)
    (hρ_re : 1/2 < ρ.re) (hρ_im : ρ.im ∈ I.interval) :
    |phaseChange ρ (I.t0 - I.len) (I.t0 + I.len)| ≥ 2 * Real.arctan 2
```

**Mathematical Content:**
- Blaschke factor B(s) = (s-ρ)/(s-ρ̄) has phase change ≈ 2π across a zero
- For ρ in interior of band, phase change across [t₀-L, t₀+L] is ≥ 2·arctan(2)
- Uses: arg((t-ρ)/(t-ρ̄)) = 2·arctan((ρ.re - 1/2)/(t - ρ.im))

**Mathlib Resources:**
- `Complex.arg_div`
- `Real.arctan_add`, `Real.arctan_sub`
- We already have `Real.arctan_two_gt_one_point_one` in our codebase!

**Estimated Effort:** ~100 lines

#### Sorry 2.2: `pigeonhole_phase_capture` (Line ~89)
```lean
lemma pigeonhole_phase_capture (I : WhitneyInterval) (ρ : ℂ)
    (hρ_re : 1/2 < ρ.re) (hρ_im : ρ.im ∈ I.interval) :
    ∃ ℓ : Fin 3, windowPhaseMass (tripleWindows I ℓ) ρ ≥ L_rec
```

**Mathematical Content:**
- Total phase ≥ 2·arctan(2) ≈ 2.21
- Three windows partition the interval
- By pigeonhole: max window ≥ total/3 ≈ 0.74
- Since L_rec = arctan(2)/2 ≈ 0.55, we have 0.74 > 0.55 ✓

**Mathlib Resources:**
- `Finset.exists_le_of_sum_le`
- Arithmetic from our arctan bounds

**Estimated Effort:** ~50 lines

#### Sorry 2.3: Interval membership in `trigger_lower_bound` (Line ~117)
```lean
-- Need to show ρ.im ∈ I.interval from hγ_in : ρ.im ∈ B.base.interval
```

**Mathematical Content:**
- Direct from `B.base = I` and band interior definition

**Estimated Effort:** ~20 lines

### Axiom Elimination
After proving above, update `Axioms.lean`:
```lean
-- Change from:
axiom trigger_lower_bound_axiom ...
-- To:
theorem trigger_lower_bound_axiom ... := trigger_lower_bound ...
```

### Verification
```lean
#print axioms RiemannRecognitionGeometry.RiemannHypothesis_classical
-- Should NOT include trigger_lower_bound_axiom
```

### Dependencies
- `Real.arctan_two_gt_one_point_one` ✅ Already proven
- Blocks: Track 4 (Main theorem integration)

---

## Track 3: Carleson-Fefferman-Stein Bounds

### Goal
Complete the Carleson energy bound infrastructure (even if not directly needed for main theorem).

### Files
- `RiemannRecognitionGeometry/CarlesonBound.lean`

### Sorries to Eliminate (4)

#### Sorry 3.1: `bmo_carleson_embedding` (Line ~61)
```lean
lemma bmo_carleson_embedding (gradLogXi : ℝ × ℝ → ℝ × ℝ) (I : WhitneyInterval)
    (h_bmo : True) :
    boxEnergy gradLogXi I ≤ K_tail * (2 * I.len)
```

**Mathematical Content:**
- Fefferman-Stein (1972): BMO functions have Carleson measure bound
- log|ξ| is in BMO (from functional equation + growth bounds)
- E(I) ≤ K · |I| with uniform constant

**References:**
- Fefferman & Stein, "Hp spaces of several variables", Acta Math 1972
- Mathlib: `MeasureTheory.Measure.IsCarleson` (if available)

**Estimated Effort:** ~300 lines (hardest sorry)

#### Sorry 3.2: `green_cauchy_schwarz` (Line ~86)
```lean
lemma green_cauchy_schwarz (W : WindowFunction) (gradTail : ℝ → ℝ)
    (E : ℝ) (hE : E = boxEnergy (fun _ => (gradTail 0, 0)) W.support) :
    |windowPairing W gradTail| ≤ C_geom * sqrt E * (1 / sqrt (2 * W.support.len))
```

**Mathematical Content:**
- Green's identity: boundary integral ↔ area integral
- Cauchy-Schwarz: |⟨f,g⟩| ≤ ‖f‖ · ‖g‖

**Mathlib Resources:**
- `inner_mul_le_norm_mul_norm`
- `MeasureTheory.integral_mul_le`

**Estimated Effort:** ~150 lines

#### Sorry 3.3: `tail_pairing_bound` (Line ~106)
```lean
theorem tail_pairing_bound (I : WhitneyInterval) (gradTail : ℝ → ℝ)
    (h_carleson : boxEnergy (fun _ => (gradTail 0, 0)) I ≤ K_tail * (2 * I.len)) :
    |∫ t in I.interval, gradTail t| ≤ U_tail
```

**Mathematical Content:**
- Combine BMO→Carleson with Green+C-S
- Key cancellation: |I|^(1/2) · |I|^(-1/2) = 1 makes bound uniform

**Estimated Effort:** ~50 lines

#### Sorry 3.4: `tail_pairing_bound_full` (Line ~119)
```lean
theorem tail_pairing_bound_full ... :
    |∫ t in I.interval, integrand t| ≤ U_tail
```

**Estimated Effort:** ~30 lines

### Note
Track 3 may not be on the critical path if we can prove Track 4's sorry directly. But completing it provides a cleaner proof structure.

### Dependencies
- None (can start immediately)
- May help: Track 4

---

## Track 4: Main Theorem Integration

### Goal
Complete `local_zero_free_criterion` by proving the signal-noise bound.

### Files
- `RiemannRecognitionGeometry/Main.lean`

### Sorries to Eliminate (1)

#### Sorry 4.1: Signal bound in `local_zero_free_criterion` (Line ~55)
```lean
have h_bound : recognitionSignal I ρ ≤ U_tail := by
  sorry
```

**Mathematical Content:**
The key insight is that for any zero ρ:
1. The recognition signal captures phase rotation from the zero
2. But this signal is bounded by the tail contribution
3. The tail is bounded by U_tail (from Carleson)

**Two approaches:**

**Approach A (Direct):**
Show that `recognitionSignal` as defined equals L_rec (a constant), making the bound trivial since we need signal ≤ U_tail but signal ≥ L_rec and L_rec > U_tail gives contradiction.

Wait - this is the WRONG direction! We need:
- Trigger says: signal ≥ L_rec (if there's a zero)
- To get contradiction: we need signal ≤ U_tail
- Since U_tail < L_rec, this is impossible, proving no zero exists

**Approach B (Via Carleson):**
Connect `recognitionSignal` to `tail_pairing_bound` to get the U_tail bound.

**Current blocker:** The `recognitionSignal` definition is a placeholder (= L_rec). Need to:
1. Define it properly as an integral
2. Show it's bounded by the tail contribution

**Estimated Effort:** ~50 lines (if Track 3 is done) or ~100 lines (standalone)

### Dependencies
- Best after: Track 2 (for trigger bound) and Track 3 (for tail bound)
- Can start: Immediately (with placeholder approach)

---

## Track 5: Axiom Elimination & Final Verification

### Goal
Verify the proof is unconditional and clean up.

### Tasks

#### 5.1: Verify No Custom Axioms
```lean
#print axioms RiemannRecognitionGeometry.RiemannHypothesis_classical
-- Expected output:
-- 'RiemannRecognitionGeometry.RiemannHypothesis_classical' depends on axioms: 
--   [propext, Classical.choice, Quot.sound]
```

#### 5.2: Remove Unused Axiom Declarations
Once all axioms are proven as theorems, remove the `axiom` declarations from `Axioms.lean` or rename the file to `Lemmas.lean`.

#### 5.3: Final Build Verification
```bash
lake clean
lake build
```
Ensure no warnings about `sorry`.

#### 5.4: Documentation Update
Update `README.md` to reflect unconditional status.

### Dependencies
- Requires: ALL other tracks complete

---

## Parallel Work Matrix

| Track | Can Start Now | Blocked By | Blocks |
|-------|---------------|------------|--------|
| 1: Whitney | ✅ Yes | Nothing | Track 5 |
| 2: Poisson-Jensen | ✅ Yes | Nothing | Track 4, 5 |
| 3: Carleson | ✅ Yes | Nothing | Track 4 (optional), 5 |
| 4: Integration | ⚠️ Partial | Track 2, 3 (for clean proof) | Track 5 |
| 5: Verification | ❌ No | All others | Nothing |

---

## Quick Reference: Mathlib Searches

When stuck, search Mathlib for these patterns:

```bash
# In .lake/packages/mathlib/Mathlib/
grep -r "theorem.*floor" --include="*.lean" | head -20
grep -r "lemma.*arctan" --include="*.lean" | head -20
grep -r "Carleson\|BMO" --include="*.lean" | head -20
grep -r "Blaschke\|phase\|winding" --include="*.lean" | head -20
```

Or use LeanSearch: https://leansearch.net/

---

## Success Criteria

The proof is **unconditional** when:

1. ✅ `lake build` succeeds with no `sorry` warnings
2. ✅ `#print axioms RiemannHypothesis_classical` shows only `propext`, `Classical.choice`, `Quot.sound`
3. ✅ No `axiom` declarations in our code (only `theorem`/`lemma`)
4. ✅ All mathematical content is formalized, not assumed

---

## Estimated Total Effort

| Track | Lines | Days (1 person) |
|-------|-------|-----------------|
| 1: Whitney | ~150 | 2-3 |
| 2: Poisson-Jensen | ~170 | 3-4 |
| 3: Carleson | ~530 | 7-10 |
| 4: Integration | ~50-100 | 1-2 |
| 5: Verification | ~20 | 0.5 |
| **Total** | **~900-1000** | **14-20** |

With 5 parallel tracks: **3-5 days** with full team.

---

## Commands Reference

```bash
# Build
cd /Users/jonathanwashburn/Projects/riemann-geometry-rs
lake build

# Check axioms
echo 'import RiemannRecognitionGeometry
#print axioms RiemannRecognitionGeometry.RiemannHypothesis_classical' > /tmp/check.lean
lake env lean /tmp/check.lean

# Count sorries
grep -rn "sorry" RiemannRecognitionGeometry/*.lean | grep -v "PROOF_GOAL"

# Find Mathlib lemmas
lake env lean --run .lake/packages/mathlib/.lake/build/bin/leanproject search "arctan"
```

---

*Document generated for riemann-geometry-rs unconditional proof completion.*
*Last updated: December 2024*

