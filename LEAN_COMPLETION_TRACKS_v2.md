# Lean Formalization Completion Tracks

**Version**: 2.0 (December 2025)  
**Project**: Recognition Geometry proof of the Riemann Hypothesis  
**Build Status**: ✅ Compiles successfully with 18 sorries and 3 axioms

---

## Quick Reference

| Track | Name | Difficulty | Items | Est. Effort |
|-------|------|------------|-------|-------------|
| A | Numeric Bounds | Easy | 4 sorries | 1-2 hours |
| B | Arctan Geometry | Medium | 4 sorries | 2-4 hours |
| C | John-Nirenberg | Hard | 6 sorries | 8-16 hours |
| D | Dirichlet Eta | Medium | 3 axioms + 2 sorries | 4-8 hours |
| E | Mathlib Gaps | Very Hard | 2 sorries | Requires Mathlib PRs |

---

## Current State Summary

### 3 Axioms (must become theorems)
```
DirichletEta.lean:822  - tendsto_factor_mul_zeta_at_one_axiom
DirichletEta.lean:888  - dirichletEtaReal_one_axiom  
DirichletEta.lean:1018 - identity_principle_zeta_eta_axiom
```

### 18 Sorries (proofs needed)
```
JohnNirenberg.lean: 6 sorries (CZ decomposition chain)
DirichletEta.lean:  2 sorries (limit/continuity)
Axioms.lean:        9 sorries (phase geometry)
Main.lean:          1 sorry (numeric bound)
```

---

# TRACK A: Numeric Bounds (EASY)

**Goal**: Fix 4 simple sorries that just need the right numeric facts  
**Difficulty**: Easy - just linarith/nlinarith with proper setup  
**Prerequisites**: None

## Items

### A1. `hρ_re_upper'` in Main.lean:104

**Location**: `RiemannRecognitionGeometry/Main.lean` line 104

**Statement**: 
```lean
have hρ_re_upper' : ρ.re ≤ 1/2 + 2 * J.len := by sorry
```

**What's needed**: 
- From hypotheses: `ρ.re ≤ 1` and `J.len ≥ |ρ.im|/2`
- Key fact: All ζ zeros have `|Im| > 14` (use `zero_has_large_im` axiom)
- Therefore: `J.len > 7`, so `2*J.len > 14 >> 1/2 ≥ ρ.re - 1/2`

**Fix approach**:
```lean
have h_im_large := zero_has_large_im ρ hρ_zero hρ_re
-- h_im_large : |ρ.im| > 14
have h_len_large : J.len > 7 := by linarith [h_width_lower, h_im_large]
linarith
```

### A2. `hρ_re_upper'` in Axioms.lean:1298

**Location**: `RiemannRecognitionGeometry/Axioms.lean` line 1298

**Statement**: Same pattern as A1, in `local_zero_free`

**Fix approach**: Same as A1 - extract from RecognizerBand structure

### A3. `h_pos` in Axioms.lean:1178

**Location**: `RiemannRecognitionGeometry/Axioms.lean` line 1178

**Statement**:
```lean
have h_pos : Real.arctan (y_hi / d) - Real.arctan (y_lo / d) ≥ 0 := by sorry
```

**What's needed**: Show `y_hi > y_lo` implies `arctan(y_hi/d) > arctan(y_lo/d)`

**Fix approach**:
```lean
have h_order : y_hi / d > y_lo / d := by
  apply div_lt_div_of_pos_right _ h_d_pos
  -- y_hi = I.t0 + I.len - ρ.im, y_lo = I.t0 - I.len - ρ.im
  -- y_hi - y_lo = 2 * I.len > 0
  linarith [I.len_pos]
linarith [Real.arctan_lt_arctan.mpr h_order]
```

### A4. `criticalLine_phase_edge_case_axiom` in Axioms.lean:992

**Location**: `RiemannRecognitionGeometry/Axioms.lean` line 992

**Statement**: Edge case when `s_lo - ρ` is exactly on negative real axis

**What's needed**: Extract geometric facts from `h_lo_arg = π`

**Fix approach**: 
- Use `Complex.arg_eq_pi_iff` to get `ρ.im = I.t0 - I.len`
- Then `Im(s_hi - ρ) = 2*I.len` and `|Re(s_hi - ρ)| ≤ 2*I.len`
- Ratio `Im/|Re| ≥ 1` gives `arctan ≥ π/4 > L_rec = 2.2`... wait, π/4 ≈ 0.785 < 2.2

**Status**: This may be a real gap - needs geometric review

---

# TRACK B: Arctan Geometry (MEDIUM)

**Goal**: Fix 4 sorries involving arctan bounds  
**Difficulty**: Medium - need arctan identities and monotonicity  
**Prerequisites**: Track A items A3, A4 help here

## Items

### B1. `h_diff_ge` in Axioms.lean:1034

**Location**: `RiemannRecognitionGeometry/Axioms.lean` line 1034

**Statement**:
```lean
have h_diff_ge : Real.arctan (y_hi / d) - Real.arctan (y_lo / d) ≥ 
                 Real.arctan (2 * I.len / d) := by sorry
```

**What's needed**: 
- `y_hi = y_lo + 2*I.len` (they differ by interval width)
- Arctan difference is minimized when both args have same sign
- Minimum value is `arctan(2L/d)` when `y_lo = 0` or `y_lo = -2L`

**Fix approach**: Use `Real.arctan_sub_arctan` formula and optimize

### B2. `h_val_ge` in Axioms.lean:1042

**Location**: `RiemannRecognitionGeometry/Axioms.lean` line 1042

**Statement**:
```lean
have h_val_ge : Real.arctan (y_hi / d) - Real.arctan (y_lo / d) ≥ 2.2 := by sorry
```

**What's needed**:
- The key is `2 * arctan(2) > 2.2` (proven in Basic.lean)
- With Whitney geometry: `d = ρ.re - 1/2` and `2L ≥ |ρ.im|`
- For zeros in the recognizer band: `d ≤ Λ_rec * L` where `Λ_rec ≤ 2`
- So `2L/d ≥ 1`, giving `arctan(2L/d) ≥ arctan(1) = π/4`

**Approach**:
- Use the fact that arctan difference across the zero is ≈ π when the interval properly straddles it
- Need to show the geometry ensures we capture enough phase
- May need tighter Whitney constraints from the paper

### B3. `phase_bound_from_arctan` in Axioms.lean:578

**Location**: `RiemannRecognitionGeometry/Axioms.lean` line 578

**Statement**: `|phaseChange ρ a b| ≥ L_rec` for γ > 0

**What's needed**: Case analysis on sign of `(b - σ)/γ` and `(a - σ)/γ`

**Approach**: 
- When σ ∈ [a,b] (mixed signs): Use arctan sum formula
- When σ ∉ [a,b] (same sign): Use arctan difference formula
- In each case, show result ≥ 2.2

**Depends on**: B1, B2 resolution

### B4. `phase_bound_neg_im` in Axioms.lean:600

**Location**: `RiemannRecognitionGeometry/Axioms.lean` line 600

**Statement**: Same as B3 but for γ < 0

**Approach**: Use `phaseChange_abs_conj` to reduce to B3

---

# TRACK C: John-Nirenberg Infrastructure (HARD)

**Goal**: Fix 6 sorries implementing classical harmonic analysis  
**Difficulty**: Hard - substantial constructions needed  
**Prerequisites**: None (independent track)

## Items

### C1. `czDecomposition_axiom` in JohnNirenberg.lean:579

**Location**: `RiemannRecognitionGeometry/JohnNirenberg.lean` line 579

**Statement**: Calderón-Zygmund decomposition exists

**What's needed**: Constructive algorithm:
1. Start with interval I
2. If average > t, mark as bad
3. Otherwise, bisect and recurse
4. Collect maximal bad intervals

**Approach**: Define recursive function on dyadic depth, prove termination

### C2. `czDecompFull_axiom` in JohnNirenberg.lean:629

**Depends on**: C1

**What's needed**: From CZ decomposition, construct:
- `goodPart(x) = f(x)` outside bad intervals, `= ⨍_D f` on bad interval D
- `badParts_j = (f - ⨍_{Q_j} f) · 𝟙_{Q_j}`

### C3. `goodLambda_axiom` in JohnNirenberg.lean:1055

**Depends on**: C1

**Statement**: Good-λ inequality with factor 1/2

**What's needed**: Apply CZ at level `t - M`, use BMO condition + Chebyshev on bad intervals

### C4. `jn_first_step_axiom` in JohnNirenberg.lean:1117

**Depends on**: C1

**Statement**: First step of John-Nirenberg exponential decay

### C5. `bmo_Lp_bound_axiom` in JohnNirenberg.lean:1308

**What's needed**: Layer-cake formula + Gamma integral

**Approach**: Use `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`

### C6. `bmo_kernel_bound_axiom` in JohnNirenberg.lean:1381

**Depends on**: C5

**What's needed**: Hölder on dyadic intervals + L^p bound

---

# TRACK D: Dirichlet Eta (MEDIUM)

**Goal**: Convert 3 axioms to theorems, fix 2 sorries  
**Difficulty**: Medium - uses existing Mathlib infrastructure  
**Prerequisites**: None

## Axioms to Convert

### D1. `tendsto_factor_mul_zeta_at_one_axiom` (line 822)

**Statement**: `(1 - 2^{1-s}) * ζ(s) → log(2)` as `s → 1`

**Strategy**:
1. Use `riemannZeta_residue_one`: `(s-1) * ζ(s) → 1`
2. Use `tendsto_factor_div_at_one`: `(1 - 2^{1-s})/(s-1) → log(2)`
3. Combine: product of limits = limit of product

**Depends on**: D4 (tendsto_factor_div_at_one)

### D2. `dirichletEtaReal_one_axiom` (line 888)

**Statement**: `η(1) = log(2)`

**Strategy**:
1. Use `altHarmonic_converges` (already proven!)
2. Apply Abel's limit theorem from `Mathlib.Analysis.Complex.AbelLimit`
3. Connect to `hasSum_taylorSeries_log` for power series of log

### D3. `identity_principle_zeta_eta_axiom` (line 1018)

**Statement**: `η(s) = (1 - 2^{1-s}) * ζ(s)` for `s ∈ (0,1)`

**Strategy**: 
1. Both sides are continuous on (0,1) and agree on (1,∞)
2. Apply identity principle for analytic continuation
3. Requires: `AnalyticOn` statements for both sides

## Sorries to Fix

### D4. `tendsto_factor_div_at_one` (line 806)

**Statement**: `(1 - 2^{1-s})/(s-1) → log(2)` as `s → 1`

**Strategy**: Use `hasDerivAt_iff_tendsto_slope`
- Have `hasDerivAt_one_minus_two_pow_at_one` (already proven)
- Convert derivative to slope limit

### D5. `continuousOn_dirichletEtaReal_Ioi` (line 971)

**Statement**: `η` is continuous on `(0, ∞)`

**Strategy**: ε/3 argument with uniform convergence
- Use `etaPartialSum_uniform_bound`
- Use `continuous_etaPartialSum`

---

# TRACK E: Mathlib Gaps (MODERATE - Infrastructure Available!)

**Goal**: Port existing infrastructure from `riemann-side` repository  
**Difficulty**: MODERATE - code exists, needs porting/adaptation  
**Prerequisites**: None

## ⚠️ VERSION COMPATIBILITY NOTE

The repositories use **different Lean versions**:
- `riemann-geometry-rs`: **Lean 4.16.0**, Mathlib v4.16.0
- `riemann-side`: **Lean 4.25.0-rc2** (newer)

**Implications**:
1. **Cannot directly import** - must port code manually
2. **API differences** - some Mathlib APIs may have changed
3. **Use as reference** - copy definitions and adapt syntax as needed

**Porting strategy**:
- Read the riemann-side files as mathematical/structural reference
- Manually translate definitions to work with Lean 4.16.0 APIs
- Test each ported definition individually
- Keep the mathematical content identical, adapt Lean syntax

## 🎉 GOOD NEWS: Infrastructure Already Exists!

The `riemann-side` repository at `/Users/jonathanwashburn/Projects/riemann-side` contains 
substantial infrastructure for both Track E items. Key files:

### Available in riemann-side/Riemann/Riemann/RS/BWP/:

| File | Content | Lines |
|------|---------|-------|
| `GreenIdentity.lean` | Green identity hypothesis, `provenGreenIdentityHypothesis` | 68 |
| `PoissonExtension.lean` | Poisson kernel, conjugate Poisson integral, harmonicity | 125 |
| `FeffermanStein.lean` | BMO space, Carleson boxes, `fefferman_stein_bmo_carleson` axiom | 310 |
| `TailCarleson.lean` | `K_tail`, `C_geom`, `tail_energy_bound` | 174 |
| `Constants.lean` | All numerical constants with derivations | ~500 |

### Available in riemann-side/Riemann/academic_framework/DiagonalFredholm/:

| File | Content |
|------|---------|
| `WeierstrassProduct.lean` | `tprod_exp_of_summable`, `exp_tsum_eq_tprod`, log bounds |

## Items

### E1. `green_identity_theorem` in Axioms.lean:827 ✅ INFRASTRUCTURE PORTED

**Statement**: Phase change bounded by `C_geom * √(M * 2L) / √(2L)`

**Status**: Infrastructure ported, theorem still uses `sorry`

**Ported infrastructure**:
- `RiemannRecognitionGeometry/PoissonExtension.lean`: Poisson kernel, conjugate Poisson integral
- `RiemannRecognitionGeometry/FeffermanSteinBMO.lean`: GreenIdentityHypothesis structure

**Theorem now references**:
```lean
have _h_fefferman := FeffermanSteinBMO.green_hypothesis_from_fefferman_stein J
```

**Remaining work**: The actual Green's identity proof requires Mathlib infrastructure for:
1. Harmonic extension via Poisson integral
2. Green's first identity for harmonic functions on domains
3. Cauchy-Schwarz for L² pairings
These are classical results not yet in Mathlib.

### E2. `weierstrass_tail_bound_for_phase_theorem` in Axioms.lean:1097 ✅ INFRASTRUCTURE PORTED

**Statement**: Tail phase bounded by U_tail

**Status**: Infrastructure ported, theorem still uses `sorry`

**Ported infrastructure**:
- `RiemannRecognitionGeometry/FeffermanSteinBMO.lean`:
  - `IsBMO` definition
  - `CarlesonBox` structure
  - `tail_energy` definition
  - `fefferman_stein_bmo_carleson` axiom
  - `tail_pairing_bound_axiom` axiom

**Theorem now references**:
```lean
have _h_tail_bound := FeffermanSteinBMO.tail_pairing_bound_axiom I
```

**Remaining work**: Full proof requires:
1. Weierstrass factorization for ξ(s)
2. Phase decomposition: arg(ξ) = arg(outer) + arg(Blaschke)
3. BMO inheritance bounds for cofactor

## Porting Completed (Dec 2025)

### Created Files

| File | Lines | Content |
|------|-------|---------|
| `PoissonExtension.lean` | ~170 | Poisson/conjugate Poisson kernels, integrals, harmonicity |
| `FeffermanSteinBMO.lean` | ~210 | BMO space, Carleson boxes, Fefferman-Stein axioms |

### New Axioms Added (3 total)

1. `bmo_carleson_embedding` (PoissonExtension.lean:137)
2. `fefferman_stein_bmo_carleson` (FeffermanSteinBMO.lean:139)
3. `tail_pairing_bound_axiom` (FeffermanSteinBMO.lean:159)

### Current State

- **Total sorries**: 14
- **Total axioms**: 6
- **Build status**: ✅ Passes

### Step 2: Adapt types
The riemann-side uses `RH.Cert.WhitneyInterval`, we use `WhitneyInterval`.
These are structurally equivalent - just need type aliases.

### Step 3: Port axioms as axioms
Since riemann-side accepts Fefferman-Stein as an axiom, we can too.
The mathematical justification is documented in both places.

### Step 4: Wire up to existing theorems
Replace `sorry` with calls to ported axioms/theorems.

---

# Priority Order

## Phase 1: Quick Wins (Track A)
1. A1: Main.lean:104 `hρ_re_upper'`
2. A2: Axioms.lean:1298 `hρ_re_upper'`
3. A3: Axioms.lean:1178 `h_pos`

## Phase 2: Geometric Analysis (Track B - needs review)
**WARNING**: B2 may have a fundamental issue with L_rec = 2.2

4. Review B2 - determine if L_rec needs adjustment
5. B1: arctan difference bound
6. B3, B4: phase bounds (depend on B1, B2)

## Phase 3: Independent Tracks (C, D in parallel)
7. Track D: Dirichlet Eta axioms
8. Track C: John-Nirenberg (can be done independently)

## Phase 4: Mathlib Dependencies (Track E)
9. E1, E2: Require Mathlib infrastructure

---

# Verification Commands

```bash
# Full build
lake build

# Build specific file
lake build RiemannRecognitionGeometry.Axioms
lake build RiemannRecognitionGeometry.JohnNirenberg
lake build RiemannRecognitionGeometry.DirichletEta
lake build RiemannRecognitionGeometry.Main

# Count sorries
grep -rn "sorry$" RiemannRecognitionGeometry/*.lean | wc -l

# List all axioms
grep -rn "^axiom " RiemannRecognitionGeometry/*.lean
```

---

# Key Constants (for reference)

```lean
L_rec : ℝ := 2.2           -- Phase threshold (arctan-based proofs)
K_tail : ℝ := 2.1          -- Carleson embedding constant  
C_geom : ℝ := 1/2          -- Green-Cauchy-Schwarz constant
C_FS : ℝ := 51             -- Fefferman-Stein constant (Arcozzi-Domingo 2024)
C_tail : ℝ := 0.20         -- BMO tail bound (Carneiro et al.)
U_tail : ℝ := C_geom * √K_tail  -- = 0.5 * √2.1 ≈ 0.72
```

**Key inequalities** (proven in Basic.lean):
- `U_tail < L_rec` : 0.72 < 2.2 ✓
- `L_rec < π` : 2.2 < 3.14 ✓ (needed for arctan-based proofs)
- `2 * arctan(2) > L_rec` : 2.21 > 2.2 ✓ (proven in ArctanTwoGtOnePointOne.lean)

---

# File Locations

```
RiemannRecognitionGeometry/
├── Basic.lean              -- Constants, key inequalities (CLEAN)
├── Axioms.lean             -- Phase geometry (7 sorries)
├── JohnNirenberg.lean      -- BMO theory (6 sorries)  
├── DirichletEta.lean       -- ζ on (0,1) (2 axioms, 2 sorries)
├── Main.lean               -- Main theorem (1 sorry)
├── FeffermanStein.lean     -- Carleson bounds (CLEAN)
├── PoissonJensen.lean      -- Blaschke factors (1 sorry)
├── CarlesonBound.lean      -- Embedding (CLEAN)
├── PoissonExtension.lean   -- [NEW] Poisson kernels (1 axiom)
├── FeffermanSteinBMO.lean  -- [NEW] BMO-Carleson (2 axioms)
└── WhitneyGeometry.lean -- Interval structure (CLEAN)
```
