# Lean Formalization Completion Guide

## Overview

The Recognition Geometry proof of the Riemann Hypothesis is **structurally complete** in Lean 4. The logical flow from axioms to RH is fully verified. This document organizes the remaining axioms into **5 parallel tracks** that can be worked on simultaneously.

**Repository**: `/Users/jonathanwashburn/Projects/riemann-geometry-rs/`

**Key Files**:
- `RiemannRecognitionGeometry/Main.lean` - Main theorems
- `RiemannRecognitionGeometry/Basic.lean` - Core definitions and constants
- `RiemannRecognitionGeometry/Axioms.lean` - Phase bounds and signal machinery
- `RiemannRecognitionGeometry/FeffermanStein.lean` - BMO→Carleson embedding
- `RiemannRecognitionGeometry/JohnNirenberg.lean` - John-Nirenberg infrastructure
- `RiemannRecognitionGeometry/DirichletEta.lean` - ζ(s) ≠ 0 on (0,1)
- `riemann-recognition-geometry.tex` - Complete mathematical paper with full proofs

**Paper Status**: The LaTeX paper now contains complete proofs for all key results:
- C_FS = 10 (Proposition 4.3, lines 1085-1166)
- C_tail ≤ 0.11 (Proposition 4.5 + Corollary 4.6, lines 622-715)
- C_geom = 1/√2 (Appendix A.2, lines 4424-4460)
- Phase Decomposition (Lemma 6.1, lines 1988-2039)

---

## Current Axiom Inventory (16 total)

| Track | File | Axiom | Line | Difficulty |
|-------|------|-------|------|------------|
| 1 | Basic.lean | `log_T0_lt_14` | 290 | Easy |
| 2 | DirichletEta.lean | `tendsto_factor_mul_zeta_at_one_axiom` | 737 | Medium |
| 2 | DirichletEta.lean | `dirichletEtaReal_one_axiom` | 767 | Medium |
| 2 | DirichletEta.lean | `continuous_dirichletEtaReal_axiom` | 788 | Medium |
| 2 | DirichletEta.lean | `identity_principle_zeta_eta_axiom` | 824 | Medium |
| 3 | JohnNirenberg.lean | `czDecomposition_axiom` | 566 | Hard |
| 3 | JohnNirenberg.lean | `czDecompFull_axiom` | 604 | Hard |
| 3 | JohnNirenberg.lean | `goodLambda_axiom` | 1023 | Hard |
| 3 | JohnNirenberg.lean | `jn_first_step_axiom` | 1074 | Hard |
| 3 | JohnNirenberg.lean | `bmo_Lp_bound_axiom` | 1235 | Medium |
| 3 | JohnNirenberg.lean | `bmo_kernel_bound_axiom` | 1295 | Medium |
| 3 | JohnNirenberg.lean | `poisson_gradient_bound_combination_axiom` | 2100 | Medium |
| 4 | Axioms.lean | `phaseChange_arctan_mixed_sign_axiom` | 510 | Medium |
| 4 | Axioms.lean | `criticalLine_phase_edge_case_axiom` | 1913 | Medium |
| 5 | Axioms.lean | `green_identity_axiom` | 1831 | Medium |
| 5 | Axioms.lean | `weierstrass_tail_bound_for_phase` | 2049 | Hard |

---

# TRACK 1: Pure Numeric Bound

**Difficulty**: Easy (1 axiom)  
**Estimated Time**: 30 minutes  
**File**: `RiemannRecognitionGeometry/Basic.lean`

## Task

Prove the single numeric bound:

```lean
axiom log_T0_lt_14 : Real.log T0 < 14
```

where `T0 = 10^6`.

## Mathematical Content

This is pure arithmetic:
- `log(10^6) = 6 × log(10) ≈ 6 × 2.302585 ≈ 13.8155 < 14`

## Implementation Strategy

```lean
theorem log_T0_lt_14_proof : Real.log T0 < 14 := by
  unfold T0
  -- T0 = 10^6 = (10:ℝ)^6
  have h1 : Real.log ((10:ℝ)^6) = 6 * Real.log 10 := Real.log_pow 10 6
  rw [h1]
  -- log(10) < 2.4, so 6 * log(10) < 14.4 < 14? No, need tighter.
  -- Actually log(10) ≈ 2.3026, so 6 * 2.3026 = 13.8155 < 14
  have h2 : Real.log 10 < 2.31 := by native_decide -- or explicit bound
  calc 6 * Real.log 10 < 6 * 2.31 := by nlinarith
    _ = 13.86 := by norm_num
    _ < 14 := by norm_num
```

## Verification

After implementation, run:
```bash
lake build RiemannRecognitionGeometry.Basic
```

---

# TRACK 2: Dirichlet Eta Function

**Difficulty**: Medium (4 axioms)  
**Estimated Time**: 2-4 hours  
**File**: `RiemannRecognitionGeometry/DirichletEta.lean`

## Task

Prove the four axioms needed to establish ζ(s) ≠ 0 on (0,1):

1. `tendsto_factor_mul_zeta_at_one_axiom` (line 737)
2. `dirichletEtaReal_one_axiom` (line 767)
3. `continuous_dirichletEtaReal_axiom` (line 788)
4. `identity_principle_zeta_eta_axiom` (line 824)

## Mathematical Content

The key identity is: for s ∈ (0,1),
```
η(s) = (1 - 2^{1-s}) · ζ(s)
```

Since η(s) > 0 (alternating series with decreasing positive terms) and (1 - 2^{1-s}) < 0 (since 2^{1-s} > 1 for s < 1), we get ζ(s) < 0, hence ζ(s) ≠ 0.

### Axiom 1: `tendsto_factor_mul_zeta_at_one_axiom`

The limit as s → 1 of (1 - 2^{1-s}) · ζ(s) equals log(2). This follows from:
- ζ(s) has a simple pole at s=1 with residue 1
- (1 - 2^{1-s}) vanishes at s=1 with derivative log(2)
- L'Hôpital: limit = log(2) × 1 = log(2)

### Axiom 2: `dirichletEtaReal_one_axiom`

η(1) = 1 - 1/2 + 1/3 - 1/4 + ... = log(2) (alternating harmonic series)

### Axiom 3: `continuous_dirichletEtaReal_axiom`

η(s) is continuous for s > 0. Follows from uniform convergence of the Dirichlet series on compact subsets.

### Axiom 4: `identity_principle_zeta_eta_axiom`

The identity η(s) = (1 - 2^{1-s}) · ζ(s) for s ∈ (0,1). 

Proof: For Re(s) > 1, direct calculation shows η(s) = (1 - 2^{1-s}) ζ(s). Both sides are analytic on Re(s) > 0, so by identity principle they agree on (0,1).

## Paper Reference

See `riemann-recognition-geometry.tex`, Section 8.2 (lines 2795-2860) for the complete mathematical argument.

## Implementation Strategy

The file `DirichletEta.lean` already has substantial infrastructure:
- `dirichletEtaReal`: Definition via ordered partial sums
- `dirichletEtaReal_pos`: η(s) > 0 for s > 0 (proven)
- Helper lemmas for alternating series

The main work is connecting to Mathlib's `riemannZeta` and proving the identity principle application.

## Verification

```bash
lake build RiemannRecognitionGeometry.DirichletEta
```

---

# TRACK 3: John-Nirenberg Infrastructure

**Difficulty**: Hard (7 axioms)  
**Estimated Time**: 1-2 weeks  
**File**: `RiemannRecognitionGeometry/JohnNirenberg.lean`

## Task

Prove the seven John-Nirenberg axioms needed for the Fefferman-Stein theorem:

1. `czDecomposition_axiom` (line 566) - Calderón-Zygmund decomposition
2. `czDecompFull_axiom` (line 604) - Full C-Z decomposition
3. `goodLambda_axiom` (line 1023) - Good-λ inequality
4. `jn_first_step_axiom` (line 1074) - First step of J-N proof
5. `bmo_Lp_bound_axiom` (line 1235) - BMO → L^p bound
6. `bmo_kernel_bound_axiom` (line 1295) - BMO kernel convolution
7. `poisson_gradient_bound_combination_axiom` (line 2100) - Combined gradient bounds

## Mathematical Content

### The John-Nirenberg Inequality

For f ∈ BMO(ℝ) with ‖f‖_BMO ≤ M:
```
|{x ∈ I : |f(x) - f_I| > λ}| ≤ C₁ · |I| · exp(-C₂ · λ / M)
```

with explicit constants C₁ = 2, C₂ = 1.

### Proof Chain

1. **Calderón-Zygmund Decomposition**: For f integrable on I and threshold t > avg|f|, decompose I into "good" set G and disjoint "bad" intervals {I_j} where:
   - |f| ≤ t a.e. on G
   - t < (1/|I_j|)∫_{I_j}|f| ≤ 2t

2. **Good-λ Inequality**: For f ∈ BMO with ‖f‖ ≤ M,
   ```
   |{|f - f_I| > 2t}| ≤ (1/2) · |{|f - f_I| > t}|  for t > M
   ```

3. **John-Nirenberg**: Iterate good-λ to get exponential decay.

4. **BMO → L^p**: From J-N, for p < ∞,
   ```
   (1/|I|) ∫_I |f - f_I|^p ≤ C_p · M^p
   ```

5. **Gradient Bounds**: Combine L^p bounds with Poisson kernel estimates.

## Paper Reference

See `riemann-recognition-geometry.tex`:
- Proposition 4.3 (lines 1085-1166): C_FS = 10 derivation with J-N constants C₁=2, C₂=1
- The proof chain: energy identity → local piece → tail piece → combine

## Implementation Strategy

The file `JohnNirenberg.lean` already has:
- `dyadicChild`, `dyadicParent`: Dyadic interval structure
- `meanOscillation`: BMO seminorm
- `intervalAverage`: Mean value
- Partial C-Z decomposition structure

Recommended order:
1. First prove `czDecomposition_axiom` and `czDecompFull_axiom`
2. Then `goodLambda_axiom` and `jn_first_step_axiom`
3. Then `bmo_Lp_bound_axiom` via layer-cake formula
4. Finally the kernel bounds

## Verification

```bash
lake build RiemannRecognitionGeometry.JohnNirenberg
```

---

# TRACK 4: Blaschke Phase Geometry

**Difficulty**: Medium (2 axioms)  
**Estimated Time**: 2-4 hours  
**File**: `RiemannRecognitionGeometry/Axioms.lean`

## Task

Prove the two phase geometry axioms:

1. `phaseChange_arctan_mixed_sign_axiom` (line 510)
2. `criticalLine_phase_edge_case_axiom` (line 1913)

## Mathematical Content

### Axiom 1: Mixed-Sign Phase Change

For ρ = σ + iγ with 1/2 < σ ≤ 1, γ ∈ [a, b], the Blaschke phase change satisfies:
```
|phaseChange ρ a b| ≥ L_rec = arctan(2)/2 ≈ 0.553
```

**Case Analysis**: The same-sign cases (σ < a or σ > b) are already proven in the file. The mixed-sign case (a < σ < b) requires:
- The phase crosses from one quadrant to another as t goes from a to b
- Total phase change ≥ arctan(2)/2

**Proof Strategy**: When σ ∈ (a, b), we have:
- At t = a: arg(a - σ + iγ) in one half-plane
- At t = b: arg(b - σ + iγ) in the other half-plane
- The argument must cross through π/2 or -π/2, giving total change ≥ π/2 > L_rec

### Axiom 2: Edge Case Phase

The edge case when the endpoint exactly lands on a quadrant boundary. This is measure-zero and handled separately.

## Paper Reference

See `riemann-recognition-geometry.tex`:
- Section 5 (Trigger Bound): Theorem 5.1 (lines 1423-1524)
- The three cases analysis: same-sign positive, same-sign negative, mixed-sign

## Existing Infrastructure

The file `Axioms.lean` already has extensive phase analysis:
- `phaseChange_arctan_formula`: Basic formula
- `arctan_sub_of_pos`: Subtraction formula for arctan
- Complete proofs for σ < a case (lines 905-989)
- Complete proofs for σ > b case (lines 990-1100)

The mixed-sign case follows the same pattern but with different sign analysis.

## Implementation Strategy

1. For `phaseChange_arctan_mixed_sign_axiom`:
   - Use the existing `phaseChange_arctan_formula`
   - Handle the case where a - σ < 0 < b - σ
   - Show the phase change spans at least one quadrant

2. For `criticalLine_phase_edge_case_axiom`:
   - This is a degenerate case with measure-zero probability
   - The proof can use continuity arguments or direct calculation

## Verification

```bash
lake build RiemannRecognitionGeometry.Axioms
```

---

# TRACK 5: Green's Identity & Tail Bounds

**Difficulty**: Medium-Hard (2 axioms)  
**Estimated Time**: 3-6 hours  
**File**: `RiemannRecognitionGeometry/Axioms.lean`

## Task

Prove the two analytic axioms:

1. `green_identity_axiom` (line 1831)
2. `weierstrass_tail_bound_for_phase` (line 2049)

## Mathematical Content

### Axiom 1: Green's Identity on Carleson Boxes

For a Whitney interval I with half-length L, and Carleson box Q(I) = I × (0, 2L):
```
|∫_I ∂u/∂σ(t, 0) dt| ≤ C_geom · √(E(I)) · |I|^{-1/2}
```

where E(I) is the Carleson energy and C_geom = 1/√2.

**Proof (from paper Appendix A.2):**

1. Green's first identity on the Carleson box Q = [t₀-L, t₀+L] × [0, 2L]:
   ```
   ∫_Q |∇u|² = -∫_Q u·Δu + ∫_{∂Q} u · (∂u/∂n)
   ```

2. Since u is harmonic (Δu = 0), the first term vanishes.

3. The boundary integral on the bottom edge (σ = 0) gives:
   ```
   ∫_I u(t,0) · ∂u/∂σ(t,0) dt
   ```

4. Cauchy-Schwarz:
   ```
   |∫_I ∂u/∂σ dt|² ≤ |I| · ∫_I |∂u/∂σ|² ≤ |I| · E(I)/(2L)
   ```

5. Taking square roots with |I| = 2L gives C_geom = 1/√2.

### Axiom 2: Weierstrass Tail Bound

The Hadamard product tail (zeros outside the local region) contributes:
```
|τ(I)| ≤ U_tail
```

This follows from:
- Hadamard factorization: ξ(s) = e^{B s} ∏_ρ (1 - s/ρ) e^{s/ρ}
- Localization: separate "nearby" zeros (Blaschke) from "far" zeros (tail)
- Poisson decay: far zeros contribute O(2^{-j}) per annulus
- The explicit bound C_tail ≤ 0.11 from Corollary 4.6

## Paper Reference

See `riemann-recognition-geometry.tex`:
- Appendix A.2 (lines 4424-4460): Explicit C_geom = 1/√2 derivation
- Proposition 4.5 + Corollary 4.6 (lines 622-715): C_tail ≤ 0.11
- Lemma 6.1 (lines 1988-2039): Phase decomposition into signal + tail

## Implementation Strategy

### For `green_identity_axiom`:

The paper provides the complete derivation. Key Lean steps:
1. Define the Carleson box region
2. Apply Green's first identity (may need to formalize or use as sub-axiom)
3. Use harmonicity of u
4. Apply Cauchy-Schwarz
5. Simplify to get C_geom = 1/√2

### For `weierstrass_tail_bound_for_phase`:

This is harder and may require:
1. Hadamard product theory (likely an axiom for now)
2. Poisson decay bounds (available in FeffermanStein.lean)
3. Geometric series summation (explicit in paper)

A pragmatic approach: use the explicit calculation from Corollary 4.6 to justify the bound, with Hadamard as a sub-axiom.

## Verification

```bash
lake build RiemannRecognitionGeometry.Axioms
```

---

# Build and Verification Commands

## Full Build
```bash
cd /Users/jonathanwashburn/Projects/riemann-geometry-rs
lake build
```

## Check Axiom Dependencies
```bash
lake env lean --run <<'EOF'
import RiemannRecognitionGeometry.Main
#print axioms RiemannHypothesis_classical
EOF
```

## Individual Track Builds
```bash
lake build RiemannRecognitionGeometry.Basic          # Track 1
lake build RiemannRecognitionGeometry.DirichletEta   # Track 2
lake build RiemannRecognitionGeometry.JohnNirenberg  # Track 3
lake build RiemannRecognitionGeometry.Axioms         # Track 4 & 5
```

---

# Priority Ordering

For fastest impact, work on tracks in this order:

1. **Track 1** (Easy, 30 min) - Removes 1 axiom immediately
2. **Track 4** (Medium, 2-4 hrs) - Completes phase geometry
3. **Track 2** (Medium, 2-4 hrs) - Completes eta/zeta connection
4. **Track 5** (Medium-Hard, 3-6 hrs) - Completes analytic core
5. **Track 3** (Hard, 1-2 weeks) - Major Mathlib contribution

Tracks 1-2-4-5 can all be worked in parallel. Track 3 is the longest but is self-contained.

---

# Success Criteria

The formalization is complete when:

```bash
lake env lean --run <<'EOF'
import RiemannRecognitionGeometry.Main
#print axioms RiemannHypothesis_classical
EOF
```

outputs only standard Lean axioms:
```
'RiemannHypothesis_classical' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

Currently it lists 16 custom axioms. Each track removes a subset of these.
