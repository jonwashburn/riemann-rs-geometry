# Analysis of Prior Work in `jonwashburn/riemann`

## Executive Summary

The `jonwashburn/riemann` repository contains **substantial prior work** on formalizing a proof of the Riemann Hypothesis in Lean 4. The repository pursues **two independent proof strategies**, both of which have significant infrastructure but remain incomplete.

**Other repositories** (`riemann-side`, `riemann-extra`, `riemann-arctan`, `riemann-finish`) return 404 - they are either private or deleted.

---

## Two Main Proof Strategies

### Strategy 1: Hardy-Schur Pinch Route (Boundary Certificate)

**Core Idea**: Construct a Schur function Θ via Cayley transform that forces a contradiction if off-critical zeros exist.

**Key Files**:
- `Riemann/RS/Cayley.lean` - Cayley transform, Schur bounds from Re(2J) ≥ 0
- `Riemann/RS/CRGreenOuter.lean` - CR-Green pairing
- `Riemann/RS/HalfPlaneOuterV2.lean` - Half-plane outer function
- `Riemann/Cert/KxiWhitney_RvM.lean` (103KB) - Annular Poisson energy bounds
- `Riemann/RS/BWP/ZeroDensity.lean` - Vinogradov-Korobov zero density (placeholder)

**The "Pinch" Logic** (from `proof_map.md`):
1. Assume off-critical zero ρ exists
2. Construct Θ(s) = (2J-1)/(2J+1) 
3. Show: Θ → -1 at ∞ (N1), Θ(ρ) = 1 (N2), |Θ| ≤ 1 (Schur)
4. Contradiction: Schur function can't be 1 in interior and -1 at boundary

**Status**: Blocked at:
- VK zero density (currently placeholder returning 0)
- CR-Green window bound (`sorry`)
- `PPlusFromCarleson` implication (unproven)

### Strategy 2: Weil Explicit Formula / De Branges Route

**Core Idea**: Use Weil's explicit formula relating zeros to primes, prove positivity of quadratic form.

**Key Files**:
- `Riemann/Weil/ExplicitFormula.lean` - Original explicit formula
- `Riemann/Weil/ExplicitFormula_new.lean` (19KB) - Enhanced version with Schwartz functions
- `Riemann/Weil/SelbergClass.lean` - Complete Selberg class definition
- `Riemann/Weil/ResidueSum.lean` - Residue theorem for rectangles
- `Riemann/RS/DeBranges/*.lean` - De Branges space approach

**Key Definitions from ExplicitFormula_new.lean**:
```lean
class IsWeilTestFunction (g : SchwartzMap ℝ ℂ) : Prop where
  even : ∀ x, g x = g (-x)
  decay : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖g x‖ ≤ C * Real.exp (-(1/2 + ε) * |x|)
  ft_decay : ∃ (C' ε' : ℝ), 0 < ε' ∧ ∀ ξ, ‖fourierTransformCLM ℂ g ξ‖ ≤ C' * Real.exp (-(1/2 + ε') * |ξ|)
```

**Status**: More complete structurally, but:
- Spectral side summability (`sorry`)
- Weil explicit formula theorem (`sorry`)
- Log-decay and prime sum lemmas (`sorry`)

---

## Valuable Components for Route 3

### 1. SelbergClass.lean - **Highly Relevant**

Complete formalization of:
- Riemann zeta as Selberg class member
- `differentiable_mul_sub_one_riemannZeta` - (s-1)ζ(s) extends to entire function
- `tendsto_sub_one_mul_riemannZeta_one` - Residue at s=1
- Functional equation structure

### 2. ExplicitFormula_new.lean - **Directly Relevant**

- `weilTransform` - Φ(s) = ∫ g(x) e^{(s-1/2)x} dx
- `spectralSide` - Σ_ρ Φ(ρ) over nontrivial zeros
- `geometricSide` - Prime terms + archimedean terms + boundary
- `primeTerm_summable` - Convergence lemmas
- `weilTransform_holomorphic_strip` - Analyticity in strip

### 3. ResidueSum.lean - **Useful Infrastructure**

- `integral_logDeriv_eq_sum_zeros` - Residue theorem for L'/L
- `LFunctionZeros` - Zero set infrastructure
- `countZerosInRect` - Zero counting

### 4. Cayley.lean - **Positivity Machinery**

- `Theta_Schur_of_Re_nonneg_on` - Key positivity → Schur bound
- `boundary_abs_J_pinch_eq_one` - Boundary modulus control
- `PinchCertificateExt` structure - Certificate packaging

### 5. KxiWhitney_RvM.lean - **Poisson/Energy Analysis**

- `Ksigma` - Poisson kernel
- `integral_ksigma_sq` - ∫ K_σ(t-x)² dt = (π/2)/σ
- `annularEnergy` - Energy on Whitney boxes
- Cauchy-Schwarz for finite sums

---

## Critical Gaps Identified (from remaining_gaps.md)

| Component | Sorry Count | Impact |
|-----------|-------------|--------|
| VK Zero Density | Placeholder (returns 0) | Blocks Carleson energy |
| Mellin/Theta/Euler | 39+ | Blocks Archimedean control |
| Fredholm det₂ | 16 | Blocks operator theory |
| CR-Green bound | 1 (critical) | Blocks wedge closure |
| De Branges HB | 4+ | Blocks alternative route |
| PNT components | 5+ | Blocks prime sum bounds |

---

## What Can Be Reused for Current Route 3

### Direct Ports (consider importing)

1. **Test function class**: `IsWeilTestFunction` is exactly what our `TestSpace` generalizes
2. **Selberg class zeta**: The verification that ζ satisfies Selberg axioms
3. **Poisson kernel lemmas**: `integral_ksigma_sq`, `integrable_ksigma_sq`
4. **Summability lemmas**: `summable_log_mul_rpow_of_one_lt`, `prime_sum_summable`

### Proof Strategies to Adopt

1. **Spectral side convergence**: Uses N(T) ~ T log T + rapid decay of Φ
2. **Geometric side assembly**: Uses -ζ'/ζ Dirichlet series + Fourier transforms
3. **Wedge/positivity logic**: Re(2J) ≥ 0 ⟹ |Θ| ≤ 1 via Cayley

### Key Observations

1. **The VK gap is fundamental**: Both routes ultimately need zero density estimates
2. **Explicit formula is well-structured**: The spectral=geometric identity is cleanly stated
3. **Positivity is the bottleneck**: Both routes reduce to proving some positivity condition
4. **The repos share infrastructure**: PrimeNumberTheoremAnd, StrongPNT dependencies

---

## Synthesis with Current Work

Our Route 3 in `RiemannRecognitionGeometry/ExplicitFormula/` should:

1. **Import/adapt the Weil test function class** - Already similar to our `TestSpace`
2. **Use the Selberg class zeta verification** - Saves proving entire/functional eq
3. **Leverage Poisson lemmas** for `W_arith` control
4. **The key remaining work** is the same:
   - Prove `W(1)(f * ~f̄) ≥ 0` (Weil positivity)
   - Or prove `λ_n ≥ 0` for all n (Li positivity)

### The "Recognition Science" Connection

The RS framework from `Source-Super.txt` provides a *physical interpretation*:
- The "Ledger" = distribution of primes
- "Conservation of Skew" = critical line constraint  
- "J-cost positivity" = Weil positivity

The mathematical translation requires showing:
- The arithmetic sum (over primes) defines a positive quadratic form
- This is equivalent to showing the explicit formula functional is positive

---

## Recommended Next Steps

1. **Clone/fork `jonwashburn/riemann`** for reference
2. **Port `IsWeilTestFunction`** to our Route 3 codebase
3. **Port `SelbergClass.riemannZeta`** verification
4. **Study the Cayley positivity logic** - may provide the detector construction
5. **The VK zero density gap is shared** - any progress benefits both approaches

---

## Summary of Files by Relevance to Route 3

### HIGH Priority (directly usable)
- `Riemann/Weil/ExplicitFormula_new.lean` - Weil test functions, transforms
- `Riemann/Weil/SelbergClass.lean` - Zeta in Selberg class
- `Riemann/RS/Cayley.lean` - Positivity/Schur machinery

### MEDIUM Priority (useful infrastructure)
- `Riemann/Weil/ResidueSum.lean` - Residue theorem
- `Riemann/Cert/KxiWhitney_RvM.lean` - Poisson kernel analysis
- `Riemann/Aux.lean` (64KB) - General utilities

### LOW Priority (alternative route)
- `Riemann/RS/DeBranges/*` - De Branges approach
- `Riemann/RS/BWP/*` - Boundary wedge proof files
- `Riemann/RS/CRGreen*.lean` - CR-Green machinery
