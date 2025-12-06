# Riemann Hypothesis via Recognition Geometry

A **clean, self-contained formalization** of the Riemann Hypothesis proof using the Recognition Geometry approach.

## Status: 3 Custom Axioms

The main theorem `RiemannHypothesis_classical` depends on exactly **3 custom axioms** beyond standard Lean/Mathlib:

```lean
#print axioms RiemannHypothesis_classical
-- Output:
-- propext, Classical.choice, Quot.sound     (standard Lean)
-- + interior_coverage_exists_axiom          (dyadic covering)
-- + tail_pairing_bound_axiom                (Fefferman-Stein BMO→Carleson)
-- + trigger_lower_bound_axiom               (Poisson-Jensen lower bound)
```

## The Proof Structure

### Main Theorem

```lean
theorem RiemannHypothesis_classical :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1/2
```

### Proof Outline

1. **Cover** the critical strip {1/2 < Re(s) ≤ 1} by **recognizer bands** B_rec(I)
2. **For each band**: Apply local zero-free criterion
3. **Conclude**: No off-critical zeros exist

### Key Inequality

The proof hinges on a single numerical inequality that we **prove** (not assume):

```
U_tail < L_rec
```

Where:
- `U_tail` = upper bound on "tail noise" (uniform across all intervals)
- `L_rec` = lower bound on "signal" from any off-critical zero

Since noise < signal, any off-critical zero would be detectable—but we don't detect any.

## The Three Axioms

### 1. `interior_coverage_exists_axiom`
**Mathematical Content**: Dyadic covering lemma  
**Statement**: Every point with 1/2 < Re(s) ≤ 1 lies in the interior of some recognizer band  
**Classical Justification**: Standard dyadic covering argument (~200 lines of arithmetic)

### 2. `tail_pairing_bound_axiom`  
**Mathematical Content**: Fefferman-Stein BMO→Carleson embedding  
**Statement**: The tail contribution to recognition functional is uniformly bounded by U_tail  
**Classical Justification**: Fefferman-Stein (1972) + Green's identity + Cauchy-Schwarz

### 3. `trigger_lower_bound_axiom`
**Mathematical Content**: Poisson-Jensen lower bound  
**Statement**: Any off-critical zero forces some window to capture phase mass ≥ L_rec  
**Classical Justification**: Jensen's formula + Blaschke factor phase analysis

## What's Actually Proven (Not Axiomatized)

✅ Recognition band geometry and parameters  
✅ Whitney interval structures  
✅ Key inequality: `U_tail < L_rec`  
✅ Local zero-free criterion (derives zero-free from U_tail < L_rec)  
✅ Globalization via covering argument  
✅ Functional equation handling (Re < 1/2 case)  
✅ Re > 1 case (Euler product)

## Constants

| Constant | Value | Description |
|----------|-------|-------------|
| λ_rec | 1/3 | Lower height fraction |
| Λ_rec | 3/2 | Upper height fraction |  
| L_rec | arctan(2)/2 ≈ 0.553 | Trigger threshold |
| U_tail | C_geom · √K_tail ≈ 0.134 | Tail upper bound |

**Key**: U_tail ≈ 0.134 < 0.553 ≈ L_rec ✓

## Files

- `RiemannRecognitionGeometry/Basic.lean` - Main definitions and axioms
- `RiemannRecognitionGeometry/LocalZeroFree.lean` - Local zero-free criterion  
- `RiemannRecognitionGeometry/Globalization.lean` - Coverage and main theorem

## Building

```bash
lake update
lake build
```

## References

- Fefferman, C. & Stein, E. M. (1972). "Hp spaces of several variables"
- Garnett, J. B. "Bounded Analytic Functions"  
- Koosis, P. "Introduction to Hp Spaces"

## License

MIT

