# Riemann Hypothesis Recognition Geometry - Continuation Prompt

## Goal
Complete a fully unconditional Lean 4 proof of the Riemann Hypothesis using Recognition Geometry. No `sorry`s or custom axioms allowed.

## Current Status (Updated Dec 8, 2025)
- **Build**: ✅ Compiles successfully  
- **Sorries**: 9 sorry calls in 6 declarations
- **Architecture**: Sound - correct Recognition Geometry argument

## Remaining Sorries (9 sorry calls, 6 declarations)

### Axioms.lean (6 sorry calls, 3 declarations)

| Line | Declaration | Content | Notes |
|------|-------------|---------|-------|
| 165, 169 | `phaseChange_abs_conj` | Im(B)=0 implies t=Re(ρ) | Low priority (unused) |
| 802 | `phase_bound_from_arctan` | σ > b, γ > 0 | Whitney geometry |
| 996 | `phase_bound_neg_im` | mixed-sign, γ < 0 | Symmetric to γ > 0 |
| 1032 | `phase_bound_neg_im` | σ < a, γ < 0 | Both x,y < 0 |
| 1104 | `phase_bound_neg_im` | σ > b, γ < 0 | Both x,y > 0 |

### FeffermanStein.lean (3 sorry calls, 3 declarations)

| Line | Declaration | Content | Notes |
|------|-------------|---------|-------|
| 290 | `logAbsXi_growth` | Polynomial bounds | nlinarith issues |
| 361 | `actualPhaseSignal_bound` | Carleson chain | High priority |
| 404 | `phase_decomposition` | Weierstrass tail | High priority |

## Proof Structure

```
IF zero ρ exists with Re(ρ) > 1/2:
  │
  ├── Blaschke contribution B(I,ρ) ≥ L_rec ≈ 0.55
  │   └── From phase_bound_from_arctan (mostly proven, needs 4 cases)
  │
  ├── Total phase signal |R(I)| ≤ U_tail ≈ 0.13  
  │   └── actualPhaseSignal_bound + phase_decomposition (needs work)
  │
  ├── Key inequality: L_rec > 4 * U_tail ✅ PROVEN
  │
  └── Contradiction!
```

## Key Mathematical Insight for Phase Bounds

All 4 remaining phase bound sorries follow the same pattern:

**Setup:**
- x = (b-σ)/γ, y = (a-σ)/γ where σ = Re(ρ), γ = Im(ρ)
- Interval spread: |x - y| = (b-a)/|γ| ≥ 1

**Cases:**
1. **γ > 0, σ > b**: x < 0, y < 0 (both negative)
2. **γ < 0, mixed-sign**: y ≥ 0 ≥ x
3. **γ < 0, σ < a**: x < 0, y < 0 (both negative)
4. **γ < 0, σ > b**: x > 0, y > 0 (both positive)

**Goal:** |phaseChange| = 2|arctan(x) - arctan(y)| ≥ L_rec

**Approach:** For same-sign cases, use arctan subtraction:
arctan(y) - arctan(x) = arctan((y-x)/(1+xy))
With |y-x| ≥ 1 and bounded xy, get ≥ arctan(1/3) > L_rec/2

## Build Commands

```bash
lake build 2>&1 | grep -E "error:|sorry"
grep -n "sorry" RiemannRecognitionGeometry/Axioms.lean RiemannRecognitionGeometry/FeffermanStein.lean
```

## Next Steps

1. **Phase bounds** - Prove the arctan subtraction formulas for remaining 4 cases
2. **Carleson chain** - actualPhaseSignal_bound via Fefferman-Stein
3. **Weierstrass tail** - phase_decomposition bound

## Notes

- DirichletEta.lean being developed in separate session (zero_has_nonzero_im)
- The phaseChange_abs_conj lemma is "not used in main proof"
- γ < 0 cases are symmetric to γ > 0 via conjugation
