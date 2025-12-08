# Riemann Hypothesis Recognition Geometry - Continuation Prompt

## Goal
Complete a fully unconditional Lean 4 proof of the Riemann Hypothesis using Recognition Geometry. No `sorry`s or custom axioms allowed.

## Current Status (Updated Dec 8, 2025)
- **Build**: ✅ Compiles successfully  
- **Sorries**: 9 sorry calls in 6 declarations
- **Architecture**: Sound - correct Recognition Geometry argument

## Recent Progress

### Proven Lemmas
- `arctan_sub_of_neg`: Arctan subtraction formula for negative arguments
- Restructured γ > 0, σ > b case with clear proof outline

## Remaining Sorries (9 sorry calls, 6 declarations)

### Axioms.lean (6 sorry calls, 3 declarations)

| Line | Declaration | Content | Analysis |
|------|-------------|---------|----------|
| 165, 169 | `phaseChange_abs_conj` | Im(B)=0 implies t=Re(ρ) | Low priority (unused) |
| 850 | `phase_bound_from_arctan` | σ > b, γ > 0 | Needs Whitney bound on xy |
| 1048 | `phase_bound_neg_im` | mixed-sign, γ < 0 | Symmetric to γ > 0 |
| 1084 | `phase_bound_neg_im` | σ < a, γ < 0 | Both x,y < 0, y > x |
| 1156 | `phase_bound_neg_im` | σ > b, γ < 0 | Both x,y > 0, y > x |

### FeffermanStein.lean (3 sorry calls, 3 declarations)

| Line | Declaration | Content | Notes |
|------|-------------|---------|-------|
| 290 | `logAbsXi_growth` | Polynomial bounds | nlinarith issues |
| 361 | `actualPhaseSignal_bound` | Carleson chain | High priority |
| 404 | `phase_decomposition` | Weierstrass tail | High priority |

## Key Mathematical Analysis

### Phase Bound Cases

The arctan subtraction formula gives:
```
arctan(a) - arctan(b) = arctan((a-b)/(1+ab))
```

For |phaseChange| = 2|arctan(x) - arctan(y)| ≥ 2*arctan(1/3) ≥ L_rec, we need:
```
|x - y|/(1 + xy) ≥ 1/3
```

With |x - y| ≥ 1 (proven from width constraints), we need xy ≤ 2 + |x-y|.

**Proven case (γ > 0, σ < a):**
- Both x, y > 0, x > y
- Key: y = (a-σ)/γ < 1 from a - σ < a ≤ γ
- This bounds xy and gives the result

**Remaining cases need similar geometric bounds:**
- γ > 0, σ > b: Need -x < 1 or -y < 1 (both negative)
- γ < 0 cases: Mirror images via conjugation symmetry

### Critical Strip Constraint

For zeros of ζ(s) in the critical strip: 0 < Re(ρ) < 1.
Adding σ < 1 as a hypothesis might help bound xy in the σ > b cases.

## Build Commands

```bash
lake build 2>&1 | grep -E "error:|sorry"
grep -n "sorry" RiemannRecognitionGeometry/Axioms.lean RiemannRecognitionGeometry/FeffermanStein.lean
```

## Next Steps

1. **Phase bounds** - Investigate adding σ < 1 constraint or alternative bounds
2. **Conjugation symmetry** - Use |phaseChange ρ| = |phaseChange (conj ρ)|
3. **FeffermanStein** - Focus on actualPhaseSignal_bound and phase_decomposition

## Notes

- DirichletEta.lean being developed in separate session (zero_has_nonzero_im)
- The phaseChange_abs_conj lemma is "not used in main proof"
- γ < 0 cases are symmetric to γ > 0 via conjugation
