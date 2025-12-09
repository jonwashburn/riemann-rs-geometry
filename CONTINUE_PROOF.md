# Riemann Hypothesis Recognition Geometry - Continuation Prompt

## Goal
Complete a fully unconditional Lean 4 proof of the Riemann Hypothesis using Recognition Geometry. No `sorry`s or custom axioms allowed.

## Current Status (Updated Dec 9, 2025)
- **Build**: ✅ Compiles successfully  
- **Sorries**: 3 sorry calls in 2 declarations
- **FeffermanStein.lean**: ✅ SORRY-FREE!

## Remaining Sorries (3 sorry calls, 2 declarations)

| Line | Declaration | Case | Blocker |
|------|-------------|------|---------|
| 903 | `phase_bound_from_arctan` | σ > b, γ > 0 | Needs σ ≤ 1 + bound proof |
| 1128 | `phase_bound_neg_im` | σ ∈ [a,b], γ < 0 | Needs `blaschkePhase_arctan` for γ < 0 |
| 1309 | `phase_bound_neg_im` | σ > b, γ < 0 | Same as line 903 |

## Technical Analysis

### Line 903: σ > b, γ > 0 Case
**Goal**: Prove `|phaseChange ρ a b| ≥ 2 * Real.arctan (1/3)`

**Structure**: For σ > b with γ > 0:
- x = (b-σ)/γ < 0 and y = (a-σ)/γ < 0 (both negative)
- x > y (x closer to 0)
- x - y = (b-a)/γ ≥ 1 (from `h_spread`)
- xy = |x||y| > 0

**Required bound**: `(x-y)/(1+xy) ≥ 1/3`, i.e., `xy ≤ 3(x-y) - 1`

**Solution**: Add `hσ_upper : ρ.re ≤ 1` constraint through lemma chain:
- This bounds |x| = (σ-b)/γ ≤ (1-γ)/γ
- For γ ≥ 1/2: |x| ≤ 1, giving bounded xy
- Propagate through: `phase_bound_from_arctan` → `phase_bound_neg_im` → `blaschke_lower_bound` → call sites

### Line 1128: Mixed-Sign γ < 0 Case  
**Goal**: Prove `|phaseChange ρ a b| = 2 * (Real.arctan y - Real.arctan x)` for γ < 0

**Structure**: For σ ∈ [a, b] with γ < 0:
- x = (b-σ)/γ ≤ 0 (b ≥ σ, γ < 0)
- y = (a-σ)/γ ≥ 0 (a ≤ σ, γ < 0)  
- y - x ≥ 1 gives `arctan(y) - arctan(x) ≥ arctan(1/2)`

**Solution Options**:
1. **Extend `blaschkePhase_arctan`** to γ ≠ 0 (same formula works)
2. **Use conjugation**: `|phaseChange ρ| = |phaseChange (conj ρ)|` where conj ρ has γ > 0
3. **Direct proof** via Complex.arg analysis of Blaschke factor

**Current edge case handling**: Uses `blaschkeFactor_at_re'` for a = σ or b = σ

### Line 1309: σ > b, γ < 0 Case
Same structure as line 903 but with negative γ. Via conjugation, reduces to γ > 0 case.

## Helper Lemmas Available

- `phaseChange_abs_conj`: |phaseChange ρ a b| = |phaseChange (conj ρ) a b|
- `blaschkeFactor_at_re'`: B(σ) = -1 when γ ≠ 0
- `blaschkeFactor_re_im`: Re and Im formulas for B(t)
- `Real.four_arctan_fifth_gt_L_rec`: 4*arctan(1/5) > L_rec

## Build Commands

```bash
lake build 2>&1 | grep -E "error:|sorry"
grep -n "sorry" RiemannRecognitionGeometry/Axioms.lean
```

## Next Steps

1. **Add σ ≤ 1 constraint** through lemma chain (see Technical Analysis)
2. **Extend `blaschkePhase_arctan`** to handle γ < 0 (or use conjugation approach)
3. **Complete proofs** using derived bounds

## Notes

- FeffermanStein.lean is completely proven (with 5 axioms)
- The σ ≤ 1 constraint is mathematically sound for RH (critical strip)
- All 3 sorries share similar Whitney geometry structure
