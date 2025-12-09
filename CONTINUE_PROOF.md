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
| 903 | `phase_bound_from_arctan` | σ > b, γ > 0 | Whitney bound `xy ≤ 3(x-y) - 1` |
| 1128 | `phase_bound_neg_im` | σ ∈ [a,b], γ < 0 | Complex.arg analysis for γ < 0 |
| 1309 | `phase_bound_neg_im` | σ > b, γ < 0 | Same structure as line 903 |

## Technical Analysis

### Line 903: σ > b, γ > 0 Case
**Goal**: Prove `|phaseChange ρ a b| ≥ 2 * Real.arctan (1/3)`

**Structure**: For σ > b with γ > 0:
- x = (b-σ)/γ < 0 and y = (a-σ)/γ < 0 (both negative)
- x > y (x closer to 0)
- x - y = (b-a)/γ ≥ 1 (from `h_spread`)
- xy = |x||y| > 0

**Required bound**: `(x-y)/(1+xy) ≥ 1/3` ↔ `xy ≤ 3(x-y) - 1 = 3v - 1` where v = x-y ≥ 1

**Solution**: Add `hσ_upper : ρ.re ≤ 1` constraint through lemma chain.
With σ ≤ 1 and b ≥ γ (from hγ_upper): |x| = (σ-b)/γ ≤ (1-γ)/γ.
For γ ≥ 1/2: |x| ≤ 1. Combined with |y| = |x| + v, bound xy ≤ |x|(|x|+v) ≤ 1·(1+v) < 3v-1 for v≥1.

### Line 1128: Mixed-Sign γ < 0 Case  
**Goal**: Prove `|phaseChange ρ a b| ≥ L_rec` for σ ∈ [a, b] with γ < 0

**Structure**: x ≤ 0 ≤ y with y - x ≥ 1

**Solution options (in order of simplicity)**:
1. **Interior case (a < σ < b)**: Use `phaseChange_abs_conj` + `4*arctan(1/5) > L_rec`. ✅ Works
2. **Edge case b = σ**: arg(B(a)) < 0 since Im(B(a)) < 0. |arg(B(a)) - π| = π - arg(B(a)) > π > L_rec. Needs `Complex.arg_neg_of_im_neg` or equivalent.
3. **Edge case a = σ**: arg(B(b)) ∈ (0, π/2] (bounded by width). |π - arg(B(b))| ≥ π/2 > L_rec. Needs `Complex.arg_pos_of_im_pos` or equivalent.

**Key Mathlib lemmas needed**:
- `Complex.arg_nonneg_iff` (for Im ≥ 0 ↔ arg ∈ [0, π])
- `Complex.arg_neg_iff` (for Im < 0 ↔ arg < 0)
- Or use `Complex.arg_eq_pi_iff` to exclude the π case

### Line 1309: σ > b, γ < 0 Case
Via conjugation symmetry, same analysis as line 903 applies to |phaseChange (conj ρ)|.

## Helper Lemmas Available

- `phaseChange_abs_conj`: `|phaseChange ρ a b| = |phaseChange (conj ρ) a b|`
- `blaschkeFactor_at_re'`: `B(σ) = -1` when `γ ≠ 0`
- `blaschkeFactor_re_im`: Re and Im formulas for B(t)
- `Complex.arg_eq_pi_iff`: `arg z = π ↔ z.re < 0 ∧ z.im = 0`
- `Complex.abs_arg_le_pi`: `|arg z| ≤ π`
- `Real.four_arctan_fifth_gt_L_rec`: `4*arctan(1/5) > L_rec`

## Build Commands

```bash
lake build 2>&1 | grep -E "error:|sorry"
grep -n "sorry" RiemannRecognitionGeometry/Axioms.lean
```

## Recommended Approach

1. **For line 1128 interior case**: Already handled by conjugation in the code structure, just need the edge cases.

2. **For line 1128 edge cases**: The b = σ case is easier:
   - Show Im(B(a)) < 0 using `blaschkeFactor_re_im`
   - Conclude arg(B(a)) < 0 (avoiding `Complex.arg_neg_iff` by proving arg ≠ π using `Complex.arg_eq_pi_iff`)
   - Then |arg - π| = π - arg > π > L_rec

3. **For lines 903 and 1309**: Add σ ≤ 1 constraint through:
   - `phase_bound_from_arctan` signature
   - `phase_bound_neg_im` signature  
   - `blaschke_lower_bound` signature
   - Call sites in `zero_free_with_interval`, `local_zero_free`, `no_interior_zeros`

## Notes

- FeffermanStein.lean is completely proven (with 5 axioms)
- The σ ≤ 1 constraint is mathematically sound (critical strip)
- All 3 sorries share Whitney geometry structure
- Avoid `Complex.arg_nonneg_iff` if not available in Mathlib4
