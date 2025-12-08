# Parallel Session Prompts for Riemann Hypothesis Proof Completion

Each prompt below is self-contained. Open a new AI chat session and paste one prompt.

---

## SESSION 1: Phase Conjugation & γ < 0 Cases

**Sorries**: Lines 194, 898, 931, 999 in `RiemannRecognitionGeometry/Axioms.lean`

PROMPT:
```
Continue working on the Riemann Hypothesis Recognition Geometry proof in Lean 4.
Workspace: /Users/jonathanwashburn/Projects/riemann-geometry-rs

YOUR TASK: Prove the phase conjugation lemma and the γ < 0 phase bound cases.

TARGET SORRIES in RiemannRecognitionGeometry/Axioms.lean:

1. Line 194 (phaseChange_abs_conj): Prove |phaseChange (conj ρ) a b| = |phaseChange ρ a b|
   - Key: blaschkeFactor (conj ρ) t = (blaschkeFactor ρ t)⁻¹
   - So arg(B_conj) = -arg(B) using Complex.arg_inv
   - Therefore phaseChange (conj ρ) = -phaseChange ρ, and |-x| = |x|

2. Lines 898, 931, 999 (phase_bound_neg_im cases): Once #194 is proven, these reduce to γ > 0 cases via symmetry.

Mathlib: Complex.arg_inv, Complex.conj_sub, abs_neg

Build: lake build
Check: grep -n "sorry" RiemannRecognitionGeometry/Axioms.lean

Goal: Eliminate all 4 sorries.
```

---

## SESSION 2: Mixed-Sign Arctan Bound (γ > 0)

**Sorry**: Line 629 in `RiemannRecognitionGeometry/Axioms.lean`

PROMPT:
```
Continue working on the Riemann Hypothesis Recognition Geometry proof in Lean 4.
Workspace: /Users/jonathanwashburn/Projects/riemann-geometry-rs

YOUR TASK: Prove the arctan bound for the mixed-sign case when γ > 0.

TARGET SORRY Line 629:
  have h_phaseChange_lower : |phaseChange ρ a b| ≥ 4 * Real.arctan (1/5) := by sorry

Mathematical derivation:
1. x = (b-σ)/γ > 0, |y| = (σ-a)/γ > 0, where σ = ρ.re ∈ (a,b)
2. |phaseChange| = 2π - 2*(arctan(x) + arctan(|y|))
3. From h_width_upper: x + |y| = (b-a)/γ ≤ 10
4. By concavity of arctan: arctan(x) + arctan(|y|) ≤ 2*arctan(5)
5. So |phaseChange| ≥ 2π - 4*arctan(5) = 4*arctan(1/5)

Key Mathlib: Real.arctan_inv_of_pos, blaschkePhase_arctan (in PoissonJensen.lean)
Existing: Real.four_arctan_fifth_gt_L_rec (in Mathlib/ArctanTwoGtOnePointOne.lean)

Build: lake build
Check: grep -n "sorry" RiemannRecognitionGeometry/Axioms.lean

Goal: Eliminate this sorry.
```

---

## SESSION 3: Same-Sign Case σ > b (γ > 0)

**Sorry**: Line 749 in `RiemannRecognitionGeometry/Axioms.lean`

PROMPT:
```
Continue working on the Riemann Hypothesis Recognition Geometry proof in Lean 4.
Workspace: /Users/jonathanwashburn/Projects/riemann-geometry-rs

YOUR TASK: Prove the phase bound for the σ > b case when γ > 0.

TARGET SORRY Line 749:
  sorry -- σ > b case: requires Whitney geometry analysis

Mathematical situation:
- σ = ρ.re > b > a, so both a - σ < 0 and b - σ < 0
- x = (a - σ)/γ < 0 and y = (b - σ)/γ < 0
- Need |phaseChange ρ a b| ≥ L_rec

From width constraints h_width_lower: b - a ≥ γ and h_width_upper: b - a ≤ 10γ:
- σ - a ≥ σ - b + γ > γ, so |x| = (σ-a)/γ > 1
- The arctan difference gives sufficient phase change

Existing: two_arctan_third_gt_half_arctan_two, arctan_sub_of_pos

Build: lake build
Check: grep -n "sorry" RiemannRecognitionGeometry/Axioms.lean

Goal: Eliminate this sorry.
```

---

## SESSION 4: Classical Number Theory Axioms

**Sorries**: Lines 1098, 1204 in `RiemannRecognitionGeometry/Axioms.lean`

PROMPT:
```
Continue working on the Riemann Hypothesis Recognition Geometry proof in Lean 4.
Workspace: /Users/jonathanwashburn/Projects/riemann-geometry-rs

YOUR TASK: Prove or properly axiomatize two classical number theory results.

TARGET SORRIES:

1. Line 1098 (classical_riemannZeta_neg_on_interval):
   axiom: ∀ s : ℝ, 0 < s → s < 1 → riemannZeta s < 0

   Proof via Dirichlet eta: η(s) = (1 - 2^(1-s)) * ζ(s)
   For s ∈ (0,1): η(s) > 0, and 1 - 2^(1-s) < 0, so ζ(s) < 0

2. Line 1204 (totalPhaseSignal_bound):
   theorem: |totalPhaseSignal I| ≤ U_tail

   This is Fefferman-Stein BMO→Carleson embedding (1972).
   Options: Full proof, or convert to explicit axiom with documentation.

Check Mathlib.NumberTheory.ZetaFunction for existing lemmas.
Check jonwashburn/riemann repo for Carleson formalization.

Build: lake build
Check: grep -n "sorry" RiemannRecognitionGeometry/Axioms.lean

Goal: Either prove or convert to clearly documented axioms.
```

---

## After All Sessions Complete

Run:
```bash
lake build
grep -rn "sorry" RiemannRecognitionGeometry/ Main.lean PoissonJensen.lean
```

Dependency: Session 1 should complete first (unlocks γ < 0 cases).
Sessions 2, 3, 4 can run in parallel.
