# Sorry Completion Plan

**Version**: 2.3 (December 2025)  
**Project**: Recognition Geometry proof of the Riemann Hypothesis  
**Current State**: 1 sorry, 19 axioms  
**Goal**: Prove the remaining sorry

---

## Quick Reference

| Track | Name | Sorries | Difficulty | File | Status |
|-------|------|---------|------------|------|--------|
| S1 | Dirichlet Eta | 1 | Hard | DirichletEta.lean | S1.1 ✅, S1.2 ⏳ |
| S2 | Dyadic Intervals | 0 | Easy | JohnNirenberg.lean | ✅ COMPLETE |
| S3 | CZ Decomposition | 0 | Medium | JohnNirenberg.lean | ✅ COMPLETE |
| S4 | Good-λ Inequality | 0 | Hard | JohnNirenberg.lean | ✅ COMPLETE |
| S5 | JN Integration | 0 | Medium | JohnNirenberg.lean | ✅ COMPLETE |

## Remaining Sorry

**`dirichletEtaReal_eq_factor_mul_zeta`** (DirichletEta.lean:1277)

```lean
theorem dirichletEtaReal_eq_factor_mul_zeta (s : ℝ) (hs : 0 < s) (hs_ne : s ≠ 1) :
    dirichletEtaReal s = (1 - (2 : ℝ)^(1-s)) * (riemannZeta (s : ℂ)).re
```

**What's proven**:
- Case s > 1: Fully proven via `etaZetaDiff_eq_zero_of_gt_one` and `zeta_eta_relation_gt_one`
- Case s = 1: Excluded by hypothesis

**What's left (the sorry)**:
- Case 0 < s < 1: Requires showing dirichletEtaReal is real analytic

**Mathematical proof** (Titchmarsh §2.1):
1. η(s) = Σ(-1)^{n-1}/n^s converges for s > 0 (alternating series)
2. (1-2^{1-s})ζ(s) is analytic on {Re(s) > 0}
3. They agree on (1, ∞) ⟹ agree on (0, ∞) by identity principle

**Formalization gap**:
- Need to prove dirichletEtaReal is real analytic via term-by-term differentiation
- Requires showing derivative series Σ(-1)^{n+1}log(n+1)/(n+1)^s converges uniformly on compacts
- Mathlib has `hasDerivAt_tsum` but we need to apply it to alternating series

---

# TRACK S1: Dirichlet Eta

**File**: `RiemannRecognitionGeometry/DirichletEta.lean`  
**Sorries**: 2  
**Difficulty**: Medium  
**Prerequisites**: None

## S1.1 `dirichletEtaReal_one_eq` ✅ COMPLETE

**Statement**:
```lean
theorem dirichletEtaReal_one_eq : dirichletEtaReal 1 = Real.log 2
```

**Status**: ✅ PROVEN

**Proof Strategy Used**:
1. For s > 1: η(s) = (1 - 2^{1-s}) * ζ(s).re (from `zeta_eta_relation_gt_one`)
2. As s → 1⁺: (1 - 2^{1-s}) * ζ(s).re → log(2) (from `tendsto_factor_mul_zeta_at_one`)
3. η is continuous at 1 (from `continuousAt_dirichletEtaReal`)
4. By uniqueness of limits: η(1) = log(2)

**Reference**: Hardy, "A Course of Pure Mathematics" §8.4

---

## S1.2 `identity_principle_zeta_eta_eq` (line 1096)

**Statement**:
```lean
theorem identity_principle_zeta_eta_eq (s : ℝ) (hs_pos : 0 < s) (hs_lt : s < 1) :
    dirichletEtaReal s = (1 - (2 : ℝ)^(1-s)) * (riemannZeta (s : ℂ)).re
```

**Mathematical Content**:
- Both η and (1-2^{1-s})ζ are analytic on {Re(s) > 0, s ≠ 1}
- They agree on (1, ∞) by `zeta_eta_relation_gt_one`
- By Identity Principle: agreement extends to (0, 1)

**Proof Strategy**:
1. Define `dirichletEtaComplex : ℂ → ℂ` extending `dirichletEtaReal`
2. Prove both functions are `AnalyticOnNhd` on the domain
3. Apply `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`
4. Extract real part

**Key Infrastructure**:
```lean
-- Complex extension
noncomputable def dirichletEtaComplex (s : ℂ) : ℂ := 
  if 0 < s.re then lim (atTop.map (etaPartialSumComplex · s)) else 0

-- Analyticity
theorem analytic_dirichletEtaComplex : AnalyticOnNhd ℂ dirichletEtaComplex {s | 0 < s.re}
```

**Reference**: Ahlfors "Complex Analysis" Ch. 4

---

# TRACK S2: Dyadic Intervals

**File**: `RiemannRecognitionGeometry/JohnNirenberg.lean`  
**Sorries**: 2  
**Difficulty**: Easy  
**Prerequisites**: None

## S2.1 `DyadicInterval.trichotomy` (line 576)

**Statement**:
```lean
lemma DyadicInterval.trichotomy (D₁ D₂ : DyadicInterval) :
    Disjoint D₁.toSet D₂.toSet ∨ D₁ = D₂ ∨ D₁.toSet ⊆ D₂.toSet ∨ D₂.toSet ⊆ D₁.toSet
```

**Mathematical Content**:
- Dyadic intervals are nested or disjoint
- Same generation + same index → equal
- Same generation + different index → disjoint (or share boundary)
- Different generation → finer ⊆ coarser (if overlapping)

**Proof Strategy**:
```lean
  rcases Nat.lt_trichotomy D₁.generation D₂.generation with hlt | heq | hgt
  · -- D₁ coarser: if overlap then D₂ ⊆ D₁
    by_cases h : D₂.toSet ∩ D₁.toSet = ∅
    · left; exact Set.disjoint_iff_inter_eq_empty.mpr h
    · right; right; right; exact dyadic_nesting_property D₂ D₁ hlt h
  · -- Same generation
    rcases eq_or_ne D₁.index D₂.index with hidx | hidx
    · right; left; ext <;> simp [heq, hidx]
    · left; exact disjoint_same_gen_diff_idx D₁ D₂ heq hidx
  · -- D₁ finer: symmetric
```

**Key Helper**:
```lean
lemma dyadic_nesting_property (D₁ D₂ : DyadicInterval) 
    (h_gen : D₁.generation > D₂.generation) (h_overlap : D₁.toSet ∩ D₂.toSet ≠ ∅) :
    D₁.toSet ⊆ D₂.toSet
```

---

## S2.2 `DyadicInterval.avg_doubling` (line 681)

**Statement**:
```lean
lemma DyadicInterval.avg_doubling (D : DyadicInterval) (f : ℝ → ℝ) :
    setAverage (|f ·|) D.leftChild.toSet ≤ 2 * setAverage (|f ·|) D.toSet ∧
    setAverage (|f ·|) D.rightChild.toSet ≤ 2 * setAverage (|f ·|) D.toSet
```

**Mathematical Content**:
- avg_child = (μ_child)⁻¹ * ∫_child |f|
- = 2 * μ_parent⁻¹ * ∫_child |f| (since μ_child = μ_parent/2)
- ≤ 2 * μ_parent⁻¹ * ∫_parent |f| (since child ⊆ parent)
- = 2 * avg_parent

**Proof Strategy**:
```lean
  have ⟨hL_meas, hR_meas⟩ := D.child_measure_half
  have hL_sub := D.leftChild_subset
  constructor <;> {
    unfold setAverage
    -- Use hL_meas to rewrite μ(child) = μ(parent)/2
    -- Use MeasureTheory.setIntegral_mono_set for ∫_child ≤ ∫_parent
    sorry
  }
```

**Key Lemma**:
```lean
MeasureTheory.setIntegral_mono_set : IntegrableOn f s μ → 
    (∀ᵐ x ∂μ, 0 ≤ g x) → t ⊆ s → ∫ x in t, g x ∂μ ≤ ∫ x in s, g x ∂μ
```

---

# TRACK S3: CZ Decomposition

**File**: `RiemannRecognitionGeometry/JohnNirenberg.lean`  
**Sorries**: 2  
**Difficulty**: Medium  
**Prerequisites**: Track S2

## S3.1 `czDecomposition_axiom` (line 715)

**Statement**:
```lean
theorem czDecomposition_axiom (f : ℝ → ℝ) (a b : ℝ) (_hab : a < b)
    (_hf_int : IntegrableOn f (Icc a b))
    (t : ℝ) (_ht_pos : t > 0)
    (_ht_above_avg : t > (b - a)⁻¹ * ∫ x in Icc a b, |f x|) :
    ∃ _cz : CZDecomposition f (Icc a b) t, True
```

**Mathematical Content**:
- Dyadic bisection algorithm
- Mark interval as "bad" if average > t
- Stop at maximal bad intervals
- Properties: t < avg(Q_j) ≤ 2t, disjoint, measure ≤ (1/t)∫|f|

**Proof Strategy**:
1. Construct bad intervals recursively via `Nat.strongInductionOn`
2. Use `avg_doubling` for the 2t upper bound
3. Use `trichotomy` for disjointness
4. Chebyshev for measure bound

**Key Construction**:
```lean
def czBadIntervals (f : ℝ → ℝ) (I : Set ℝ) (t : ℝ) : Set DyadicInterval :=
  { D | D.toSet ⊆ I ∧ setAverage (|f ·|) D.toSet > t ∧ 
        ∀ D', D.toSet ⊂ D'.toSet → D'.toSet ⊆ I → setAverage (|f ·|) D'.toSet ≤ t }
```

---

## S3.2 `czDecompFull_exists` (line 765)

**Statement**:
```lean
theorem czDecompFull_exists (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_int : IntegrableOn f (Icc a b)) (t : ℝ) (ht_pos : t > 0)
    (ht_above_avg : t > (b - a)⁻¹ * ∫ x in Icc a b, |f x|) :
    ∃ _cz : CZDecompFull f (Icc a b) t, True
```

**Mathematical Content**:
- Construct good/bad function split from CZ intervals
- goodPart = f outside ⋃Q_j, = avg(f, Q_j) on each Q_j
- badParts_j = (f - avg) · 𝟙_{Q_j}

**Proof Strategy**:
```lean
  obtain ⟨cz, _⟩ := czDecomposition_axiom f a b hab hf_int t ht_pos ht_above_avg
  exact ⟨{
    badIntervals := cz.badIntervals,
    goodPart := fun x => if ∃ D ∈ cz.badIntervals, x ∈ D.toSet 
                         then intervalAverage f D.left D.right else f x,
    badParts := fun D x => (f x - intervalAverage f D.left D.right) * D.toSet.indicator 1 x,
    ...
  }, trivial⟩
```

---

# TRACK S4: Good-λ Inequality

**File**: `RiemannRecognitionGeometry/JohnNirenberg.lean`  
**Sorries**: 2  
**Difficulty**: Hard  
**Prerequisites**: Track S3

## S4.1 `measureBound_superlevelSet` (line 1191)

**Statement**:
```lean
theorem measureBound_superlevelSet (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_int : IntegrableOn f (Icc a b))
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b', a ≤ a' → b' ≤ b → a' < b' → 
      (b' - a')⁻¹ * ∫ x in Icc a' b', |f x - intervalAverage f a' b'| ≤ M)
    (t : ℝ) (ht : t > 2 * M) :
    volume {x ∈ Icc a b | |f x - intervalAverage f a b| > t} ≤ 
    ENNReal.ofReal ((b - a) / 2)
```

**Mathematical Content**:
- Apply CZ at level t - M
- Superlevel set ⊆ ⋃Q_j
- Use BMO + Chebyshev on each Q_j

**Proof Strategy**:
```lean
  have h_cz := czDecomposition_axiom (fun x => |f x - intervalAverage f a b|) a b hab _ (t - M) _ _
  -- The superlevel set {|f - f_I| > t} ⊆ {|f - f_I| > t - M} ⊆ ⋃Q_j
  -- Total measure of ⋃Q_j ≤ (1/(t-M)) * ∫|f - f_I| ≤ M·|I|/(t-M) ≤ |I|/2
```

---

## S4.2 `goodLambda_measure_bound` (line 1253)

**Statement**:
```lean
theorem goodLambda_measure_bound (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_int : IntegrableOn f (Icc a b))
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b', a ≤ a' → b' ≤ b → a' < b' → 
      (b' - a')⁻¹ * ∫ x in Icc a' b', |f x - intervalAverage f a' b'| ≤ M)
    (t : ℝ) (ht : t > 2 * M) :
    volume {x ∈ Icc a b | |f x - intervalAverage f a b| > t} ≤ 
    ENNReal.ofReal ((b - a) / 2)
```

**Mathematical Content**:
- Similar to S4.1 but with explicit constant extraction
- Key: the factor 1/2 from CZ maximality

**Proof Strategy**:
Same as S4.1 - these may be duplicates to consolidate.

---

# TRACK S5: John-Nirenberg Integration

**File**: `RiemannRecognitionGeometry/JohnNirenberg.lean`  
**Sorries**: 2  
**Difficulty**: Medium  
**Prerequisites**: Track S4

## S5.1 `bmo_Lp_bound_proof` (line 1444)

**Statement**:
```lean
theorem bmo_Lp_bound_proof (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_int : IntegrableOn f (Icc a b))
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b', a ≤ a' → b' ≤ b → a' < b' → 
      (b' - a')⁻¹ * ∫ x in Icc a' b', |f x - intervalAverage f a' b'| ≤ M)
    (p : ℝ) (hp : 1 < p) :
    (∫ x in Icc a b, |f x - intervalAverage f a b|^p)^(1/p) ≤ Cp * M * (b - a)^(1/p)
```

**Mathematical Content**:
- Layer-cake formula: ∫|f|^p = p∫₀^∞ t^{p-1} μ{|f|>t} dt
- Apply John-Nirenberg exponential decay
- Integrate: ∫₀^∞ t^{p-1} e^{-ct/M} dt = M^p · Γ(p) / c^p

**Proof Strategy**:
```lean
  have h_decay := johnNirenberg_exp_decay f a b hab M hM_pos h_bmo
  -- Use MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul for layer cake
  -- Bound: ∫ t^{p-1} · C·|I|·e^{-ct/M} dt = C·|I|·M^p·Γ(p)/c^p
```

---

## S5.2 `bmo_Holder_bound_theorem` (line 1517)

**Statement**:
```lean
theorem bmo_Holder_bound_theorem (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_int : IntegrableOn f (Icc a b))
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b', a ≤ a' → b' ≤ b → a' < b' → 
      (b' - a')⁻¹ * ∫ x in Icc a' b', |f x - intervalAverage f a' b'| ≤ M)
    (K : ℝ → ℝ) (hK_int : IntegrableOn K (Icc a b)) :
    |∫ x in Icc a b, K x * (f x - intervalAverage f a b)| ≤ 2 * JN_C1 * M * ∫ x in Icc a b, |K x|
```

**Mathematical Content**:
- Hölder inequality with L^p bound from S5.1
- Take p → ∞ or use p = 2 with conjugate q = 2

**Proof Strategy**:
```lean
  -- Apply Hölder: |∫Kf| ≤ ‖K‖_q · ‖f‖_p
  -- Use bmo_Lp_bound for ‖f‖_p ≤ C·M·|I|^{1/p}
  -- Take p → ∞ or optimize over p
```

---

# Dependency Graph

```
S1 (DirichletEta) ─────────────────────────── Independent
S2 (Dyadic Intervals) ──┬─────────────────── Independent
                        │
S3 (CZ Decomposition) ──┴─── Depends on S2
                        │
S4 (Good-λ) ────────────┴─── Depends on S3
                        │
S5 (JN Integration) ────┴─── Depends on S4
```

---

# Recommended Order

1. **S1 + S2**: Start in parallel (independent)
2. **S3**: After S2 completes
3. **S4**: After S3 completes
4. **S5**: After S4 completes

Or work all 5 tracks simultaneously with dependencies noted.

---

# Success Criteria

- [ ] All 10 sorries eliminated
- [ ] Build passes: `lake build` succeeds
- [ ] No new axioms introduced
- [ ] All proofs use Mathlib API correctly

**Target**: 0 sorries, 9 axioms
