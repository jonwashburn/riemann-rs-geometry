/-
# Connes–Consani–Moscovici (arXiv:2511.22755) — Section 7 objects (E-map, educated guess `k_λ`)

This module is **not** the CCM proof. Its job is to make the Section 7 “educated guess” objects
*concrete Lean definitions*, and to carve the convergence story (Lemma 7.3 style) into small,
typed lemmas that can later be proved (or instantiated from paper hypotheses).

Design goal: make **M2** (`ConnesMissingStep_kLam_approximates_xiLam`) attackable by supplying:
- a concrete definition of the E-map `E` (paper: `E(f)(u) := u^{1/2} ∑_{n≥1} f(nu)`),
- a canonical definition of `k_λ := E(h_λ)` for a given family `h_λ`,
- small “reduction lemmas” that turn a sup-norm approximation hypothesis on `h_λ` into a
  uniform-on-`[λ⁻¹, λ]` approximation hypothesis on `k_λ`.

We deliberately keep the analytic heavy lifting (summability, tail bounds, prolate-wave estimates)
as **assumption bundles / targets**, not global axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Complex.Basic

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open scoped Real Topology BigOperators
open Filter Set

/-! ## The CCM E-map -/

namespace Connes

/-- The CCM `E`-map (paper Eq. (7.2)):

`E(f)(u) := u^{1/2} * ∑_{n≥1} f(nu)`.

We implement the `n ≥ 1` sum as `∑' n : ℕ, f((n+1)u)`.

Notes:
- In the CCM setting one evaluates `u` on `[λ⁻¹, λ]`, hence eventually `u > 0` and `Real.sqrt u`
  matches the intended `u^{1/2}`.
- We do **not** bake summability into the definition; summability becomes an explicit hypothesis
  in lemmas below.
-/
def E (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ((Real.sqrt u : ℝ) : ℂ) * ∑' n : ℕ, f ((n + 1 : ℕ) * u)

/-- The Section 7 “educated guess” from a given `h`: `k := E(h)`. -/
def kOf (h : ℝ → ℂ) : ℝ → ℂ := fun u => E h u

/-- A family version: given `hLam : λ ↦ h_λ`, define `kLam := λ ↦ E(h_λ)`. -/
def kLamOf (hLam : ℝ → ℝ → ℂ) : ℝ → (ℝ → ℂ) := fun lam => kOf (hLam lam)

@[simp] lemma kOf_def (h : ℝ → ℂ) (u : ℝ) : kOf h u = E h u := rfl
@[simp] lemma kLamOf_def (hLam : ℝ → ℝ → ℂ) (lam u : ℝ) : kLamOf hLam lam u = E (hLam lam) u := rfl

/-! ## Small reduction lemmas (algebraic skeleton) -/

/-- Pointwise difference bound for the E-map (pure algebra).

This is the basic “triangle inequality + pull out `sqrt u`” step that every convergence argument
starts from. It is intentionally stated without attempting to prove summability.
-/
theorem abs_E_sub_le
    (f g : ℝ → ℂ) (u : ℝ)
    (hSum : Summable (fun n : ℕ => Complex.abs (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u)))) :
    Complex.abs (E f u - E g u) ≤
      (Real.sqrt u) * (∑' n : ℕ, Complex.abs (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u))) := by
  -- Expand and apply the triangle inequality for `tsum`.
  classical
  -- Factor out `sqrt u`.
  simp [E, mul_sub, sub_mul, Complex.abs.map_mul, Complex.abs_ofReal, Real.sqrt_sq_eq_abs] at *
  -- The remaining inequality is `‖∑ (a_n)‖ ≤ ∑ ‖a_n‖`.
  -- Use `norm_tsum_le` on `ℂ` (with `‖z‖ = abs z`).
  -- Mathlib lemma name is `norm_tsum_le` in `Topology/Algebra/InfiniteSum`.
  -- We keep this proof lightweight: convert to `‖·‖` and apply `norm_tsum_le`.
  have h1 :
      Complex.abs (∑' n : ℕ, (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u))) ≤
        ∑' n : ℕ, Complex.abs (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u)) := by
    simpa [Complex.abs] using
      (norm_tsum_le (f := fun n : ℕ => (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u))) ) hSum
  -- Reinsert `sqrt u` (as a nonnegative real scalar).
  have hsqrt : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  -- `mul_le_mul_of_nonneg_left` on `ℝ`.
  -- `Complex.abs (E f u - E g u)` has already been simp-rewritten to `Real.sqrt u * abs(tsum ...)` above.
  -- So we just finish by monotonicity of multiplication by a nonnegative real.
  exact mul_le_mul_of_nonneg_left h1 hsqrt

/-!
## “Lemma 7.3 style” decomposition: finite window + tail

The CCM E-map is defined by a `tsum` over `n ≥ 1`. To make convergence proofs modular, we split
that `tsum` into:

- a **finite window part** (`n < N`), which can be controlled using a sup bound on `[-λ,λ]` once we
  ensure `(n+1)u ∈ [-λ,λ]`,
- a **tail part** (`n ≥ N`), controlled by a separate tail hypothesis (Schwartz decay, etc.).

This is the standard shape used in CCM’s Section 7.
-/

/-- Split the `n ≥ 1` series `∑_{n≥1} f(nu)` (implemented as `∑' n, f((n+1)u)`) into
a finite sum over `n < N` and a tail starting at `N`. -/
theorem tsum_succ_mul_eq_sum_range_add_tsum_nat_add
    (f : ℝ → ℂ) (u : ℝ) (N : ℕ)
    (hSum : Summable (fun n : ℕ => f ((n + 1 : ℕ) * u))) :
    (∑' n : ℕ, f ((n + 1 : ℕ) * u)) =
      (∑ i in Finset.range N, f ((i + 1 : ℕ) * u)) + ∑' n : ℕ, f ((n + N + 1 : ℕ) * u) := by
  -- This is a standard `tsum` decomposition on `ℕ`, applied to the shifted sequence `n ↦ f((n+1)u)`.
  have h :=
    (sum_add_tsum_nat_add (f := fun n : ℕ => f ((n + 1 : ℕ) * u)) N hSum).symm
  -- The tail term is `n ↦ f(((n+N)+1)u)`, which we rewrite as `n ↦ f((n+N+1)u)`.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_assoc] using h

/-- Corresponding split for `E f u` (just multiply the split `tsum` by `√u`). -/
theorem E_eq_sum_range_add_tsum_nat_add
    (f : ℝ → ℂ) (u : ℝ) (N : ℕ)
    (hSum : Summable (fun n : ℕ => f ((n + 1 : ℕ) * u))) :
    E f u =
      ((Real.sqrt u : ℝ) : ℂ) *
        ((∑ i in Finset.range N, f ((i + 1 : ℕ) * u)) + ∑' n : ℕ, f ((n + N + 1 : ℕ) * u)) := by
  simp [E, tsum_succ_mul_eq_sum_range_add_tsum_nat_add (f := f) (u := u) (N := N) hSum]

private lemma mem_Icc_neg_lam_lam_of_mul_le
    {lam u : ℝ} {N : ℕ} (hlam : 0 ≤ lam) (hu : 0 ≤ u) (hNu : (N : ℝ) * u ≤ lam) :
    ∀ i : ℕ, i < N → ((i + 1 : ℕ) * u) ∈ Set.Icc (-lam) lam := by
  intro i hi
  have h0 : 0 ≤ ((i + 1 : ℕ) * u) := by
    -- `(i+1) ≥ 0` and `u ≥ 0`
    simpa using (mul_nonneg (Nat.cast_nonneg (i + 1)) hu)
  have hlow : -lam ≤ ((i + 1 : ℕ) * u) := by
    exact (neg_nonpos.mpr hlam).trans h0
  have hi_le : (i + 1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hi)
  have hhigh : ((i + 1 : ℕ) * u) ≤ lam := by
    -- `(i+1)u ≤ Nu ≤ lam`
    have : ((i + 1 : ℝ) * u) ≤ (N : ℝ) * u := mul_le_mul_of_nonneg_right hi_le hu
    exact this.trans hNu
  exact ⟨hlow, hhigh⟩

/-- Sup bound on `[-λ,λ]` controls the finite “window part” of the E-map difference. -/
theorem sum_range_abs_sub_le_mul_of_sup
    {hLam : ℝ → ℝ → ℂ} {h : ℝ → ℂ}
    {lam u : ℝ} {N : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hSup : ∀ x : ℝ, x ∈ Set.Icc (-lam) lam → Complex.abs (hLam lam x - h x) ≤ δ)
    (hWin : ∀ i : ℕ, i < N → ((i + 1 : ℕ) * u) ∈ Set.Icc (-lam) lam) :
    (∑ i in Finset.range N, Complex.abs (hLam lam ((i + 1 : ℕ) * u) - h ((i + 1 : ℕ) * u)))
      ≤ (N : ℝ) * δ := by
  classical
  have hterm : ∀ i ∈ Finset.range N,
      Complex.abs (hLam lam ((i + 1 : ℕ) * u) - h ((i + 1 : ℕ) * u)) ≤ δ := by
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    exact hSup _ (hWin i hi')
  -- Sum each term ≤ δ, so the whole sum ≤ N*δ.
  calc
    (∑ i in Finset.range N,
        Complex.abs (hLam lam ((i + 1 : ℕ) * u) - h ((i + 1 : ℕ) * u)))
        ≤ ∑ _i in Finset.range N, δ := by
            exact Finset.sum_le_sum hterm
    _ = (N : ℝ) * δ := by simp [hδ]

/-- **Main window+tail bound** (E-map form):

If
- `|h_λ - h| ≤ δ` on `[-λ,λ]`,
- the first `N` E-terms satisfy `(n+1)u ≤ λ` (so they lie in the window),
- and the tail absolute sum is ≤ `T`,

then `|E(h_λ)(u) - E(h)(u)| ≤ √u * (N·δ + T)`.
-/
theorem abs_E_sub_le_window_add_tail
    (hLam : ℝ → ℝ → ℂ) (h : ℝ → ℂ)
    (lam u : ℝ) (N : ℕ) (δ T : ℝ)
    (hlam : 0 ≤ lam) (hu : 0 ≤ u) (hNu : (N : ℝ) * u ≤ lam)
    (hδ : 0 ≤ δ)
    (hSup : ∀ x : ℝ, x ∈ Set.Icc (-lam) lam → Complex.abs (hLam lam x - h x) ≤ δ)
    (hSum : Summable (fun n : ℕ =>
      Complex.abs (hLam lam ((n + 1 : ℕ) * u) - h ((n + 1 : ℕ) * u))))
    (hTail :
      (∑' n : ℕ,
        Complex.abs (hLam lam ((n + N + 1 : ℕ) * u) - h ((n + N + 1 : ℕ) * u))) ≤ T) :
    Complex.abs (E (hLam lam) u - E h u) ≤ (Real.sqrt u) * ((N : ℝ) * δ + T) := by
  -- Start from the global bound by the full absolute-sum.
  have h0 :=
    abs_E_sub_le (f := hLam lam) (g := h) (u := u) hSum
  -- Decompose the absolute-sum into window + tail.
  let d : ℕ → ℝ := fun n : ℕ => Complex.abs (hLam lam ((n + 1 : ℕ) * u) - h ((n + 1 : ℕ) * u))
  have hdecomp : (∑' n : ℕ, d n) = (∑ i in Finset.range N, d i) + ∑' n : ℕ, d (n + N) := by
    -- Apply the standard `tsum` decomposition on `ℕ`.
    -- (The tail is summable since `d` is summable.)
    simpa [d, Nat.add_assoc, add_assoc] using (sum_add_tsum_nat_add (f := d) N hSum).symm
  have hWinMem : ∀ i : ℕ, i < N → ((i + 1 : ℕ) * u) ∈ Set.Icc (-lam) lam :=
    mem_Icc_neg_lam_lam_of_mul_le (lam := lam) (u := u) (N := N) hlam hu hNu
  have hwindow_sum :
      (∑ i in Finset.range N, d i) ≤ (N : ℝ) * δ := by
    -- Reduce to the sup bound on `[-lam, lam]`.
    simpa [d] using
      (sum_range_abs_sub_le_mul_of_sup (hLam := hLam) (h := h) (lam := lam) (u := u) (N := N)
        (δ := δ) hδ hSup hWinMem)
  have htail_sum : (∑' n : ℕ, d (n + N)) ≤ T := by
    -- Rewrite `d (n+N)` to match the given tail hypothesis.
    simpa [d, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_assoc] using hTail
  have hsum_le : (∑' n : ℕ, d n) ≤ (N : ℝ) * δ + T := by
    -- Use the decomposition and combine the two bounds.
    -- `tsum d = window + tail`.
    rw [hdecomp]
    exact add_le_add hwindow_sum htail_sum
  -- Finish by monotonicity of multiplication by `√u` (nonnegative).
  have hsqrt : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  -- `h0` is `|E(...) - E(...)| ≤ √u * (tsum d)`; now bound `tsum d`.
  exact le_trans h0 (mul_le_mul_of_nonneg_left hsum_le hsqrt)

/-! ## Canonical choice of the window length `N(λ,u)` -/

/-- Canonical cutoff for the “window part”: `N(λ,u) := ⌊λ / u⌋₊`.

This ensures `(N(λ,u) : ℝ) * u ≤ λ` whenever `0 ≤ λ` and `0 < u`. -/
def Nwin (lam u : ℝ) : ℕ :=
  Nat.floor (lam / u)

@[simp] lemma Nwin_def (lam u : ℝ) : Nwin lam u = Nat.floor (lam / u) := rfl

/-- The canonical cutoff satisfies `(Nwin λ u) * u ≤ λ` when `λ ≥ 0` and `u > 0`. -/
theorem Nwin_mul_le (lam u : ℝ) (hlam : 0 ≤ lam) (hu : 0 < u) :
    ((Nwin lam u : ℝ) * u) ≤ lam := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hnonneg : 0 ≤ lam / u := div_nonneg hlam hu.le
  have hfloor : ((Nwin lam u : ℝ)) ≤ lam / u := by
    -- `Nat.floor_le` is the fundamental floor inequality.
    simpa [Nwin] using (Nat.floor_le (a := (lam / u)) hnonneg)
  have hmul : ((Nwin lam u : ℝ) * u) ≤ (lam / u) * u :=
    mul_le_mul_of_nonneg_right hfloor hu.le
  -- simplify RHS: `(lam/u)*u = lam`
  simpa [div_eq_mul_inv, mul_assoc, hu0] using (hmul.trans_eq (by
    -- `(lam * u⁻¹) * u = lam`
    simp [div_eq_mul_inv, mul_assoc, hu0]))

/-- Window membership is automatic on the semilocal interval `u ∈ [λ⁻¹, λ]` (for `λ > 0`):
for `i < Nwin λ u`, we have `((i+1)u) ∈ [-λ, λ]`. -/
theorem mem_Icc_neg_lam_lam_of_mem_semilocal
    {lam u : ℝ} (hlam : 0 < lam) (hu : u ∈ Set.Icc (lam⁻¹) lam) :
    ∀ i : ℕ, i < Nwin lam u → ((i + 1 : ℕ) * u) ∈ Set.Icc (-lam) lam := by
  have hlam0 : 0 ≤ lam := hlam.le
  have hu0 : 0 < u := by
    -- from `lam⁻¹ ≤ u` and `lam⁻¹ > 0`
    have : 0 < lam⁻¹ := inv_pos.mpr hlam
    exact lt_of_lt_of_le this hu.1
  have hNu : ((Nwin lam u : ℝ) * u) ≤ lam := Nwin_mul_le lam u hlam0 hu0
  -- use the generic helper with `N := Nwin lam u`
  exact mem_Icc_neg_lam_lam_of_mul_le (lam := lam) (u := u) (N := Nwin lam u) hlam0 hu0.le hNu

/-- **Window+tail bound with canonical cutoff** `N = Nwin λ u`.

This is the “next-step” lemma: once you have (i) a sup bound on `[-λ,λ]` and (ii) a tail bound
starting at `Nwin λ u`, the window condition is automatic for `u ∈ [λ⁻¹,λ]`.
-/
theorem abs_E_sub_le_window_add_tail_Nwin
    (hLam : ℝ → ℝ → ℂ) (h : ℝ → ℂ)
    {lam u : ℝ} (hlam : 0 < lam) (hu : u ∈ Set.Icc (lam⁻¹) lam)
    (δ T : ℝ)
    (hδ : 0 ≤ δ)
    (hSup : ∀ x : ℝ, x ∈ Set.Icc (-lam) lam → Complex.abs (hLam lam x - h x) ≤ δ)
    (hSum : Summable (fun n : ℕ =>
      Complex.abs (hLam lam ((n + 1 : ℕ) * u) - h ((n + 1 : ℕ) * u))))
    (hTail :
      (∑' n : ℕ,
        Complex.abs (hLam lam ((n + Nwin lam u + 1 : ℕ) * u) - h ((n + Nwin lam u + 1 : ℕ) * u)))
        ≤ T) :
    Complex.abs (E (hLam lam) u - E h u) ≤ (Real.sqrt u) * ((Nwin lam u : ℝ) * δ + T) := by
  have hlam0 : 0 ≤ lam := hlam.le
  have hu0 : 0 < u := by
    have : 0 < lam⁻¹ := inv_pos.mpr hlam
    exact lt_of_lt_of_le this hu.1
  have hNu : ((Nwin lam u : ℝ) * u) ≤ lam := Nwin_mul_le lam u hlam0 hu0
  -- Apply the generic window+tail lemma with `N = Nwin lam u`.
  exact abs_E_sub_le_window_add_tail (hLam := hLam) (h := h)
    (lam := lam) (u := u) (N := Nwin lam u) (δ := δ) (T := T)
    (hlam := hlam0) (hu := hu0.le) (hNu := hNu)
    (hδ := hδ) (hSup := hSup) (hSum := hSum) (hTail := hTail)

/-!
## Corollary: tail envelope `T(λ)` uniform in `u ∈ [λ⁻¹,λ]`

For M2 we ultimately want a bound of the form

`∀ u ∈ [λ⁻¹,λ], |k_λ(u) - …| ≤ ε(λ)`

where the right-hand side depends only on `λ`. The lemma below packages the *tail* contribution
as a function `T : ℝ → ℝ` depending only on `λ`, uniformly in `u ∈ [λ⁻¹,λ]`, and produces such an
`ε(λ)` for the E-map comparison.
-/

/-- For `u ∈ [λ⁻¹,λ]` (and `λ>0`), we have the universal bound `Nwin(λ,u) ≤ λ^2`. -/
theorem Nwin_le_sq_of_mem_semilocal {lam u : ℝ} (hlam : 0 < lam) (hu : u ∈ Set.Icc (lam⁻¹) lam) :
    (Nwin lam u : ℝ) ≤ lam ^ 2 := by
  have hlam0 : 0 ≤ lam := hlam.le
  have hu0 : 0 < u := by
    have : 0 < lam⁻¹ := inv_pos.mpr hlam
    exact lt_of_lt_of_le this hu.1
  have hnonneg : 0 ≤ lam / u := div_nonneg hlam0 hu0.le
  have hfloor : (Nwin lam u : ℝ) ≤ lam / u := by
    simpa [Nwin] using (Nat.floor_le (a := lam / u) hnonneg)
  have hdiv_le : lam / u ≤ lam ^ 2 := by
    -- From `u ≥ λ⁻¹` we get `u⁻¹ ≤ λ`, hence `λ/u = λ*u⁻¹ ≤ λ^2`.
    have hu_inv : u⁻¹ ≤ lam := by
      have hpos_inv : 0 < lam⁻¹ := inv_pos.mpr hlam
      have := inv_le_inv_of_le hpos_inv hu.1
      simpa [inv_inv] using this
    have : lam * u⁻¹ ≤ lam * lam := mul_le_mul_of_nonneg_left hu_inv hlam0
    simpa [div_eq_mul_inv, pow_two, mul_assoc] using this
  exact hfloor.trans hdiv_le

/-- **Uniform-in-`u` bound on `[λ⁻¹,λ]`**, given a tail envelope `T(λ)` uniform in `u`.

This produces an explicit `ε(λ)` depending only on `λ`:
`ε(λ) = √λ * (λ^2 * δ + T(λ))`.
-/
theorem abs_E_sub_le_uniform_semilocal_of_tailEnvelope
    (hLam : ℝ → ℝ → ℂ) (h : ℝ → ℂ)
    {lam : ℝ} (hlam : 0 < lam)
    (δ : ℝ) (T : ℝ → ℝ)
    (hδ : 0 ≤ δ) (hT : 0 ≤ T lam)
    (hSup : ∀ x : ℝ, x ∈ Set.Icc (-lam) lam → Complex.abs (hLam lam x - h x) ≤ δ)
    (hSum : ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
      Summable (fun n : ℕ => Complex.abs (hLam lam ((n + 1 : ℕ) * u) - h ((n + 1 : ℕ) * u))))
    (hTail :
      ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
        (∑' n : ℕ,
          Complex.abs (hLam lam ((n + Nwin lam u + 1 : ℕ) * u) - h ((n + Nwin lam u + 1 : ℕ) * u)))
          ≤ T lam) :
    ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
      Complex.abs (E (hLam lam) u - E h u) ≤
        (Real.sqrt lam) * ((lam ^ 2) * δ + T lam) := by
  intro u hu
  have hbase :=
    abs_E_sub_le_window_add_tail_Nwin (hLam := hLam) (h := h) (hlam := hlam) (hu := hu)
      (δ := δ) (T := T lam) hδ hSup (hSum u hu) (hTail u hu)
  have hsqrt_le : Real.sqrt u ≤ Real.sqrt lam :=
    Real.sqrt_le_sqrt hu.2
  have hN_le : (Nwin lam u : ℝ) ≤ lam ^ 2 :=
    Nwin_le_sq_of_mem_semilocal (lam := lam) (u := u) hlam hu
  have hfactor_le : (Nwin lam u : ℝ) * δ + T lam ≤ (lam ^ 2) * δ + T lam := by
    have : (Nwin lam u : ℝ) * δ ≤ (lam ^ 2) * δ := mul_le_mul_of_nonneg_right hN_le hδ
    exact add_le_add_right this (T lam)
  have hnonneg_factor : 0 ≤ (lam ^ 2) * δ + T lam := by
    have hlam2 : 0 ≤ lam ^ 2 := by positivity
    exact add_nonneg (mul_nonneg hlam2 hδ) hT
  have h1 :
      Complex.abs (E (hLam lam) u - E h u) ≤
        (Real.sqrt u) * ((lam ^ 2) * δ + T lam) :=
    le_trans hbase (mul_le_mul_of_nonneg_left hfactor_le (Real.sqrt_nonneg u))
  have h2 :
      (Real.sqrt u) * ((lam ^ 2) * δ + T lam) ≤
        (Real.sqrt lam) * ((lam ^ 2) * δ + T lam) :=
    mul_le_mul_of_nonneg_right hsqrt_le hnonneg_factor
  exact le_trans h1 h2

/-- Companion lemma to `abs_E_sub_le_uniform_semilocal_of_tailEnvelope`, stated directly for
`kLamOf` / `kOf` (no mention of `E`). -/
theorem abs_kLam_sub_k_le_uniform_semilocal_of_tailEnvelope
    (hLam : ℝ → ℝ → ℂ) (h : ℝ → ℂ)
    {lam : ℝ} (hlam : 0 < lam)
    (δ : ℝ) (T : ℝ → ℝ)
    (hδ : 0 ≤ δ) (hT : 0 ≤ T lam)
    (hSup : ∀ x : ℝ, x ∈ Set.Icc (-lam) lam → Complex.abs (hLam lam x - h x) ≤ δ)
    (hSum : ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
      Summable (fun n : ℕ => Complex.abs (hLam lam ((n + 1 : ℕ) * u) - h ((n + 1 : ℕ) * u))))
    (hTail :
      ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
        (∑' n : ℕ,
          Complex.abs (hLam lam ((n + Nwin lam u + 1 : ℕ) * u) - h ((n + Nwin lam u + 1 : ℕ) * u)))
          ≤ T lam) :
    ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
      Complex.abs (kLamOf hLam lam u - kOf h u) ≤
        (Real.sqrt lam) * ((lam ^ 2) * δ + T lam) := by
  intro u hu
  simpa [kLamOf, kOf] using
    (abs_E_sub_le_uniform_semilocal_of_tailEnvelope (hLam := hLam) (h := h) (lam := lam)
      (hlam := hlam) (δ := δ) (T := T) (hδ := hδ) (hT := hT)
      (hSup := hSup) (hSum := hSum) (hTail := hTail) u hu)

/-- Variant of `abs_kLam_sub_k_le_uniform_semilocal_of_tailEnvelope` where the window error is a
function `δ(λ)` (paper-style `O(λ⁻²)`). -/
theorem abs_kLam_sub_k_le_uniform_semilocal_of_tailEnvelope_delta
    (hLam : ℝ → ℝ → ℂ) (h : ℝ → ℂ)
    {lam : ℝ} (hlam : 0 < lam)
    (δ : ℝ → ℝ) (T : ℝ → ℝ)
    (hδ : 0 ≤ δ lam) (hT : 0 ≤ T lam)
    (hSup : ∀ x : ℝ, x ∈ Set.Icc (-lam) lam → Complex.abs (hLam lam x - h x) ≤ δ lam)
    (hSum : ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
      Summable (fun n : ℕ => Complex.abs (hLam lam ((n + 1 : ℕ) * u) - h ((n + 1 : ℕ) * u))))
    (hTail :
      ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
        (∑' n : ℕ,
          Complex.abs (hLam lam ((n + Nwin lam u + 1 : ℕ) * u) - h ((n + Nwin lam u + 1 : ℕ) * u)))
          ≤ T lam) :
    ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
      Complex.abs (kLamOf hLam lam u - kOf h u) ≤
        (Real.sqrt lam) * ((lam ^ 2) * (δ lam) + T lam) := by
  -- Just instantiate the constant-`δ` lemma with `δ := δ lam`.
  simpa [mul_assoc] using
    (abs_kLam_sub_k_le_uniform_semilocal_of_tailEnvelope (hLam := hLam) (h := h) (lam := lam)
      (hlam := hlam) (δ := δ lam) (T := T) (hδ := hδ) (hT := hT)
      (hSup := hSup) (hSum := hSum) (hTail := hTail))

/-!
## Section 7 “Lemma 7.3 style” convergence scaffolding

The paper’s Lemma 7.3 uses a **sup-norm approximation** for `h_λ` on `[-λ, λ]` with rate `O(λ⁻²)`
to deduce uniform convergence (after Fourier transform) on closed substrips.

Before we touch Fourier transforms, we isolate the purely *E-map* part:

> if `h_λ ≈ h` (in a usable quantitative sense), then `k_λ = E(h_λ)` is uniformly close to `k = E(h)`
> on the semilocal interval `[λ⁻¹, λ]`.

We encode exactly what hypotheses are needed to make that argument go through, without committing
to a specific prolate-wave construction.
-/

/-- Quantitative “Section 7” hypothesis: `h_λ` approximates `h` on `[-λ, λ]` in sup norm.

This is the direct formalization of the paper’s `δ(λ) := max_{x∈[-λ,λ]} |h_λ(x)-h(x)|` control.
-/
structure SupApproxOnSymmInterval (hLam : ℝ → ℝ → ℂ) (h : ℝ → ℂ) where
  δ : ℝ → ℝ
  bound :
    ∀ᶠ lam : ℝ in atTop,
      ∀ x : ℝ, x ∈ Set.Icc (-lam) lam → Complex.abs (hLam lam x - h x) ≤ δ lam

/-- A tail-control hypothesis for the E-map.

This packages whatever decay/summability estimates you have on the `n`-sum defining `E`.
We keep this flexible: different implementations of `h_λ` will supply different tail bounds.

The intent is: for `u ∈ [λ⁻¹, λ]`, the tail `∑_{n>N(λ,u)} |h_λ((n+1)u)-h((n+1)u)|` is small.
-/
structure EMapTailControl (hLam : ℝ → ℝ → ℂ) (h : ℝ → ℂ) where
  tail : ℝ → ℝ
  tail_tendsto0 : Tendsto tail atTop (nhds 0)
  bound :
    ∀ᶠ lam : ℝ in atTop,
      ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
        Complex.abs (E (hLam lam) u - E h u) ≤ tail lam

/-- **Core Section 7 output (E-map form):**
uniform-on-`[λ⁻¹,λ]` approximation of `k_λ := E(h_λ)` by `k := E(h)` with vanishing error.

This is the exact shape you want in order to later compare `k_λ` to the true ground state `ξ_λ`
(M2), or to feed a Fourier-transform convergence statement.
-/
theorem kLam_uniform_approx_of_tailControl
    {hLam : ℝ → ℝ → ℂ} {h : ℝ → ℂ}
    (T : EMapTailControl hLam h) :
    ∀ᶠ lam : ℝ in atTop,
      ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
        Complex.abs (kLamOf hLam lam u - kOf h u) ≤ T.tail lam := by
  -- This is definitional: `kLamOf = E ∘ hLam` and `kOf = E h`.
  filter_upwards [T.bound] with lam hlam u hu
  simpa [kLamOf, kOf] using hlam u hu

end Connes

end ExplicitFormula
end RiemannRecognitionGeometry
