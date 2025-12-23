/-
# Route 3′: Hurwitz / locally-uniform convergence gate (Connes-style approximants)

Several operator-theoretic approaches (e.g. Connes–Consani–Moscovici `arXiv:2511.22755`)
produce a sequence of entire functions (often via regularized determinants / Fourier transforms)
whose zeros lie **exactly on the real axis** in the *spectral parameter* (the variable in which
Riemann’s `Ξ` is written as `Ξ(t) = ξ(1/2 + i t)`). If one can then prove **locally uniform
convergence** of these approximants to the completed target `Ξ`, a classical Hurwitz-type
argument implies the limit is also zero-free off the real axis (inside the critical strip).

Mathlib currently has strong infrastructure for locally uniform limits of holomorphic functions
(`Mathlib.Analysis.Complex.LocallyUniformLimit`) but does not expose a ready-to-use Hurwitz
theorem about **preservation of nonvanishing**. We therefore isolate that analytic fact as a
single named axiom/target, so the Connes Route 3′ pipeline can be expressed cleanly in Lean.
-/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.OrderClosed

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Set Filter
open scoped Real Topology

/-! ## The critical strip in the `t`-variable (`Ξ(t) = ξ(1/2 + i t)`) -/

/-- The open horizontal strip `|Im(t)| < 1/2`. This corresponds to `0 < Re(s) < 1` under `s = 1/2 + i t`. -/
def strip : Set ℂ := {t : ℂ | abs t.im < (1 / 2 : ℝ)}

/-- Upper half of the strip: `0 < Im(t) < 1/2`. -/
def upperStrip : Set ℂ := {t : ℂ | 0 < t.im ∧ t.im < (1 / 2 : ℝ)}

/-- Lower half of the strip: `-1/2 < Im(t) < 0`. -/
def lowerStrip : Set ℂ := {t : ℂ | (- (1 / 2 : ℝ)) < t.im ∧ t.im < 0}

lemma upperStrip_subset_strip : upperStrip ⊆ strip := by
  intro t ht
  have h0 : 0 < t.im := ht.1
  have hhalf : t.im < (1 / 2 : ℝ) := ht.2
  have habs : abs t.im < (1 / 2 : ℝ) := by
    -- since `0 < im`, `abs im = im`
    simpa [abs_of_pos h0] using hhalf
  exact habs

lemma lowerStrip_subset_strip : lowerStrip ⊆ strip := by
  intro t ht
  have hneg : t.im < 0 := ht.2
  have hgt : (- (1 / 2 : ℝ)) < t.im := ht.1
  have habs : abs t.im < (1 / 2 : ℝ) := by
    -- since `im < 0`, `abs im = -im`
    have : -t.im < (1 / 2 : ℝ) := by
      -- from `-1/2 < im` we get `-im < 1/2`
      linarith
    simpa [abs_of_neg hneg] using this
  exact habs

lemma isOpen_strip : IsOpen strip := by
  -- `t ↦ |Im(t)|` is continuous, so `{ |Im(t)| < 1/2 }` is open.
  simpa [strip] using isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

lemma isOpen_upperStrip : IsOpen upperStrip := by
  -- intersection of two open halfspaces for `im`
  have h1 : IsOpen {t : ℂ | 0 < t.im} := isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen {t : ℂ | t.im < (1 / 2 : ℝ)} := isOpen_lt Complex.continuous_im continuous_const
  simpa [upperStrip, Set.setOf_and] using h1.inter h2

lemma isOpen_lowerStrip : IsOpen lowerStrip := by
  have h1 : IsOpen {t : ℂ | (- (1 / 2 : ℝ)) < t.im} := isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen {t : ℂ | t.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  simpa [lowerStrip, Set.setOf_and] using h1.inter h2

private lemma isLinearMap_im : IsLinearMap ℝ (fun z : ℂ => z.im) := by
  refine ⟨?_, ?_⟩
  · intro x y; simp
  · intro a x; simp

lemma isPreconnected_strip : IsPreconnected strip := by
  -- strip is convex (intersection of two halfspaces), hence preconnected
  have h1 : Convex ℝ {t : ℂ | (- (1 / 2 : ℝ)) < t.im} :=
    convex_halfSpace_gt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im (- (1 / 2 : ℝ))
  have h2 : Convex ℝ {t : ℂ | t.im < (1 / 2 : ℝ)} :=
    convex_halfSpace_lt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im (1 / 2 : ℝ)
  have hconv : Convex ℝ strip := by
    -- `|im| < 1/2` is equivalent to `-1/2 < im ∧ im < 1/2`
    have : strip = ({t : ℂ | (- (1 / 2 : ℝ)) < t.im} ∩ {t : ℂ | t.im < (1 / 2 : ℝ)}) := by
      ext t
      constructor
      · intro ht
        have ht' : abs t.im < (1 / 2 : ℝ) := by
          simpa [strip] using ht
        exact (abs_lt.mp ht')
      · rintro ⟨hgt, hlt⟩
        have hgt' : (- (1 / 2 : ℝ)) < t.im := by simpa using hgt
        have hlt' : t.im < (1 / 2 : ℝ) := by simpa using hlt
        exact abs_lt.mpr ⟨hgt', hlt'⟩
    -- rewrite and use convexity of intersection
    rw [this]
    exact h1.inter h2
  exact hconv.isPreconnected

lemma isPreconnected_upperStrip : IsPreconnected upperStrip := by
  have h1 : Convex ℝ {t : ℂ | 0 < t.im} :=
    convex_halfSpace_gt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im 0
  have h2 : Convex ℝ {t : ℂ | t.im < (1 / 2 : ℝ)} :=
    convex_halfSpace_lt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im (1 / 2 : ℝ)
  have : upperStrip = ({t : ℂ | 0 < t.im} ∩ {t : ℂ | t.im < (1 / 2 : ℝ)}) := by
    ext t; simp [upperStrip, and_left_comm, and_assoc, and_comm, Set.setOf_and]
  rw [this]
  exact (h1.inter h2).isPreconnected

lemma isPreconnected_lowerStrip : IsPreconnected lowerStrip := by
  have h1 : Convex ℝ {t : ℂ | (- (1 / 2 : ℝ)) < t.im} :=
    convex_halfSpace_gt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im (- (1 / 2 : ℝ))
  have h2 : Convex ℝ {t : ℂ | t.im < 0} :=
    convex_halfSpace_lt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im 0
  have : lowerStrip = ({t : ℂ | (- (1 / 2 : ℝ)) < t.im} ∩ {t : ℂ | t.im < 0}) := by
    ext t; simp [lowerStrip, and_left_comm, and_assoc, and_comm, Set.setOf_and]
  rw [this]
  exact (h1.inter h2).isPreconnected

/-! ## Zero-free predicates -/

/-- A function is zero-free on a set `U`. -/
def ZeroFreeOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, f z ≠ 0

/--
A function is zero-free off the real axis **inside the critical strip** (`|Im(t)| < 1/2`),
packaged as zero-freeness on the upper and lower halves of the strip.
-/
def ZeroFreeOffRealAxisInStrip (f : ℂ → ℂ) : Prop :=
  ZeroFreeOn f upperStrip ∧ ZeroFreeOn f lowerStrip

/-! ## Hurwitz-style nonvanishing preservation (proved theorem) -/

/--
**Hurwitz nonvanishing principle (proved).**

If `Fₙ` are holomorphic on an open, preconnected set `U`, converge locally uniformly to `f` on `U`,
and each `Fₙ` is zero-free on `U`, then either `f` is identically `0` on `U` or `f` is zero-free on `U`.

We expose the useful “nontrivial ⇒ zero-free” direction as a single named lemma.
-/
theorem hurwitz_zeroFree_of_tendstoLocallyUniformlyOn
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hF : ∀ n : ℕ, DifferentiableOn ℂ (F n) U)
    (hLim : TendstoLocallyUniformlyOn F f atTop U)
    (hZeroFree : ∀ n : ℕ, ZeroFreeOn (F n) U)
    (hNontriv : ∃ z ∈ U, f z ≠ 0) :
    ZeroFreeOn f U := by
  classical
  intro z0 hz0
  -- First, the locally uniform limit of holomorphic functions is holomorphic.
  have hf : DifferentiableOn ℂ f U :=
    hLim.differentiableOn (Eventually.of_forall hF) hUopen
  have hAnalyticOn : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hUopen
  have hAnalyticAt : AnalyticAt ℂ f z0 := hf.analyticAt (hUopen.mem_nhds hz0)
  -- Suppose `f z0 = 0`; we will derive a contradiction.
  intro hf0
  -- Isolated zeros: either `f ≡ 0` near `z0` or `f` is nonzero on a punctured neighborhood.
  have hAlt :
      (∀ᶠ z in 𝓝 z0, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z0, f z ≠ 0 :=
    hAnalyticAt.eventually_eq_zero_or_eventually_ne_zero
  have hPunctured : ∀ᶠ z in 𝓝[≠] z0, f z ≠ 0 := by
    -- The “eventually zero” branch would force `f ≡ 0` on `U`, contradicting `hNontriv`.
    refine hAlt.resolve_left ?_
    intro hEvZero
    have hfreq : (∃ᶠ z in 𝓝[≠] z0, f z = 0) :=
      (hAnalyticAt.frequently_zero_iff_eventually_zero).2 hEvZero
    have hEqOn : EqOn f 0 U :=
      hAnalyticOn.eqOn_zero_of_preconnected_of_frequently_eq_zero hUconn hz0 hfreq
    rcases hNontriv with ⟨z1, hz1U, hz1ne⟩
    have : f z1 = 0 := by simpa using hEqOn hz1U
    exact hz1ne this
  -- Extract a punctured ball on which `f` is nonzero.
  have hPunctured' : ∀ᶠ z in 𝓝 z0, z ≠ z0 → f z ≠ 0 := by
    -- `𝓝[≠] z0` is `𝓝[{z0}ᶜ] z0`.
    simpa [nhdsWithin, Filter.eventually_inf_principal] using
      (eventually_nhdsWithin_iff).1 hPunctured
  rcases (Metric.eventually_nhds_iff_ball).1 hPunctured' with ⟨δ, hδpos, hδ⟩
  -- Also pick a ball whose closure stays inside `U` (since `U` is open).
  rcases (Metric.mem_nhds_iff).1 (hUopen.mem_nhds hz0) with ⟨ε, hεpos, hεU⟩
  -- Choose a radius that is small enough for both constraints.
  let r : ℝ := min (δ / 2) (ε / 2)
  have hrpos : 0 < r := by
    have hδ2 : 0 < δ / 2 := by nlinarith [hδpos]
    have hε2 : 0 < ε / 2 := by nlinarith [hεpos]
    exact lt_min hδ2 hε2
  have hr_lt_δ : r < δ := by
    have h : δ / 2 < δ := by nlinarith
    exact (min_le_left _ _).trans_lt h
  have hr_lt_ε : r < ε := by
    have h : ε / 2 < ε := by nlinarith
    exact (min_le_right _ _).trans_lt h
  have hclosedU : Metric.closedBall z0 r ⊆ U := by
    -- `closedBall z0 r ⊆ ball z0 ε ⊆ U`
    have h1 : Metric.closedBall z0 r ⊆ Metric.ball z0 ε :=
      Metric.closedBall_subset_ball hr_lt_ε
    exact h1.trans hεU
  have hSphereU : Metric.sphere z0 r ⊆ U := (Metric.sphere_subset_closedBall).trans hclosedU
  -- On the boundary sphere, `f` is nonzero by the punctured neighborhood property.
  have hf_ne_on_sphere : ∀ z ∈ Metric.sphere z0 r, f z ≠ 0 := by
    intro z hz
    have hz_ne : z ≠ z0 := by
      have : dist z z0 = r := by simpa [Metric.mem_sphere] using hz
      -- If `z = z0`, then `dist z z0 = 0`, contradicting `r > 0`.
      intro hEq
      have : (0 : ℝ) = r := by simpa [hEq] using this
      exact (ne_of_gt hrpos) this.symm
    have hz_in_ball : z ∈ Metric.ball z0 δ := by
      -- `dist z z0 = r < δ`
      have : dist z z0 = r := by simpa [Metric.mem_sphere] using hz
      exact (Metric.mem_ball.2 (this ▸ hr_lt_δ))
    -- Apply the punctured-ball nonvanishing hypothesis.
    exact hδ z hz_in_ball hz_ne
  -- Get a positive lower bound `m` for `|f|` on the boundary sphere.
  have hsphere_compact : IsCompact (Metric.sphere z0 r) := isCompact_sphere z0 r
  have hcont_abs : ContinuousOn (fun z : ℂ => Complex.abs (f z)) (Metric.sphere z0 r) := by
    have hcont_f : ContinuousOn f (Metric.sphere z0 r) := (hf.continuousOn.mono hSphereU)
    exact Complex.continuous_abs.comp_continuousOn hcont_f
  have hpos_on_sphere : ∀ z ∈ Metric.sphere z0 r, (0 : ℝ) < Complex.abs (f z) := by
    intro z hz
    exact AbsoluteValue.pos Complex.abs (hf_ne_on_sphere z hz)
  obtain ⟨m, hmpos, hmle⟩ :=
    hsphere_compact.exists_forall_le' hcont_abs (a := (0 : ℝ))
      (by intro z hz; exact hpos_on_sphere z hz)
  -- Use locally uniform convergence on the boundary sphere to transfer this lower bound to `F n`.
  have hUnif : TendstoUniformlyOn F f atTop (Metric.sphere z0 r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen).1 hLim (Metric.sphere z0 r) hSphereU hsphere_compact
  have hUnif' : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere z0 r, dist (f z) (F n z) < ε := by
    simpa using (Metric.tendstoUniformlyOn_iff.1 hUnif)
  have hClose : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere z0 r, Complex.abs (F n z) ≥ m / 2 := by
    filter_upwards [hUnif' (m / 2) (by nlinarith [hmpos])] with n hn z hz
    have hmf : m ≤ Complex.abs (f z) := hmle z hz
    have hdist : Complex.abs (f z - F n z) < m / 2 := by
      -- `dist (f z) (F n z) = abs (f z - F n z)`
      simpa [Complex.dist_eq] using (hn z hz)
    -- `‖F n z‖ ≥ ‖f z‖ - ‖f z - F n z‖`
    have htri : Complex.abs (F n z) ≥ Complex.abs (f z) - Complex.abs (f z - F n z) := by
      -- Start from `‖f‖ - ‖F‖ ≤ ‖f - F‖` and rearrange.
      have h := norm_sub_norm_le (f z) (F n z)
      -- rewrite norms as `Complex.abs`
      have h' :
          Complex.abs (f z) - Complex.abs (F n z) ≤ Complex.abs (f z - F n z) := by
        simpa [Complex.norm_eq_abs] using h
      linarith
    have htri' : Complex.abs (F n z) ≥ m - (m / 2) := by
      have hdist_le : Complex.abs (f z - F n z) ≤ m / 2 := le_of_lt hdist
      have : Complex.abs (F n z) ≥ m - (m / 2) := by
        have := le_trans (sub_le_sub_right hmf _) (sub_le_sub_left hdist_le _)
        -- combine `abs(F) ≥ abs(f) - abs(f-F)` with bounds
        linarith [htri, hmf, hdist_le]
      exact this
    -- simplify `m - m/2 = m/2`
    nlinarith
  -- Propagate the boundary lower bound to the center using the maximum modulus principle on `1/F n`.
  have hCenterLower : ∀ᶠ n in atTop, Complex.abs (F n z0) ≥ m / 2 := by
    filter_upwards [hClose] with n hn
    -- Let `g(z) = (F n z)⁻¹`. Apply maximum modulus to bound `|g|` on the disc.
    have hFn_ne : ∀ z ∈ Metric.closedBall z0 r, F n z ≠ 0 := by
      intro z hz
      exact hZeroFree n z (hclosedU hz)
    have hDiffOn_inv : DifferentiableOn ℂ (fun z : ℂ => (F n z)⁻¹) U :=
      (hF n).inv (fun z hz => hZeroFree n z hz)
    have hDiffCont : DiffContOnCl ℂ (fun z : ℂ => (F n z)⁻¹) (Metric.ball z0 r) :=
      hDiffOn_inv.diffContOnCl_ball (c := z0) (R := r) hclosedU
    have hBoundFrontier :
        ∀ z ∈ frontier (Metric.ball z0 r), ‖(F n z)⁻¹‖ ≤ (2 / m) := by
      intro z hz
      -- Use `frontier(ball) ⊆ sphere`.
      have hz' : z ∈ Metric.sphere z0 r :=
        Metric.frontier_ball_subset_sphere (x := z0) (ε := r) hz
      have hlow : Complex.abs (F n z) ≥ m / 2 := hn z hz'
      have hmne : m ≠ 0 := ne_of_gt hmpos
      -- `‖(F n z)⁻¹‖ = 1 / ‖F n z‖ ≤ 2 / m`
      have : ‖(F n z)⁻¹‖ = (Complex.abs (F n z))⁻¹ := by
        -- `‖z⁻¹‖ = ‖z‖⁻¹` in a normed field
        simp
      -- Convert the lower bound on the denominator to an upper bound on its inverse.
      have hInv : (Complex.abs (F n z))⁻¹ ≤ (m / 2)⁻¹ := by
        exact inv_le_inv_of_le (by nlinarith [hlow, hmpos]) hlow
      have : ‖(F n z)⁻¹‖ ≤ (m / 2)⁻¹ := by simpa [this] using hInv
      -- `(m/2)⁻¹ = 2/m` for `m ≠ 0`.
      have hcalc : (m / 2)⁻¹ = (2 / m) := by
        field_simp [hmne]
      simpa [hcalc] using this
    have hBoundCenter :
        ‖(F n z0)⁻¹‖ ≤ (2 / m) := by
      have hz0mem : z0 ∈ closure (Metric.ball z0 r) := by
        -- since `r > 0`, we have `z0 ∈ ball z0 r ⊆ closure (ball z0 r)`.
        have hz0ball : z0 ∈ Metric.ball z0 r := by
          simpa [Metric.mem_ball, dist_self] using hrpos
        exact subset_closure hz0ball
      exact Complex.norm_le_of_forall_mem_frontier_norm_le (hU := Metric.isBounded_ball)
        (hd := hDiffCont) (hC := hBoundFrontier) hz0mem
    -- Turn the bound on `‖(F n z0)⁻¹‖` into a lower bound on `‖F n z0‖`.
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have : Complex.abs (F n z0) ≥ m / 2 := by
      -- If `‖(F n z0)⁻¹‖ ≤ 2/m`, then `‖F n z0‖ ≥ m/2`.
      have hInvNorm : ‖(F n z0)⁻¹‖ = (Complex.abs (F n z0))⁻¹ := by simp
      have hInv_le : (Complex.abs (F n z0))⁻¹ ≤ (2 / m) := by simpa [hInvNorm] using hBoundCenter
      -- Invert both sides (all positive).
      have habs_pos : 0 < Complex.abs (F n z0) :=
        AbsoluteValue.pos Complex.abs (hZeroFree n z0 hz0)
      have hinv_pos : 0 < (Complex.abs (F n z0))⁻¹ := inv_pos.mpr habs_pos
      have hInv_ge : (2 / m)⁻¹ ≤ Complex.abs (F n z0) := by
        -- `inv_anti₀` (order-reversing on positives)
        -- first rewrite `abs` as `inv(inv abs)` to match the lemma.
        rw [← inv_inv (Complex.abs (F n z0))]
        exact inv_anti₀ hinv_pos hInv_le
      have hcalc : (2 / m)⁻¹ = m / 2 := by
        field_simp [hmne]
      -- rewrite and finish
      simpa [hcalc] using hInv_ge
    exact this
  -- Take limits at the center: `abs(F n z0) → abs(f z0)`, so `abs(f z0) ≥ m/2`, contradiction.
  have hT0 : Tendsto (fun n : ℕ => F n z0) atTop (𝓝 (f z0)) :=
    hLim.tendsto_at hz0
  have hTabs : Tendsto (fun n : ℕ => Complex.abs (F n z0)) atTop (𝓝 (Complex.abs (f z0))) :=
    (Complex.continuous_abs.tendsto (f z0)).comp hT0
  have habs_ge : m / 2 ≤ Complex.abs (f z0) :=
    ge_of_tendsto hTabs hCenterLower
  -- But `f z0 = 0` by assumption.
  have : Complex.abs (f z0) = 0 := by simp [hf0]
  have hmhalf_pos : 0 < m / 2 := by nlinarith [hmpos]
  have : False := by
    -- `m/2 ≤ 0` contradicts `0 < m/2`.
    have : m / 2 ≤ 0 := by simpa [this] using habs_ge
    exact not_lt_of_ge this hmhalf_pos
  exact this

/-! ## A packaged Hurwitz gate for “zeros are real (in the strip)” -/

/--
Route 3′ Hurwitz gate (Connes-style):

If we have approximants `F n` that are holomorphic and zero-free on the upper/lower parts
of the strip `|Im(t)| < 1/2`, and they converge locally uniformly to `f` on that strip, then `f`
is also zero-free off the real axis in that strip.

This is the exact “final analytic step” needed for the Connes-style determinant-approximation
strategy once locally uniform convergence is established.
-/
structure HurwitzOffRealAxisInStripGate (f : ℂ → ℂ) where
  F : ℕ → ℂ → ℂ
  holo_upper  : ∀ n, DifferentiableOn ℂ (F n) upperStrip
  holo_lower  : ∀ n, DifferentiableOn ℂ (F n) lowerStrip
  tendsto_strip : TendstoLocallyUniformlyOn F f atTop strip
  zeroFree_upper  : ∀ n, ZeroFreeOn (F n) upperStrip
  zeroFree_lower  : ∀ n, ZeroFreeOn (F n) lowerStrip
  nontriv_upper  : ∃ z ∈ upperStrip, f z ≠ 0
  nontriv_lower  : ∃ z ∈ lowerStrip, f z ≠ 0

namespace HurwitzOffRealAxisInStripGate

variable {f : ℂ → ℂ}

theorem zeroFree_upper_of_gate (H : HurwitzOffRealAxisInStripGate f) : ZeroFreeOn f upperStrip := by
  have hLimU : TendstoLocallyUniformlyOn (F H) f atTop upperStrip :=
    (tendsto_strip H).mono upperStrip_subset_strip
  exact hurwitz_zeroFree_of_tendstoLocallyUniformlyOn
    (hUopen := isOpen_upperStrip)
    (hUconn := isPreconnected_upperStrip)
    (hF := holo_upper H)
    (hLim := hLimU)
    (hZeroFree := zeroFree_upper H)
    (hNontriv := nontriv_upper H)

theorem zeroFree_lower_of_gate (H : HurwitzOffRealAxisInStripGate f) : ZeroFreeOn f lowerStrip := by
  have hLimU : TendstoLocallyUniformlyOn (F H) f atTop lowerStrip :=
    (tendsto_strip H).mono lowerStrip_subset_strip
  exact hurwitz_zeroFree_of_tendstoLocallyUniformlyOn
    (hUopen := isOpen_lowerStrip)
    (hUconn := isPreconnected_lowerStrip)
    (hF := holo_lower H)
    (hLim := hLimU)
    (hZeroFree := zeroFree_lower H)
    (hNontriv := nontriv_lower H)

theorem zeroFree_offRealAxisInStrip (H : HurwitzOffRealAxisInStripGate f) : ZeroFreeOffRealAxisInStrip f :=
  ⟨zeroFree_upper_of_gate H, zeroFree_lower_of_gate H⟩

end HurwitzOffRealAxisInStripGate

end ExplicitFormula
end RiemannRecognitionGeometry
