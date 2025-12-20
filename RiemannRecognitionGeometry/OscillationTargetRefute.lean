import RiemannRecognitionGeometry.Assumptions
import RiemannRecognitionGeometry.FeffermanStein

noncomputable section

namespace RiemannRecognitionGeometry

/-!
## Refuting `OscillationTarget` from any linear-in-length mean oscillation lower bound

This file is part of the “prove it false” workflow:

`OscillationTarget` is a *global* BMO smallness claim about `logAbsXi`.

To prove it false, it suffices to produce **any** quantitative lower bound of the form

`meanOscillation logAbsXi (-L) L ≥ c * L`

for some fixed `c > 0` and all sufficiently large `L`.  Once you have this, no finite BMO bound can
exist.

This file packages that reduction as a reusable lemma: it turns a drift/oscillation witness into
`¬ OscillationTarget`.
-/

namespace OscillationTargetRefute

open Real

/-!
### Eventual linear growth

For refuting global BMO, we only need **eventual** linear growth (for large `L`), not a bound that
holds all the way down to tiny intervals.
-/

def EventuallyLinearGrowthMeanOscillation (f : ℝ → ℝ) : Prop :=
  ∃ c L0 : ℝ, 0 < c ∧ 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → c * L ≤ meanOscillation f (-L) L

theorem not_inBMOWithBound_of_eventuallyLinearGrowth {f : ℝ → ℝ}
    (h : EventuallyLinearGrowthMeanOscillation f) (M : ℝ) :
    ¬ InBMOWithBound f M := by
  intro hBMO
  rcases h with ⟨c, L0, hc_pos, hL0_pos, hlower⟩
  -- pick `L := max L0 (2*M/c)` so that:
  -- - `L ≥ L0` (so the lower bound applies), and
  -- - `c*L ≥ 2M > M`.
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  let L : ℝ := max L0 ((2 * M) / c)
  have hL_pos : 0 < L := by
    -- note: `InBMOWithBound` includes `0 < M`
    have hM_pos : 0 < M := hBMO.1
    have : 0 < (2 * M) := by nlinarith
    -- divide by positive `c`
    have : 0 < (2 * M) / c := by
      exact div_pos this hc_pos
    have : 0 < max L0 ((2 * M) / c) := lt_of_lt_of_le this (le_max_right _ _)
    simpa [L] using this
  have hlt : (-L : ℝ) < L := neg_lt_self hL_pos
  have h_upper : meanOscillation f (-L) L ≤ M := hBMO.2 (-L) L hlt
  have h_lower : c * L ≤ meanOscillation f (-L) L := hlower L (le_max_left _ _)
  have h_big : M < c * L := by
    -- since `L ≥ 2M/c`, we have `c*L ≥ 2M > M`
    have hL_ge : (2 * M) / c ≤ L := le_trans (le_max_right _ _) (le_rfl)
    have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
    have hmul : c * ((2 * M) / c) ≤ c * L := by
      exact mul_le_mul_of_nonneg_left hL_ge hc_nonneg
    have h_eq : c * ((2 * M) / c) = 2 * M := by
      field_simp [hc_ne]
    have : 2 * M ≤ c * L := by simpa [h_eq] using hmul
    nlinarith [this, hBMO.1]
  exact (not_lt_of_ge (le_trans h_lower h_upper) h_big)

theorem not_OscillationTarget_of_eventuallyLinearGrowth
    (h : EventuallyLinearGrowthMeanOscillation logAbsXi) :
    ¬ OscillationTarget := by
  intro hT
  rcases hT with ⟨M, hBMO, _hMle⟩
  exact not_inBMOWithBound_of_eventuallyLinearGrowth (f := logAbsXi) h M hBMO

end OscillationTargetRefute
end RiemannRecognitionGeometry
