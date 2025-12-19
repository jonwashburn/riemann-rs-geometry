# Current Proof Status

## Current status (2025-12-18)

- **Build**: `lake build` succeeds.
- **`sorry` count**: **0** across the entire Lean codebase (verified via grep).
- **Axiom count**: **22 explicit axioms** across 12 files:
  - ExplicitFormula track: 11 axioms (Weil transform, Fourier inversion, outer/Schur bridges, wedge closure, etc.)
  - RG spine: 8 axioms (CZ/JN infrastructure, identity principle, BMO→Carleson embedding)
  - Port track: 0 axioms (all assumptions are bundled as hypothesis structures, not `axiom` declarations)
- **Recognition Geometry (RG) track** (`RiemannRecognitionGeometry/Main.lean`):
  - Core RG development has **0 `sorry`** in `RiemannRecognitionGeometry/Axioms.lean`.
  - The main theorem is explicitly **conditional** on:
    - `OscillationTarget` / `InBMOWithBound logAbsXi M ∧ M ≤ C_tail`
    - `ClassicalAnalysisAssumptions` (Green/CR bounds + ζ≠0 on (0,1))
    - `RGAssumptions.j_carleson_energy_axiom_statement` (RG bottleneck)
- **Route 3 / ExplicitFormula track**: see `ROUTE3_DRIVER.md` for the live assumption ledger and remaining **axioms / hypothesis bundles** (Fourier inversion, wedge closure, splice identity, Cayley/Schur bridge packaging, etc.). The `ExplicitFormula/*` subtree is now `sorry`-free (the gaps are explicit assumptions).
- **Reality integration**: see `REALITY_PORT_PLAN.md` for the statement alignment with
  `/Users/jonathanwashburn/Projects/reality/IndisputableMonolith/RH/HardyDirichlet/*.lean.disabled`.
  - **Note**: those `reality` files are blueprint scaffolds (they contain `sorry`/axiom placeholders for
    `standardWindow`, `Green_pairing`, `window_energy_bound`, Fefferman–Stein, VK→Carleson, etc.), so the remaining
    CR/Green work here is not a direct “proof copy” — it’s new formalization or explicit assumption targets.
- **Port scaffold (compiled)**: added `RiemannRecognitionGeometry/Port/{HardyDirichletCarleson,HardyDirichletCRGreen,SkewHarmGate}.lean`
  to mirror the Hardy/Dirichlet blueprint statement-shapes inside this repo.
  - **Note**: `Port/HardyDirichletCRGreen.lean` is currently **cofactor-specific** (it targets
    `rgCofactorPhaseAngle`). The xi-side uses the separate targets `Port.XiCRGreenAssumptions*`.
- **Port step (compiled)**: added `RiemannRecognitionGeometry/Port/WeierstrassTailBound.lean`, proving the RG tail bound
  from the Hardy/Dirichlet-style interfaces (Carleson budget + CR/Green) and the √|I| cancellation.
- **Port step (compiled)**: added `RiemannRecognitionGeometry/Port/CofactorEnergy.lean`, defining a concrete candidate
  cofactor energy functional `cofactorEbox` to use as `Ebox` in the Hardy/Dirichlet interfaces.
- **Port step (compiled)**: added `RiemannRecognitionGeometry/Port/CofactorCarlesonBudget.lean`, discharging
  `HardyDirichletCarlesonBudget cofactorEbox_poisson` using the existing Fefferman–Stein axiom.
- **Port step (compiled)**: added `RiemannRecognitionGeometry/Port/CofactorTailBound.lean`, deriving an RG-style tail bound
  for `Ebox := cofactorEbox_poisson`. It now exposes variants depending on either an explicit
  `HardyDirichletCRGreen cofactorEbox_poisson` or the energy-based `Port.CofactorCRGreenAssumptions` bundle, while
  keeping the original `ClassicalAnalysisAssumptions`-based theorem as a compatibility wrapper.
- **Port step (compiled)**: added `RiemannRecognitionGeometry/Port/BlaschkeDominatesTotal.lean`, providing
  `Port.blaschke_dominates_total_of_cofactorBMO` (an RG-facing replacement of `Axioms.blaschke_dominates_total` that no longer needs `RGAssumptions`).
  It also provides variants that depend only on the energy-based `Port.CofactorCRGreenAssumptions` bundle (instead of full `ClassicalAnalysisAssumptions`).
- **Port step (compiled)**: added `RiemannRecognitionGeometry/Port/ZeroFreeWithInterval.lean`, providing
  `Port.zero_free_with_interval_of_cofactorBMO` (a centered contradiction theorem that removes `RGAssumptions` from the `zero_free_with_interval` step).
- **Port step (compiled)**: added `RiemannRecognitionGeometry/Port/LocalZeroFree.lean`, providing Port analogues of
  `Axioms.local_zero_free` and `Axioms.no_interior_zeros` that remove the `RGAssumptions` parameter and route the
  contradiction through the Port centered theorem + `Port.CofactorBMOInheritance`.
- **Port step (compiled)**: added `RiemannRecognitionGeometry/Port/CofactorCRGreenAssumptions.lean`, packaging the
  remaining CR/Green step as an **energy-based target** for `cofactorEbox_poisson` (with a compatibility lemma from
  the current project-level cofactor Green axiom).
- **Port step (compiled)**: added `RiemannRecognitionGeometry/Port/CofactorBMOInheritance.lean`, packaging the
  missing **BMO inheritance** bridge (logAbsXi → cofactorLogAbs) as an explicit target interface, and wired it into
  the Port centered contradiction (`Port.zero_free_with_interval_of_inheritance` / `..._of_OscillationTarget_and_inheritance`).
  **Update**: after correcting the Port cofactor boundary-modulus model (`cofactorLogAbs ρ = logAbsXi`), this inheritance
  is now definitionally trivial (`cofactorBMOInheritance_trivial`), and there are convenience wrappers that take only
  `OscillationTarget`.
- **Port step (compiled)**: `RiemannRecognitionGeometry/Port/MainNoRGAssumptions.lean` now has “trivial inheritance”
  wrappers (no explicit `CofactorBMOInheritance` argument) for the Port main theorems, matching the simplified
  `cofactorLogAbs` model.
- **Port alignment (compiled)**: added `RiemannRecognitionGeometry/Port/WedgeClosure.lean` and `RiemannRecognitionGeometry/Port/SchurPinch.lean`,
  re-exporting the already-present Route 3 boundary-wedge and Schur pinch interfaces via stable `Port/*` paths
  (matching the shape of the corresponding `reality` Hardy/Dirichlet modules).
- **Port aggregator (compiled)**: added `RiemannRecognitionGeometry/Port.lean` so all `Port/*` modules can be built
  together with `lake build RiemannRecognitionGeometry.Port`.
- **Next**: start discharging the two port interfaces for `Ebox := Port.cofactorEbox_poisson` via
  Green/CR + boundary-term gates (CRGreen). (Carleson budget is now in place for `cofactorEbox_poisson`.)
- **Remaining port bottleneck (most important)**: prove `HardyDirichletCRGreen cofactorEbox_poisson`
  (i.e. the Green pairing / Cauchy–Schwarz bound that converts energy into a cofactor phase bound).
  After that, the next major analytic target for the RG route is proving `OscillationTarget` for `logAbsXi`.
  (BMO inheritance is already trivial for the current Port cofactor boundary-modulus model.)
- **Update**: Port now also has an explicit **energy-based xi-phase CR/Green target**
  (`Port/XiCRGreenAssumptions.lean`) and a derived energy-based upper bound
  `Port.totalPhaseSignal_bound_of_xiCRGreenAssumptions` (`Port/TotalPhaseSignalBound.lean`).
  This enables a new Port “main” route (in `Port/MainNoRGAssumptions.lean`) that avoids the monolithic
  `ClassicalAnalysisAssumptions` record entirely, depending instead on the explicit energy-based CR/Green targets.
  **Update**: `Port/XiCarlesonBudget.lean` provides the matching Hardy/Dirichlet Carleson-budget instance for the
  xi energy functional (wrapped as an `Ebox : ℂ → WhitneyInterval → ℝ`), keeping the Port pipeline symmetric.
  **Update**: `Port/TotalPhaseSignalBound.lean` now also has a budget-based variant of the same upper bound
  (Carleson budget + CR/Green ⇒ `totalPhaseSignal ≤ U_tail`), matching the blueprint decomposition explicitly.
- **Update**: for convenience, `Port/EnergyCRGreenAssumptions.lean` bundles the two CR/Green targets (xi-side + cofactor-side),
  and Port main theorems now have wrappers that take this single bundled assumption.
- **Update**: `Port/RealPhaseTransfer.lean` adds a “real phase → `Real.Angle`” transfer layer, so future CR/Green work
  can be done on real-valued phase differences (as in the `reality` blueprint) and then pushed into the RG/Port
  `Real.Angle` statements automatically.
  **Update**: Port now also has “blueprint-style” wrappers for the centered contradiction and Port RH theorem that
  take `XiCRGreenAssumptionsReal` / `CofactorCRGreenAssumptionsReal` directly (then transfer internally).
  **Update**: `Port/EnergyCRGreenAssumptionsReal.lean` bundles the real-valued CR/Green targets, and there are
  wrappers that accept this single bundled assumption.
  **Update**: Port now also has faithful “S2” interfaces (trace identity + pairing bound) on **both** sides:
  - xi: `Port/XiCRGreenS2Interfaces.lean` + `Port/XiCRGreenS2.lean`
  - cofactor: `Port/CofactorCRGreenS2Interfaces.lean` + `Port/CofactorCRGreenS2.lean`
  plus wiring glue `Port/EnergyCRGreenS2.lean` and a Port main wrapper
  `RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_S2` in `Port/MainNoRGAssumptions.lean`.
  **Update**: Port now also has S2-facing convenience wrappers for the *intermediate* steps:
  - `Port/TotalPhaseSignalBound.lean`: `totalPhaseSignal_bound_of_xiS2`
  - `Port/ZeroFreeWithInterval.lean`: `zero_free_with_interval_of_OscillationTarget_of_S2`
  - `Port/LocalZeroFree.lean`: `local_zero_free_of_OscillationTarget_of_S2` and
    `no_interior_zeros_of_OscillationTarget_of_S2`
  - `Port/MainNoRGAssumptions.lean`: `no_off_critical_zeros_in_strip_of_oscillationTarget_of_S2`

## Historical snapshot (superseded)

The content below reflects an earlier stage of the RG development; it is kept for context.

### Sorries: 9 remaining (historical)

#### Closed this session:
- ✅ phaseChange_arctan_formula vacuous case (line 230) - DONE

#### Remaining sorries:

1. **phaseChange_arctan_formula mixed-sign** (line 243)
   - Case: a < σ < b with γ > 0
   - Formula differs by π term; edge cases (a=σ, b=σ) already proven

2. **phase_bound_from_arctan σ < a** (line 550)
   - Needs arctan subtraction formula and geometric bounds

3. **phase_bound_from_arctan σ > b** (line 571)
   - Similar to above

4. **phase_bound_neg_im mixed case** (line 687)
   - Analysis shows needs upper bound on interval width
   - Current constraint only gives lower bound

5. **phase_bound_neg_im σ < a** (line 697)
   - Needs γ < 0 version of arctan formula

6. **phase_bound_neg_im σ > b** (line 699)
   - Similar to above

7. **zero_has_nonzero_im** (line 784)
   - ζ(s) ≠ 0 for real s ∈ (0, 1)
   - Requires Dirichlet eta function (not in Mathlib)

8. **blaschke_dominates_total** (line 890)
   - Main BMO→Carleson theorem
   - ~300 lines of classical analysis

9. **whitney_interval_width** (Main:98)
   - Covering geometry constraint
   - May need modified covering construction

### Key Insight (historical)

The phase bounds for "mixed-sign" and "σ outside interval" cases require:
- The interval width b - a to be comparable to |γ| (both lower AND upper bounds)
- Current constraint only gives lower bound: b - a ≥ |γ|
- Without upper bound, phase change can be too small for L_rec bound

This suggests either:
1. Add upper bound constraint to phase_bound lemmas
2. Modify Whitney covering to ensure controlled width
3. Find alternative proof strategy for these cases
