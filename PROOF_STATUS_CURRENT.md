# Current Proof Status

## Current status (2025-12-18)

- **Build**: `lake build` succeeds with **zero warnings**.
- **`sorry` count**: **0** across the entire Lean codebase (verified via grep).
- **Axiom count**: **24 explicit axioms** across 10 files (verified via grep):
  - ExplicitFormula track: 7 axioms (Weil transform, outer/Schur bridges, outer construction, etc.)
  - Remaining scaffolding: 17 axioms (Carleson/BMO interfaces, tail/zero-density stubs, etc.)
  - Port track: 0 axioms (all assumptions are bundled as hypothesis structures, not `axiom` declarations)
- **Axiom eliminated (2025-12-22)**: `completedRiemannZeta₀_conj` in `RiemannRecognitionGeometry/ExplicitFormula/ZetaConjugation.lean`
  is now a theorem (proved by unfolding `completedRiemannZeta₀` to Hurwitz’s completion and applying a Mellin‑conjugation lemma).
- **Axiom eliminated (2025-12-22)**: `deriv_xiLagarias_conj` in `RiemannRecognitionGeometry/ExplicitFormula/Lagarias.lean`
  is now a theorem (using `deriv_conj_conj` + `xiLagarias_conj`).
- **Axiom eliminated (2025-12-22)**: removed the ill-posed `axiom zetaPSCGlue` in
  `RiemannRecognitionGeometry/ExplicitFormula/ZetaInstantiation.lean` (the old “`Complex.arg` pointwise phase” stub).
  ζ boundary phase / μ-spec data are now carried only as hypothesis fields in `ZetaPSCHypotheses`, matching the
  measure-first Route‑3 design. (Also: `ContourToBoundary.PSCComponents` and `ZetaPSCHypotheses` no longer require a
  separate pointwise `boundaryPhase_diff` field.)
- **Axiom eliminated (2025-12-22)**: removed `axiom zetaRoute3Glue : ZetaRoute3Glue` by threading `ZetaRoute3Glue`
  as an explicit assumption parameter through the optional ζ Route‑3 glue wrappers in
  `RiemannRecognitionGeometry/ExplicitFormula/ZetaInstantiation.lean`.
- **Axiom eliminated (2025-12-22)**: removed the lightweight shim axiom `boundaryWedgeAssumptions_zeta` in
  `RiemannRecognitionGeometry/ExplicitFormula/PPlusZetaShim.lean`; wedge assumptions are now passed explicitly
  (matching `ZetaInstantiation.EndToEnd.AssumptionsSplice`), and the Port re-export in
  `RiemannRecognitionGeometry/Port/WedgeClosure.lean` was updated accordingly.
- **Axiom eliminated (2025-12-22)**: removed `axiom zetaDet2AnalyticAssumptions_weil` in
  `RiemannRecognitionGeometry/ExplicitFormula/ZetaDet2Weil.lean`; the det₂ analytic obligations for `WeilTestFunction`
  are now treated purely as an explicit hypothesis bundle (to be proved later from Mathlib).
- **Axiom eliminated (2025-12-22)**: removed `axiom fourierInversionDirichletTerm_weil` in
  `RiemannRecognitionGeometry/ExplicitFormula/ZetaFourierInversionWeil.lean`; it is now an explicit assumption surface
  (`FourierInversionDirichletTerm_weil`) to be discharged later from Mathlib.
- **Next target (Route 3 / ζ)**: eliminate `axiom weilTransform_convolution_axiom` in
  `RiemannRecognitionGeometry/ExplicitFormula/WeilTestFunction.lean` (either by proving the Weil-transform convolution
  identity, or by threading it as an explicit assumption bundle).
- **Active spine axiom check (2025-12-22)**: running `#print axioms` on the active Port‑S2 spine theorem
  `RiemannRecognitionGeometry.Port.RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_S2`
  shows it depends on **exactly one** project-level axiom:
  `RiemannRecognitionGeometry.PoissonExtension.bmo_carleson_embedding`
  (plus Lean’s standard classical axioms like `Classical.choice` / `propext`).
  - **Blocker**: eliminating this axiom requires a full Fefferman–Stein BMO→Carleson embedding formalization
    for the (conjugate) Poisson extension (see `REMAINING_WORK.md` (G0) for the decomposition plan).
    - **Repo reality check**: the vendored Mathlib in this project has **no Carleson/BMO→Carleson embedding library**,
      so this is not currently solvable by importing an upstream theorem.
    - **Statement hygiene note**: the axiom is currently stated without `a < b`, but the RHS uses `(b - a)`;
      replacing it by a theorem will require adding `hab : a < b` or changing `(b - a)` to `Real.max (b - a) 0`.
  - **Progress**: the first geometry sub-lemma needed by the tent-space proof is now formalized:
    `RiemannRecognitionGeometry.PoissonExtension.cone_base_volume_ge`.
  - **Progress (more geometry chips)**:
    - `RiemannRecognitionGeometry.PoissonExtension.integral_if_abs_lt_const`
    - `RiemannRecognitionGeometry.PoissonExtension.cone_weight_le_integral_indicator`
    - `RiemannRecognitionGeometry.PoissonExtension.setIntegral_prod_swap`
    - `RiemannRecognitionGeometry.PoissonExtension.integrableOn_K_of_integrableOn_cone`
    - `RiemannRecognitionGeometry.PoissonExtension.expand_box_integral`
    - `RiemannRecognitionGeometry.PoissonExtension.cone_to_tent_geometry`
  - **Progress (first analytic chip)**:
    - `RiemannRecognitionGeometry.PoissonExtension.deriv_conjugatePoissonIntegral_eq_integral_dxKernel`
      (differentiation under the integral sign for the conjugate Poisson integral; a prerequisite for turning the
      Fefferman–Stein embedding from an axiom into a theorem).
  - **Progress (second analytic chip, 2025-12-22)**:
    `RiemannRecognitionGeometry.PoissonExtension.deriv_conjugatePoissonIntegral_eq_integral_dyKernel`
    (y-derivative analogue; needed to control the full gradient energy).
  - **Next analytic chip to attempt**: `RiemannRecognitionGeometry.PoissonExtension.poisson_energy_identity_L2`
    (global weighted energy identity / Plancherel for the Poisson/conjugate Poisson extension).
    - **Reality check (2025-12-22)**: the vendored Mathlib here has Fourier inversion and basic Fourier-integral
      identities, but does **not** appear to ship a usable Parseval/Plancherel theorem for `Real.fourierIntegral` on
      `L²(ℝ)` (and there is no Poisson-kernel Fourier-transform API). So this “next chip” is currently blocked on new
      foundational Fourier-analysis development (see the new blocker detail added under (G0) in `REMAINING_WORK.md`).
- **Unconditional Port‑S2 reality check (2025-12-22)**: even if the last project-level axiom above is eliminated,
  the active Port‑S2 spine theorem is still **conditional** on:
  - `OscillationTarget` (global-BMO smallness for `logAbsXi`), and
  - `XiCRGreenS2.Assumptions` + `CofactorCRGreenS2.Assumptions` (the faithful “trace + pairing” inputs).
  There is currently **no theorem** in this repo that produces `OscillationTarget` unconditionally; turning the
  Port‑S2 route into a fully unconditional RH proof therefore requires proving these analytic hypotheses (or
  switching the spine to the renormalized-tail `OscillationTargetTail` interface).
  - **OscillationTarget audit (2025-12-22)**: `OscillationTarget := ∃ M, InBMOWithBound logAbsXi M ∧ M ≤ C_tail`
    has no internal proof path today. The only relevant lemma is
    `FeffermanStein.logAbsXi_mean_oscillation_bound`, which simply unwraps the assumed bound.
    Next smallest proposed chip: `log_singularity_meanOscillation_le` (mean oscillation bound for `t ↦ log|t-γ|`).

- **Port‑S2 checklist audit (2025-12-22): `XiCRGreenS2.Assumptions` is a pure interface (BLOCKED)**.
  The xi-side S2 bundle is defined as:
  `∃ T : Port.XiCRGreenS2Interfaces.GreenTraceIdentity, Port.XiCRGreenS2Interfaces.PairingBound T`
  (`RiemannRecognitionGeometry/Port/XiCRGreenS2.lean`).
  A witness `T` must provide:
  - a real lift `theta I : ℝ → ℝ` with `(theta I t : Real.Angle) = phaseXi t` on the Whitney base,
  - a velocity `dPhase I : ℝ → ℝ` with `HasDerivAt (theta I) (dPhase I t)` for all `t` in the base,
  - `IntervalIntegrable (dPhase I)` on the base,
  and the pairing inequality:
  `|∫ dPhase| ≤ sqrt(xiEbox_poisson I) * (C_geom * |I|^{-1/2})`.
  No construction of such `T` exists in the repo today (this is a substantial complex-analysis / Green–trace
  formalization task), so the item is currently **BLOCKED**.
  - **Audit detail (2025-12-22)**: `XiCRGreenS2.Assumptions` is literally
    `∃ T : Port.XiCRGreenS2Interfaces.GreenTraceIdentity, Port.XiCRGreenS2Interfaces.PairingBound T`
    (`RiemannRecognitionGeometry/Port/XiCRGreenS2.lean`), and there are **no** occurrences in the repo that
    construct such a witness (only downstream uses of it as a hypothesis).
  - **Next smallest lemma/package to attempt**: introduce `RiemannRecognitionGeometry/Port/XiOuterLogBranch.lean`
    (xi analogue of `Port/CofactorOuterLogBranch.lean`) and prove the purely-formal wiring lemma
    `XiOuterLogBranch → XiCRGreenS2.Assumptions`.

- **Port‑S2 checklist audit (2025-12-22): `CofactorCRGreenS2.Assumptions` is also an interface (BLOCKED)**.
  The cofactor-side S2 bundle is defined as:
  `∃ h : Port.CofactorOuterLogBranch.CofactorOuterLogBranch, PairingBound (greenTraceIdentity h)`
  (`RiemannRecognitionGeometry/Port/CofactorCRGreenS2.lean`).
  Here `CofactorOuterLogBranch` is a holistic “outer/log branch” package that should (in an honest analytic proof)
  come from a holomorphic nonvanishing cofactor with a logarithm branch; it contains:
  - a phase lift `CofactorPhaseLift`,
  - an FTC-valid velocity `PhaseVelocityFTC`, and
  - a Poisson-model pairing/trace convergence hook `PhaseVelocityBoundaryTracePoissonPairing`.
  However, the repo currently provides **no theorem** that constructs such an `h`, and the required `PairingBound`
  inequality (the actual CR/Green Cauchy–Schwarz estimate in energy form) is likewise not derived from the Poisson
  pairing hook. Therefore this checklist item is also **BLOCKED**.
  - **Audit detail (2025-12-22)**: the *lift agreement* part of S2 is not the main obstacle:
    `Port/RealPhaseTransfer.lean` already defines a canonical real-valued representative
    `rgCofactorPhaseReal ρ t := argXi t + rgBlaschkePhase ρ t` and proves
    `rgCofactorPhaseAngle ρ t = (rgCofactorPhaseReal ρ t : Real.Angle)`.
    The real blockers are: an FTC-valid velocity for that representative (in particular, a usable derivative theory
    for `argXi` on Whitney bases), plus the pairing inequality itself.
  - **Next smallest lemma to attempt**: `hasDerivAt_rgBlaschkePhase` (differentiate the explicit
    arctan Blaschke phase). This isolates the remaining “hard” derivative content to `argXi`.
  - **Progress (2025-12-22)**: proved `RiemannRecognitionGeometry.hasDerivAt_rgBlaschkePhase`
    in `RiemannRecognitionGeometry/Phase.lean` (derivative of the explicit arctan Blaschke phase).
  - **Progress (2025-12-22)**: added two follow-up “FTC wiring” lemmas in `RiemannRecognitionGeometry/Phase.lean`:
    - `RiemannRecognitionGeometry.hasDerivAt_rgBlaschkePhase_simplified` (same derivative in the clean Poisson-kernel form)
    - `RiemannRecognitionGeometry.intervalIntegrable_rgBlaschkePhase_deriv_of_ne` (interval integrability of that derivative
      under the natural off-line hypothesis `ρ.re ≠ 1/2`).
- **Note on what “axiom count” means**:
  - This counts literal Lean `axiom` declarations (`^\s*axiom\s+`).
  - It does **not** count “axiom-shaped fields” like `*_axiom_statement` inside assumption bundles such as `ClassicalAnalysisAssumptions` / `RGAssumptions`.
  - The **RG main theorems** are explicitly conditional on `ClassicalAnalysisAssumptions`, `RGAssumptions`, and `OscillationTarget`; the additional `ExplicitFormula/*` axioms are for the separate Route‑3 track.
- **Recognition Geometry (RG) track** (`RiemannRecognitionGeometry/Main.lean`):
  - Core RG development has **0 `sorry`** in `RiemannRecognitionGeometry/Axioms.lean`.
  - The main theorem is explicitly **conditional** on:
    - `OscillationTarget` / `InBMOWithBound logAbsXi M ∧ M ≤ C_tail`
    - `ClassicalAnalysisAssumptions` (Green/CR bounds + ζ≠0 on (0,1))
    - `RGAssumptions.j_carleson_energy_axiom_statement` (RG bottleneck)
- **Route 3 / ExplicitFormula track**: see `ROUTE3_DRIVER.md` for the live assumption ledger and remaining **axioms / hypothesis bundles**. The `ExplicitFormula/*` subtree is now `sorry`-free.
- **Verification**: Executed a comprehensive second-tier cleanup (linter warnings, unused variables, deprecations) reaching a zero-warning state.
- **Next Steps**: Formalize the remaining analytic estimates or continue discharging assumption bundles via faithful S2/Strong interfaces.
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
