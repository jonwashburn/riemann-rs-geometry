## Proof soundness plan (recursive)

This document is meant to be pasted back into the assistant as a **recursive prompt**. The assistant should follow it **top-to-bottom**, always working on the **first unchecked checkbox**, until the “Definition of done” is satisfied.

### Non-negotiable constraints
- **Keep classical axioms**: Lean’s classical logic/choice axioms are fine, and we will also keep “classical analysis” results as explicit axioms (e.g. Fefferman–Stein, Green identity, identity principle for η/ζ), *as long as they are not formulated in a way that contradicts standard analysis / Mathlib.*
- **Zero inconsistent axioms in the build graph**: do not leave an inconsistent axiom in any module that is compiled by `lake build`.
- **No “make it true by definition” in the main chain**: placeholder definitions are allowed only if they are clearly quarantined (not imported by the main theorem) and labeled as scaffolding.
- **Always keep the project building**: after each meaningful change, run `lake build`.
- **No scope creep**: this plan is about *logical soundness and faithful interfaces*, not about proving RH unconditionally.

### How the assistant should operate (when given this file as prompt)
- **Workflow**:
  - Read the current state of the repo.
  - Find the first unchecked checkbox below.
  - Implement that step completely.
  - Mark it checked in this file.
  - Run `lake build`.
  - Make a git commit with a short message (unless the step explicitly says “no commit”).
  - Repeat.
- **When to stop**: only stop when the “Definition of done” at the bottom is met.

### Definitions
- **Classical analysis axiom (allowed)**: a statement that is expected to be true in standard mathematical analysis (e.g. Fefferman–Stein BMO→Carleson embedding) even if it’s hard to formalize.
- **Inconsistent axiom (not allowed)**: a statement that contradicts basic theorems already in Mathlib / standard analysis (e.g. a uniform bound on `∫` for *all* integrands on positive-length intervals).
- **Main chain**: everything imported (directly or indirectly) by `RiemannRecognitionGeometry/Main.lean`.

---

## Milestone 0 — Inventory + guardrails

- [x] **0.1 Record the current axiom surface.**
  - Produce a list of all `axiom` declarations in `RiemannRecognitionGeometry/`.
  - Partition them into:
    - **Allowed classical analysis axioms** (keep)
    - **Engineering/structure axioms** (dyadic / CZ bookkeeping; keep)
    - **Suspect axioms** (might be inconsistent; must be audited)
  - Save the result into this file under “Axiom registry” (append-only).

- [x] **0.2 Identify the main chain precisely.**
  - Starting from `RiemannRecognitionGeometry.lean` and `RiemannRecognitionGeometry/Main.lean`, list the modules imported in the transitive closure.
  - Confirm which axioms are actually in the main chain.
  - Add a short table to this file: **axiom → file → in main chain?**

- [ ] **0.3 Add a repo rule: all axioms live in one place.**
  - Create `RiemannRecognitionGeometry/Conjectures.lean`.
  - Move all axioms that are meant to be “classical analysis assumptions” into that file.
  - Re-export them from the existing files (thin wrappers) so downstream code doesn’t break.
  - Goal: future audits are one-file.

---

## Milestone 1 — Remove inconsistent axioms (hard requirement)

### Known inconsistent module: `RiemannRecognitionGeometry/FeffermanSteinBMO.lean`
This file currently contains **structurally inconsistent content**:
- `tail_energy` is defined as `K_tail * I.len` (independent of the function), but `fefferman_stein_bmo_carleson` quantifies over all `f` and all BMO bounds `M`, which immediately conflicts with taking `f := 0` and `M` small.
- `tail_pairing_bound_axiom` asserts `|∫_I integrand| ≤ U_tail` for **any** integrand on **any** positive-length interval, which contradicts `integrand := 1` on large intervals.

- [ ] **1.1 Decide: delete or repair `FeffermanSteinBMO.lean`.**
  - Preferred: **delete** it if it is not used anywhere in the main chain.
  - If it must remain, **repair** it by:
    - Redefining `tail_energy` to depend on the boundary function `f` (or its Poisson extension), not a constant.
    - Replacing `tail_pairing_bound_axiom` with a properly-scoped statement whose hypotheses imply the bound (e.g. assuming a Carleson energy bound and a normalized window test function).

- [ ] **1.2 Enforce “no inconsistent axioms in build graph”.**
  - Make sure `lake build` does not compile any module that contains an inconsistent axiom.
  - If Lake builds all modules under the library by default, you must delete/repair the file rather than merely avoiding imports.

- [ ] **1.3 Add a “consistency smoke test” module.**
  - Create `RiemannRecognitionGeometry/ConsistencySmokeTest.lean`.
  - Prove easy facts that would *immediately* refute the old inconsistent axioms, e.g.
    - For any positive-length interval, `|∫ t in Icc a b, (1:ℝ)| = b-a`.
    - Instantiate with a Whitney interval’s `interval` to show large integrals exist.
  - This module should compile and should not assume any project axioms.
  - Purpose: prevent reintroducing “uniform bound on all integrands”-type axioms.

---

## Milestone 2 — Make the project’s claims internally honest

- [ ] **2.1 Fix “UNCONDITIONAL” labeling.**
  - Theorems `RiemannHypothesis_recognition_geometry` and `RiemannHypothesis_classical` currently take `h_osc`.
  - Update docstrings/comments in `RiemannRecognitionGeometry/Main.lean`, `RiemannRecognitionGeometry/Axioms.lean`, and the bundle text files to clearly state: **RH is proved conditional on `h_osc` (global BMO bound for `logAbsXi`).**
  - Optional (recommended): rename the theorem(s) to encode the hypothesis, e.g. `RiemannHypothesis_of_logAbsXi_BMO`.

- [ ] **2.2 Separate “classical assumption” from “RG-specific conjecture”.**
  - Create a single bundled hypothesis structure, e.g.
    - `structure ClassicalAnalysisAssumptions` (Fefferman–Stein, Green identity, η/ζ identity principle, etc.)
    - `structure RGAssumptions` (the actual bottleneck estimate(s), if any)
  - Rewrite the main theorem signatures to depend on these structures rather than many loose axioms.

---

## Milestone 3 — Fix the phase object (faithfulness requirement)

Right now the main chain uses principal `Complex.arg` on ξ and treats it like a continuous harmonic conjugate. This mismatch makes the “FTC / Green / Cauchy–Riemann” story **not about the defined objects**.

- [ ] **3.1 Introduce a faithful phase interface.**
  - Create `RiemannRecognitionGeometry/Phase.lean`.
  - Define a phase-change quantity that matches analysis, e.g. one of:
    - (Preferred) boundary value of the harmonic conjugate (via conjugate Poisson integral / Hilbert transform),
    - or an integral of `Im (ξ'/ξ)` along the critical line away from zeros.
  - Keep the old `argXi` only as a convenience, but stop using it in theorems that claim analytic identities.

- [ ] **3.2 Refactor `actualPhaseSignal` and downstream lemmas to use the new phase.**
  - Update `RiemannRecognitionGeometry/FeffermanStein.lean` and `RiemannRecognitionGeometry/Axioms.lean` so the “phase bound” theorems/axioms are stated for the new phase object.

- [ ] **3.3 Add explicit “branch / continuity” hypotheses where needed.**
  - Any statement using a phase difference should either:
    - assume ξ is nonzero on the interval (so a continuous argument lift exists), or
    - work with winding number / `Real.Angle`, then lift.

---

## Milestone 4 — Quarantine or remove scaffolding definitions

- [ ] **4.1 Quarantine `BMOCarleson.lean` if it remains definitional scaffolding.**
  - `phaseIntegral := U_tail/3` is not a real integral.
  - Either:
    - remove the module from the library build / imports, or
    - rewrite it to define the genuine integral and prove the bound from the axioms.

- [ ] **4.2 Eliminate “proof-by-definition” from anything imported by `Main.lean`.**
  - Search for definitions that hard-code desired bounds and ensure they are not used in the main chain.

---

## Milestone 5 — Tighten the axiom statements (make them plausibly true)

- [ ] **5.1 Rewrite any axiom that is too broad.**
  - Rule: if the axiom quantifies over *all* functions/integrands and returns a uniform numerical bound independent of the input, it is almost certainly inconsistent.
  - Replace such axioms with statements whose conclusions scale correctly (e.g. depend on norms and interval length).

- [ ] **5.2 Add “unit tests” for each axiom family.**
  - For each axiom about integrals/inequalities, add a small lemma file showing it behaves correctly on:
    - `f := 0`, `f := 1`, indicator functions, etc.
  - These are not mathematical proofs of the axiom; they are checks that the formulation isn’t *obviously* contradictory.

---

## Axiom registry (append-only)

### Snapshot (2025-12-12)

Total `axiom` declarations in `RiemannRecognitionGeometry/`: **18**.

#### Allowed classical analysis axioms (keep)
- **`identity_principle_eta_zeta_lt_one_axiom`** — `RiemannRecognitionGeometry/DirichletEta.lean`
  (Identity principle / analytic continuation input for η–ζ relation on `0<s<1`.)
- **`bmo_carleson_embedding`** — `RiemannRecognitionGeometry/PoissonExtension.lean`
  (Fefferman–Stein BMO→Carleson embedding; classical harmonic analysis.)
- **`green_identity_axiom_statement`** — `RiemannRecognitionGeometry/Axioms.lean`
  (Green/Cauchy–Riemann/Cauchy–Schwarz phase bound; classical harmonic analysis.)
- **`weierstrass_tail_bound_axiom_statement`** — `RiemannRecognitionGeometry/Axioms.lean`
  (RG-specific “tail bound” / factorization estimate. Not a standard textbook axiom, but not obviously inconsistent.)
- **`zero_has_large_im`** — `RiemannRecognitionGeometry/Basic.lean`
  (Numerical input: first nontrivial zero height > 14; consistent with standard facts.)

#### Engineering / structure axioms (keep)
- **`whitney_len_from_strip_height_axiom`** — `RiemannRecognitionGeometry/Basic.lean`
  (Whitney covering geometry input for length lower bound.)
- **`whitney_centered_from_strip_axiom`** — `RiemannRecognitionGeometry/Basic.lean`
  (Whitney covering geometry input for centering.)
- **`dyadic_nesting`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Dyadic grid nesting; bookkeeping/structure.)
- **`maximalBad_disjoint_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Maximal-bad intervals disjointness; CZ bookkeeping.)
- **`DyadicInterval.avg_doubling_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Dyadic doubling of averages; elementary measure/integral bookkeeping.)
- **`czDecomposition_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Existence of dyadic CZ decomposition; classical but treated here as infrastructure.)
- **`czDecompFull_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Full CZ decomposition with good/bad parts; infrastructure.)
- **`goodLambda_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Good-λ step; infrastructure for JN/BMO consequences.)
- **`jn_first_step_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (First step in John–Nirenberg; infrastructure.)
- **`bmo_Lp_bound_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (BMO→Lᵖ control; infrastructure.)
- **`bmo_kernel_bound_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Kernel bound used in harmonic analysis chain; infrastructure.)

#### Suspect axioms (must audit; likely inconsistent as currently formulated)
- **`fefferman_stein_bmo_carleson`** — `RiemannRecognitionGeometry/FeffermanSteinBMO.lean`
  **Suspect** because `tail_energy` in that file is defined as a constant multiple of `I.len` (independent of `f`), while the axiom quantifies over all `f` and all BMO bounds `M`.
- **`tail_pairing_bound_axiom`** — `RiemannRecognitionGeometry/FeffermanSteinBMO.lean`
  **Inconsistent** as stated: it bounds `|∫_I integrand|` by a fixed constant for *all* `integrand` on any positive-length interval.

#### Main chain import closure (project modules only)
Starting points:
- `RiemannRecognitionGeometry.lean`
- `RiemannRecognitionGeometry/Main.lean`

Project modules in the transitive import closure:
- `RiemannRecognitionGeometry.Mathlib.ArctanTwoGtOnePointOne`
- `RiemannRecognitionGeometry.Basic`
- `RiemannRecognitionGeometry.Axioms`
- `RiemannRecognitionGeometry.WhitneyGeometry`
- `RiemannRecognitionGeometry.PoissonJensen`
- `RiemannRecognitionGeometry.CarlesonBound`
- `RiemannRecognitionGeometry.FeffermanStein`
- `RiemannRecognitionGeometry.JohnNirenberg`
- `RiemannRecognitionGeometry.DirichletEta`
- `RiemannRecognitionGeometry.PoissonExtension`
- `RiemannRecognitionGeometry.FeffermanSteinBMO`  *(currently imported by `Axioms.lean`; this is the inconsistent module to remove/repair in Milestone 1)*
- `RiemannRecognitionGeometry.Main`

#### Axiom → file → in main chain?
All project axioms are currently in the main chain (via `RiemannRecognitionGeometry.lean` → `Axioms.lean` imports).

| axiom | file | in main chain? |
|---|---|---|
| `identity_principle_eta_zeta_lt_one_axiom` | `RiemannRecognitionGeometry/DirichletEta.lean` | ✅ yes |
| `dyadic_nesting` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `maximalBad_disjoint_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `DyadicInterval.avg_doubling_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `czDecomposition_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `czDecompFull_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `goodLambda_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `jn_first_step_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `bmo_Lp_bound_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `bmo_kernel_bound_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `zero_has_large_im` | `RiemannRecognitionGeometry/Basic.lean` | ✅ yes |
| `whitney_len_from_strip_height_axiom` | `RiemannRecognitionGeometry/Basic.lean` | ✅ yes |
| `whitney_centered_from_strip_axiom` | `RiemannRecognitionGeometry/Basic.lean` | ✅ yes |
| `fefferman_stein_bmo_carleson` | `RiemannRecognitionGeometry/FeffermanSteinBMO.lean` | ✅ yes *(problematic)* |
| `tail_pairing_bound_axiom` | `RiemannRecognitionGeometry/FeffermanSteinBMO.lean` | ✅ yes *(problematic)* |
| `bmo_carleson_embedding` | `RiemannRecognitionGeometry/PoissonExtension.lean` | ✅ yes |
| `green_identity_axiom_statement` | `RiemannRecognitionGeometry/Axioms.lean` | ✅ yes |
| `weierstrass_tail_bound_axiom_statement` | `RiemannRecognitionGeometry/Axioms.lean` | ✅ yes |

---

## Definition of done

All of the following must be true:
- **(D1)** `lake build` succeeds.
- **(D2)** There are **no inconsistent axioms in any compiled module** (especially no “uniform bound for arbitrary integrands” style axioms).
- **(D3)** The main theorem(s) and docs honestly state all remaining hypotheses (e.g. `h_osc`), and “UNCONDITIONAL” is not claimed unless the hypothesis is actually removed.
- **(D4)** Phase-related results are stated about a phase object that matches the analytic machinery (continuous lift / harmonic conjugate / log-derivative integral), not principal `Complex.arg`.
