### Purpose

This is a **systematic referee tracker** for `Riemann-Christmas.tex` (~1959 lines).  
Goal: enable a structured, line-by-line technical audit that (a) verifies correctness, (b) identifies any hidden assumptions, and (c) records “status + evidence” for each load‑bearing step.

This document is written so we can:
- Split work across reviewers.
- Track “verified / needs clarification / gap found” per lemma.
- Keep a running list of required external results (with citations and exact hypotheses).
- Ensure every line range is reviewed at least once.

---

### How to use this tracker

- **Mark status** with checkboxes and dates.
- For each item, record:
  - **What the claim is**
  - **What it depends on**
  - **What standard results it invokes**
  - **Any assumptions/regularity requirements**
  - **What to check** (mechanically verifiable steps)
  - **Outcome** (pass / needs fix / gap)

Status legend (use one per item):
- **[ ] not started**
- **[~] in progress**
- **[x] verified**
- **[!] issue found** (must be resolved)
- **[?] unclear / needs clarification**

---

## Referee summary (current)

### Overall status

- **Coverage sweep**: complete (all line ranges have been read once and logged).
- **Mathematical status**: the proof architecture is coherent and many individual analytic steps look standard. The previously flagged “must-fix” structural issues (missing wedge lemma, boundary-passage mismatch, ungated numerics) have been **patched in `Riemann-Christmas.tex`**; after a second-pass, the remaining structural blocker is the wedge-closure hypothesis alignment.

### Major issues (second-pass: patch validation)

- **[!] Global wedge closure remains the one open load-bearing step**:  
  The TeX now makes explicit that the certificate produces **Whitney-local** phase-drop bounds (and admissible-class test bounds), but it still lacks a proved/cited implication that upgrades these Whitney-local bounds to a **global a.e. boundary wedge (P+) after a single rotation**. This is the remaining open step needed for the paper’s advertised unconditional closure.

- **[~] ξ Carleson-energy lemma is now plausibly uniform but still proof-sketched in places**:  
  `lem:carleson-xi` now uses a short-interval count of the form `N(T;H) ≤ A₀ + A₁ H log⟨T⟩` (for `H≤1`) plus a crude RvM bound for larger `H`, which fixes the earlier summation issue. A referee may still request more detail on the “neutralize near zeros” step and on the `|\nabla U|^2 ≍ |\partial_σ U|^2` comparison under the stated regularity.

- **[x] Boundary passage mismatch resolved at the distribution level**:  
  `thm:phase-velocity-quant` has been rewritten to prove **Cauchy convergence in `𝒟'(I)`** from the tested σ-derivative bounds (and uses continuity of the Hilbert transform on distributions). This removes the previously ungrounded “L¹ Cauchy / outer-limit” claim from the phase–velocity step. (If later steps require an `L¹_loc`/BMO boundary trace for the specific modulus function, that should be stated and proved separately.)

### Presentation issues (strongly recommended)

- **[x] Ungated diagnostic numerics patched**:  
  The p-adaptive numeric block is now wrapped in `\ifshownumerics ... \fi`, and the diagnostic computation in `cor:conservative-closure` is gated behind `\shownumerics`. The reader-guide language was also updated to reflect “gated or explicitly diagnostic appendices.”

---

## A. Load‑bearing chain (paper’s own dependency map)

Paper states (see around lines ~149–155) the load‑bearing chain is:

- **Phase–velocity identity + boundary passage** (`thm:phase-velocity-quant`)
- **Windowed phase bound ⇒ (P+)** (`lem:CR-green-phase` + Carleson energy + wedge closure)
- **Globalization/pinch and RH** (`thm:globalize-main`, `cor:RH`)

We treat the following as “must‑referee first.”

### A1. Phase–velocity identity + boundary passage

- [x] **`lem:det2-unsmoothed`** (L209–L219) — Smoothed distributional bound for ∂σ Re log det₂  
  - **Owner**:
  - **Status**: initial pass complete (details below)
  - **Notes**: Proof looks standard: diagonal det₂ expansion → termwise ∂σ → IBP twice against `φ` → Tonelli dominated by `∑ p^{-k/2}/(k^2 log p)`. Needs only routine checks (support of `φ`, boundary terms vanish, uniformity in σ via `p^{-kσ}≤p^{-k/2}`).

- [ ] **`lem:xi-deriv-L1`** (L606–L612) — L¹-tested control for ∂σ Re log ξ  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [x] **`lem:desmooth-L1`** (updated) — Carleson⇒BMO boundary trace / de-smoothing to `L¹_loc`  
  - **Owner**:
  - **Status**: patched + consistent with current uses
  - **Notes**:
    - `lem:desmooth-L1` now states a standard theorem: Carleson control of `|∇U|² σ` on Whitney boxes gives a BMO boundary trace `u` and `U(ε,·) = P_ε * u → u` in `L¹_loc` (Garnett/Stein).
    - The phase–velocity boundary passage has been rewritten to avoid relying on `L¹_loc` convergence; it now uses a **distributional** Cauchy estimate. `lem:desmooth-L1` remains relevant for the **outer-limit / boundary trace** step in `prop:outer-central`.

- [ ] **`lem:outer-phase-HT`** (L315–L321) — outer/Hilbert boundary identity  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [ ] **`lem:pv-test-smoothed`** (L449–L460) — smoothed phase–velocity calculus  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [ ] **`thm:phase-velocity-quant`** (L326–L340) — quantified phase–velocity identity + boundary passage  
  - **Owner**:
  - **Status**:
  - **Notes**:

### A2. Windowed phase bound ⇒ (P+)

- [ ] **`lem:cutoff-pairing`** (L1099–L1111) — cutoff pairing on boxes  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [ ] **`lem:CR-green-phase`** (L1130–L1144) — CR–Green pairing for boundary phase  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [ ] **`lem:neutralization-bookkeeping`** (L275–L291) — neutralization bookkeeping (side/top errors)  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [ ] **Carleson/energy inputs (Whitney)**
  - [ ] **`lem:carleson-arith`** (L887–L897) — arithmetic Carleson energy (prime tail)
  - [ ] **`lem:annular-balayage`** (L919–L930) — annular Poisson L² bound
  - [ ] **`lem:carleson-xi`** (L957–L970) — ξ Carleson energy on Whitney boxes
  - [ ] **`lem:carleson-sum`** (L579–L585) — stable sum bound for box energies
  - [ ] **`cor:xi-carleson-all-I`** (L595–L601) — extension from Whitney to all intervals

- [ ] **Wedge closure**
  - [ ] **`lem:whitney-uniform-wedge`** (L381–L392) — Whitney‑uniform wedge inequality
  - [ ] **`thm:psc-certificate-stage2`** (L1892–L1905) — boundary wedge from product certificate

### A3. Globalization/pinch and RH

- [ ] **`lem:removable-schur`** (L1692–L1694) — removable singularity under Schur bound  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [ ] **`rem:connectedness`** (L541–L543) — connectedness and isolation argument  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [ ] **`thm:limit-rect`** (L1675–L1677) — limit N→∞ on rectangles; Herglotz/Schur closure  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [ ] **`thm:globalize-main`** (L1732–L1734) — globalization across Z(ξ)  
  - **Owner**:
  - **Status**:
  - **Notes**:

- [ ] **`cor:RH`** (L1708–L1710) — conclusion RH from zero‑free half‑plane  
  - **Owner**:
  - **Status**:
  - **Notes**:

---

## B. Full labeled-results inventory (for completeness)

The following are all labeled environments detected in `Riemann-Christmas.tex` with approximate line ranges in that file. This list is used to ensure we cover everything systematically, even if not load‑bearing.

> Note: some `\label{eq:...}` are inside theorem blocks; they’re included only as internal anchors, not separate proof obligations.

| Label | Type | Lines | Title (from `\begin[...]`) | Status |
|---|---:|---:|---|---|
| `lem:det2-unsmoothed` | lemma | 209–219 | Smoothed distributional bound for ∂σ Re log det₂ | [x] |
| `lem:desmooth-L1` | lemma | 252–266 | De-smoothing / boundary passage to an L¹\_loc trace | [x] |
| `lem:neutralization-bookkeeping` | lemma | 275–291 | Neutralization bookkeeping for CR–Green on a Whitney box | [~] |
| `lem:mu-to-lebesgue` | lemma | 298–304 | Poisson lower bound ⇒ Lebesgue a.e. wedge | [?] |
| `lem:outer-phase-HT` | lemma | 315–321 | Outer–Hilbert boundary identity | [x] |
| `thm:phase-velocity-quant` | theorem | 326–340 | Quantified phase–velocity identity and boundary passage | [~] |
| `lem:balayage-density` | lemma | 364–370 | Balayage density and consequence for Q | [~] |
| `lem:local-to-global-wedge` | lemma | 372–390 | Quantitative wedge criterion | [~] |
| `lem:whitney-uniform-wedge` | lemma | 381–392 | Whitney–uniform wedge | [x] |
| `prop:hs-det2-continuity` | proposition | 417–419 | HS→det₂ continuity | [x] |
| `lem:pv-test-smoothed` | lemma | 449–460 | Smoothed phase–velocity calculus | [~] |
| `rem:connectedness` | lemma | 541–543 | Connectedness and isolation | [x] |
| `thm:RH` | theorem | 572–574 | Riemann Hypothesis | [~] |
| `lem:carleson-sum` | lemma | 579–585 | Carleson box energy: stable sum bound | [x] |
| `cor:xi-carleson-all-I` | corollary | 595–601 | Local Carleson energy for Uξ on a fixed interval | [~] |
| `lem:xi-deriv-L1` | lemma | 606–612 | L¹-tested control for ∂σ Re log ξ | [~] |
| `cor:conservative-closure` | corollary | 627–642 | Conservative closure inequalities (diagnostics gated) | [x] |
| `lem:hs-diagonal` | lemma | 654–664 | Diagonal HS determinant analytic and nonzero | [x] |
| `lem:zeta-normalization` | lemma | 671–675 | ζ–normalized outer and compensator | [~] |
| `lem:CH-derivative-explicit` | lemma | 722–728 | Derivative envelope for printed window | [~] |
| `cor:det2-boundary` | corollary | 862–868 | Boundary-uniform smoothed control | [x] |
| `prop:outer-central` | proposition | 874–876 | Outer normalization: existence + boundary modulus + limit | [~] |
| `lem:carleson-arith` | lemma | 887–897 | Arithmetic Carleson energy | [x] |
| `lem:annular-balayage` | lemma | 919–930 | Annular Poisson–balayage L² bound | [~] |
| `lem:carleson-xi` | lemma | 957–970 | Analytic (ξ) Carleson energy on Whitney boxes | [~] |
| `prop:Kxi-finite` | proposition | 1006–1017 | Whitney Carleson finiteness for Uξ | [~] |
| `lem:cutoff-pairing` | lemma | 1099–1111 | Cutoff pairing on boxes | [~] |
| `lem:CR-green-phase` | lemma | 1130–1144 | CR–Green pairing for boundary phase | [~] |
| `lem:outer-cancel` | lemma | 1152–1154 | Outer cancellation in CR–Green | [~] |
| `lem:outer-energy-bookkeeping` | lemma | 1179–1218 | Outer cancellation and energy bookkeeping | [~] |
| `def:admissible-class` | definition | 1242–1258 | Admissible, atom-safe test class | [~] |
| `lem:uniform-CRG-A` | lemma | 1261–1274 | Uniform CR–Green bound for class A | [~] |
| `cor:atom-safe` | corollary | 1299–1312 | Atom neutralization and clean Whitney scaling | [~] |
| `rem:wedge-application` | remark | 1318–1327 | Local-to-global wedge | [x] |
| `cor:CH-Mpsi-final` | corollary | 1328–1347 | Unconditional local window constants | [~] |
| `lem:poisson-bmo-strip` | lemma | 1351–1357 | Poisson–BMO bound at fixed height | [x] |
| `lem:hilbert-H1BMO` | lemma | 1370–1375 | Uniform Hilbert pairing bound | [~] |
| `lem:hilbert` | lemma | 1388–1391 | Hilbert-transform pairing | [~] |
| `lem:poisson-plateau` | lemma | 1417–1420 | Poisson plateau lower bound | [x] |
| `lem:CH-explicit` | lemma | 1449–1459 | Explicit envelope for printed window | [~] |
| `lem:CH-derivative-2pi` | lemma | 1471–1475 | Derivative envelope: CH ≤ 2/π | [~] |
| `lem:Mpsi-correct` | lemma | 1485–1502 | Window mean-oscillation via H¹–BMO and box energy | [~] |
| `lem:P1-monotone` | lemma | 1577–1579 | Monotonicity of tail majorant | [x] |
| `cor:P1-minP` | corollary | 1585–1591 | Minimal tail parameter for target η | [x] |
| `lem:block-gersh` | lemma | 1603–1608 | Block Gershgorin lower bound | [x] |
| `lem:schur-weyl-gap` | lemma | 1626–1630 | Schur–Weyl bound | [~] |
| `thm:limit-rect` | theorem | 1675–1677 | Limit N→∞ on rectangles: 2J Herglotz, Θ Schur | [x] |
| `rem:boundary-uniqueness` | remark | 1683–1685 | Boundary uniqueness and (H+) on R | [~] |
| `cor:Schur-off-zeros` | corollary | 1686–1688 | Unconditional Schur on Ω\Z(ξ) | [x] |
| `lem:removable-schur` | lemma | 1692–1694 | Removable singularity under Schur bound | [x] |
| `cor:RH` | corollary | 1708–1710 | Conclusion (RH) | [x] |
| `cor:poisson-herglotz` | corollary | 1715–1717 | Poisson transport | [x] |
| `cor:cayley-schur` | corollary | 1726–1728 | Cayley | [x] |
| `thm:globalize-main` | theorem | 1732–1734 | Globalization across Z(ξ) | [x] |
| `cor:K-no-FF` | corollary | 1740–1742 | No far-far budget from triangular padding | [~] |
| `lem:CE-constant-one` | lemma | 1773–1775 | Normalization of embedding constant | [~] |
| `thm:psc-certificate-stage2` | theorem | 1892–1905 | Whitney-local phase-mass bounds from product certificate (atom-safe) | [x] |

---

## C. Line‑by‑line pass plan (cover all ~1959 lines)

We will do a “coverage sweep” in contiguous chunks, independent of labeled results, to catch:
- hidden assumptions in prose,
- definition changes,
- macros/constants that change meaning,
- “archived / diagnostic” sections that might accidentally be referenced,
- any subtle domain restrictions.

Each chunk gets one pass, with notes on:
- definitions introduced,
- new assumptions introduced,
- external citations used,
- any step that looks nonstandard.

### Chunk schedule

- [x] **Chunk 0:** L1–L120 (preamble, constants, conventions)  
- [x] **Chunk 1:** L121–L208 (standing properties, reader’s guide, dependency map, intro)  
- [x] **Chunk 2:** L209–L340 (A1: phase–velocity core)  
- [x] **Chunk 3:** L341–L465 (wedge lemma, det₂ continuity, smoothed PV)  
- [x] **Chunk 4:** L466–L578 (globalization section, N1/N2 pinch narrative, RH theorem)  
- [x] **Chunk 5:** L579–L760 (Carleson sum + ξ-deriv tested bound + numeric closure)  
- [x] **Chunk 6:** L761–L918 (HS diagonal + ζ-normalization + window derivative)  
- [x] **Chunk 7:** L919–L1118 (arithmetic energy + annular balayage + ξ energy lemma start)  
- [x] **Chunk 8:** L1119–L1348 (CR–Green pairing, outer cancellation, admissible class, wedge app)  
- [x] **Chunk 9:** L1349–L1565 (Poisson–BMO strip, Hilbert pairing, plateau, explicit envelopes, Mψ)  
- [x] **Chunk 10:** L1566–L1748 (prime tails, finite-block certificates, rectangle limit, Schur removability)  
- [x] **Chunk 11:** L1749–L1959 (appendices, numeric protocols, bibliography sanity)

---

## F. Referee log (running)

### Pass 3 — targeted audit of the remaining analytic infrastructure (ξ Carleson, ζ-normalization, Hilbert/H¹–BMO constants)
- **Date**: 2025-12-25
- **Summary**
  - `lem:carleson-xi`: now **[~]** — the annular summation can be made uniform on Whitney scale using the recorded short-interval count `N(T;H) ≤ A₀ + A₁ H log⟨T⟩` (for `H≤1`) plus a crude RvM bound for larger windows.
  - `lem:zeta-normalization`: **[~]** — the potentially confusing `∂_σ Im log` cancellation can be justified cleanly using Cauchy–Riemann plus the boundary modulus relation `Re log(O_X/O_Z) = - Re log G` (no need to route through the `t`-derivative Hilbert statement).
  - `lem:hilbert-H1BMO`: **[~]** — initial draft had a scaling inconsistency; after fixing the mass‑1 test-field scaling to `‖∇V‖_{L^2(σ)} ≍ L^{-1/2}·𝒜(ψ)`, the argument is plausible but still should cite/justify the “Dirichlet test field” construction.
  - `lem:Mpsi-correct` / `lem:CE-constant-one`: still **[~]** — standard in principle, but the manuscript mixes “Whitney-only” Carleson constants with all-interval BMO characterizations and treats `C_CE(α)=1` as a normalization; both need to be made explicit if used quantitatively.

### Pass 4 — small internal repairs after Pass 3 (ξ annular sum; Hilbert test scaling)
- **Date**: 2025-12-25
- **Changes made**
  - `lem:carleson-xi`: adjusted the annular counting step to use the already-stated short-interval count `N(T;H) ≤ A₀ + A₁ H log⟨T⟩` for `H≤1`, plus a crude RvM bound for larger windows, yielding `∑ 4^{-k} ν_k ≲ 1 + L log⟨T⟩` and hence uniformity on Whitney scale.
  - `lem:hilbert-H1BMO`: fixed the mass‑1 test-field scaling to `‖∇V‖_{L^2(σ)} ≍ L^{-1/2}·𝒜(ψ)`, restoring a uniform-in-(T,L) bound.

### Pass 5 — ξ-energy / tested ξ-derivative cleanup (local vs global Carleson; annular kernel scaling)
- **Date**: 2025-12-25
- **Changes made**
  - `lem:annular-balayage`: fixed the diagonal `∫ K_σ^2` estimate so it has the correct Whitney scaling, and added a short explanatory note for the off-diagonal Schur-test aggregation.
  - `cor:xi-carleson-all-I`: downgraded from a misleading “uniform all-interval” Carleson statement to the correct **local-on-compact-I** formulation (constant depends on the fixed compact interval), which is what `lem:xi-deriv-L1` actually needs.
  - `lem:xi-deriv-L1`: rephrased the proof as a direct application of the Carleson embedding / H¹–BMO pairing theorem (Garnett VI.1.1 / Stein), rather than an ad hoc `‖∇V‖_2 ≲ ‖φ‖_{H^1}` claim.
  - `C_{\rm box}^{(\zeta)}` scope: clarified in the TeX that the certificate’s `C_{\rm box}^{(\zeta)}` is a **Whitney-scale** box-energy supremum (not a supremum over all intervals).

### Pass 1 — Chunk 0 (L1–L120): preamble + constants + conventions
- **Status**: [~] (first-pass notes recorded; may revisit after later sections)
- **What’s defined here**
  - **Gated numerics**: `\numericlockfalse`, `\shownumericsfalse`. Default mode is “symbolic/unconditional,” with optional numeric overrides inside `\ifnumericlock`.
  - **Fixed numeric lower bounds still present in default mode**:
    - `c_0(ψ)` is locked as `\czeroplateau=0.17620819` (used as a lower bound, not as an equality).
    - `K_0` is locked as `\Kzero=0.03486808` (arithmetic tail bound).
    - `C_ψ^{(H^1)}` is locked as `\CpsiHone=0.2400`.
  - **Symbolic box constant**: `\CboxZeta` expands to `K_0 + K_\xi` (symbolic unless numericlock).
  - **Potential naming ambiguity**:
    - `\CHzero=0.26` is described as an envelope `sup_t |H[φ_L](t)|` (PSC sum-form).
    - `\CHone=2/π` is described as a derivative constant `‖(H[φ_L])'‖_∞ ≤ CHone/L`.
    - In “Notation and conventions” later, the macro bullet says `C_H(ψ)=\CHone`. We must check later that the paper does not use `C_H(ψ)` inconsistently as an envelope constant vs derivative constant.
- **No issues yet**, but we should keep an eye on whether *any* load‑bearing inequality accidentally depends on turning on numeric locks or on the “diagnostic” `\UpsilonLocked`.

### Pass 1 — Chunk 1 (L121–L208): reader’s guide + dependency map + setup
- **Status**: [~]
- **High-signal checks**
  - Definitions of `Ω`, Poisson kernel, defect measure `ν`, balayage `μ`, windows `ψ_{L,t0}`, `φ_{L,t0}` look standard.
  - Standing properties:
    - (N1) “right-edge normalization” and (N2) “non-cancellation at ξ-zeros” are explicitly stated as proved later.
  - The paper provides a **clear load-bearing dependency map** (good for refereeing).
  - The intro clarifies there is only one active route; several alternative/archival routes are commented out.
- **Referee note**: The Abstract claims “all load-bearing steps are unconditional.” For the referee process, we treat this as a claim to be verified by checking that every load-bearing lemma reduces to standard theorems + explicit bounds, and that all “diagnostic numerics” are truly not used for closure.

### Pass 1 — Chunk 2 (L209–L340): phase–velocity core (start)
- **Status**: [~]
- **Items covered in this pass**: `lem:det2-unsmoothed`, `lem:desmooth-L1`, plus reading the use of these in `thm:phase-velocity-quant`.

#### `lem:det2-unsmoothed` (L209–L244)
- **Verdict**: looks correct modulo routine justification.
- **Checks**
  - Diagonal identity for det₂ and the series `-∑_{p}∑_{k≥2} p^{-ks}/k` is standard for diagonal HS operators (and consistent with later `lem:hs-diagonal`).
  - Termwise ∂σ is justified by absolute convergence on compacta in `Re s > 1/2`.
  - IBP twice: since `φ∈C_c^2(I)`, boundary terms vanish; bound `|∫ φ cos(ωt)| ≤ ‖φ''‖_{L^1}/ω^2` is correct.
  - Tonelli domination: each term bounded by `‖φ''‖ * p^{-kσ}/(k^2 log p)`; uniformity in σ follows from `p^{-kσ}≤p^{-k/2}`.
- **Action item**: none, unless we want to explicitly cite a standard det₂ product identity for diagonal HS operators (but the argument provided is already explicit).

#### `lem:desmooth-L1` (L252–L273) — **potential mismatch**
- **Key observation**: the lemma’s hypothesis is
  \[
    |\langle g_\varepsilon,\phi''\rangle| \le C_I \|\phi''\|_{L^1(I)} \quad \forall \phi\in C_c^\infty(I),
  \]
  i.e. the distribution is controlled when tested against **second derivatives**.
- **But** the det₂ tested bound we have is of the form
  \[
    \Big|\int \varphi(t)\,\partial_\sigma\Re\log\det_2(\cdots)\,dt\Big|
      \le C \|\varphi''\|_{L^1(I)},
  \]
  i.e. the distribution is controlled when tested against **\(\varphi\)** with a \(\varphi''\)-norm.
- In `thm:phase-velocity-quant` the text says: “Integrating σ and using `lem:desmooth-L1` yields
  \(\|u_\varepsilon-u_\delta\|_{L^1(I)}\le C|ε-δ|\).” This step is not immediate from the current statement of `lem:desmooth-L1`.
- **Referee action item (high priority)**:
  - Either (a) adjust `lem:desmooth-L1` to match the needed functional-analytic statement (distribution bounded by `‖φ''‖` implies existence of BV primitive and yields an L¹ Cauchy/Lipschitz estimate after integrating in σ), or
  - (b) add a short bridging argument explaining how the “test by φ with ‖φ''‖” estimate is converted into the “test by φ''” estimate used in `lem:desmooth-L1`, or
  - (c) replace the invocation of `lem:desmooth-L1` in `thm:phase-velocity-quant` with a direct argument proving the claimed L¹ Cauchy/Lipschitz bound.

#### `lem:neutralization-bookkeeping` (L275–L294) — preliminary read
- **Status**: [~] (read once; full verification deferred until we read `lem:CR-green-phase`, `B_I` construction, and the exact test field `V`)
- **Main idea**: subtract local Blaschke product `B_I` to neutralize near zeros/poles, then apply CR–Green pairing to `\widetilde U = Re log(J/B_I)`; bottom-edge term cancels with Blaschke phase increments already counted in `-w'`; remainder is side/top and is bounded by Cauchy–Schwarz + Dirichlet bounds for the test field + bounds on Blaschke gradients.
- **Referee checkpoints**
  - The “exact cancellation” statement needs a precise definition of `-w'` and of `B_I` (and how the phase-velocity identity partitions those contributions).
  - Ensure the bound on `∇Re log B_I` in `Q(α'I)` is uniform in Whitney parameters and depends only on aperture/geometry.
  - Ensure the remainder constant does **not** smuggle in any dependence on the (unknown) zeros beyond what is already bounded by the Carleson energy.

#### `lem:mu-to-lebesgue` (L298–L311) — Poisson lower bound ⇒ Lebesgue a.e. wedge
- **Status**: [?] (plausible but the proof is terse at the key step)
- **What it does**: “If μ(Q)=0 then |Q|=0” for the bad wedge set `Q = { |Arg J(1/2+it)-m| ≥ π/2 }`.
- **Referee note**: The argument sketches:
  1) choose `φ≤1_Q`, use phase–velocity identity  
  2) kill atomic sum by making `φ(γ)=0` near finitely many atoms in a compact interval  
  3) deduce `∫_Q (-w')=0` and hence `-w'=0` a.e. on `Q`  
  4) invoke boundary uniqueness to conclude `|Q|=0`.
- **Needs clarification**:
  - Explicitly justify “`-w'` positive boundary distribution ⇒ `-w'` is a positive measure,” so that “integral zero ⇒ a.e. zero” is legitimate.
  - Make the boundary uniqueness step explicit: which analytic/Hardy class function is being used, and how does “`w' = 0` on a set” force `Q` to have Lebesgue measure zero?
  - This lemma may be avoidable if later lemmas (e.g. explicit density positivity) provide a stronger route; but as written it is used to pass from μ-null to Lebesgue-null.

#### `lem:outer-phase-HT` (L315–L325) — outer/Hilbert identity
- **Status**: [~] (looks standard)
- **Referee note**: Standard Hardy/outer theory statement in distribution form. Check that the required regularity is satisfied: `u∈L¹_loc` is assumed, so `u'` is a distribution, Hilbert transform on distributions is classical.

#### `thm:phase-velocity-quant` (L326–L362) — quantified phase–velocity identity + boundary passage
- **Status**: [~]
- **What looks solid**
  - The combination “outer factorization + Blaschke contributions ⇒ Poisson terms + atoms” is standard in half-plane Hardy theory.
- **Main technical dependency**
  - The boundary passage has been rephrased to a **distributional** statement: from the tested σ-derivative bounds one gets a Lipschitz estimate
    \(|\langle u_\varepsilon-u_\delta,\phi\rangle|\le |\varepsilon-\delta|\cdot(\cdots)\),
    hence `u_ε` is Cauchy in `𝒟'(I)` and `H[u_ε']→H[u']` by continuity of the Hilbert transform on distributions.
  - Remaining referee checks here are about the **atomic term** in the ε→0 limit (critical-line zeros) and about making explicit which distribution is being named `-w'` (it is ultimately defined by the limiting identity).

### Pass 1 — Chunk 3 (L341–L465): balayage + wedge + det₂ continuity + smoothed PV
- **Status**: [~]

#### `lem:balayage-density` (L364–L376)
- **Status**: [~]
- **Assessment**: mathematically plausible and likely correct, but check one technical statement.
- **Notes**
  - If there exists at least one off-critical zero, each Poisson kernel term is strictly positive for all `t`, so the density `f(t)` should be strictly positive everywhere (not just a.e.), provided the series defining `f` is pointwise finite (or interpreted as `+∞`).
  - The proof references “Carleson energy finiteness implies the balayage of zeros on any Whitney box is finite, so the monotone limit … converges in L¹_loc.”  
    **Referee check**: confirm where the finiteness of `μ` on compact `t`-intervals is proved/guaranteed. (It should follow from the phase–velocity identity together with the upper bound coming from CR–Green/energy.)

#### `lem:whitney-uniform-wedge` (L381–L407)
- **Status**: [x]
- **Assessment**: the Whitney-local phase-drop inequality is consistent (Whitney scaling + CR–Green). The manuscript now explicitly treats the promotion to a global a.e. wedge (P+) as a separate (missing) local-to-global step (see `rem:wedge-application`).
- **Notes**
  - Uses only positivity `-w'` and the CR–Green inequality `∫ ψ(-w') ≤ C(ψ) * sqrt(energy)`.
  - Clean Whitney scaling: converts energy bound `≤ C_box * |I|` into `≤ const * sqrt(C_box) * L_*^{1/2}` and then chooses `c` small so `Υ_Whit(c)<1/2`.
  - **Dependency**: `C(ψ)` and the CR–Green inequality are defined later (`lem:CR-green-phase` etc). Must verify `C(ψ)` is truly uniform in `t0,L` and only depends on fixed window/aperture.
  - **Gap to close**: what is actually proved is a Whitney-scale phase-mass bound `∫_I (-w') ≤ π Υ_Whit(c)` for each Whitney interval `I`. The current `lem:local-to-global-wedge.(1)` requires a centered-exhaustion oscillation bound `osc_{[-N,N]} w ≤ D` (all N), which is not supplied by this lemma. Meanwhile `rem:wedge-application` describes a mass‑1 bump criterion. The paper needs an explicit bridge from the Whitney-scale inequality to the global a.e. wedge (P+), or else the wedge criterion statement should be replaced by the correct one being used.

#### `prop:hs-det2-continuity` (L417–L447)
- **Status**: [x]
- **Assessment**: standard functional analysis argument; the proof is concrete and checks out.
- **Notes**: Uses the identity `det₂(I-T)=det((I-T)e^T)` and a trace-norm series bound; the Lipschitz estimate on HS-balls is standard via `‖XY‖₁ ≤ ‖X‖₂‖Y‖₂`.

#### `lem:pv-test-smoothed` (L449–L464)
- **Status**: [~]
- **Assessment**: structurally correct (inner/outer decomposition yields Poisson kernels) and now stated purely as the **ε>0 smoothed identity**; the ε→0 boundary limit is handled in `thm:phase-velocity-quant`.
- **Referee checkpoints**
  - Confirm the stated boundary phase derivative for the half-plane Blaschke factor `C_ρ(s)` is exactly `-2(β-1/2-ε) P_{β-1/2-ε}(t-γ)` in the chosen normalization.
  - No longer depends on an `L¹_loc` convergence claim in this lemma; only the smoothed Hardy/inner–outer calculus needs checking.

### Pass 1 — Chunk 4 (L466–L578): globalization/pinch + (N1) normalization + RH statement
- **Status**: [~]
- **Assessment**: the pinch argument is standard once (P+) and (N1)/(N2) are in place; the only nontrivial part is ensuring hypotheses match exactly.
- **Notes**
  - Poisson transport `Re F ≥ 0` on `Ω\Z(ξ)` from boundary a.e. inequality is standard (harmonic extension). Needs: `Re F` is harmonic on rectangles avoiding zeros.
  - Cayley/Schur step uses the identity `1-|Θ|² = 4 Re F/|F+1|²`.
  - Removability + max modulus: standard; requires connectedness of `Ω\(Z(ξ)\{ρ})`. The paper provides `rem:connectedness`.
  - **Normalization at infinity (N1)** uses:
    - ζ/gamma growth (standard)
    - det₂→1 as σ→∞ (standard from product formula)
    - boundedness of outer factor `𝒪` on vertical strips, via “Carleson embedding inequality” + `lem:poisson-bmo-strip` (to be checked later; this is one of the deepest analytic pieces in the paper).

### Pass 1 — Chunk 5 (L579–L760): Carleson energy bookkeeping + ξ tested bound + (N2) + ζ-normalization
- **Status**: [~]

#### `lem:carleson-sum` (L579–L593)
- **Status**: [x]
- **Assessment**: correct (pointwise Cauchy–Schwarz on each Carleson box, then take supremum).

#### `cor:xi-carleson-all-I` (L595–L604)
- **Status**: [~]
- **Assessment**: the statement has been weakened to a **local (compact-I) Carleson bound** with constant depending on `I`. In that form it is plausible and matches what `lem:xi-deriv-L1` actually needs. The proof is still sketch-level (finite cover by Whitney intervals + bounded overlap), but this is standard and should be easy to expand if desired.
- **Referee checklist**
  - Specify the finite Whitney cover of a fixed compact interval `I` (e.g. a Vitali selection for the variable scale `L(t)`), and record an explicit overlap bound.
  - Confirm `Q(I) ⊂ ⋃_j Q(α I_j)` in the chosen construction.

#### `lem:xi-deriv-L1` (L606–L626)
- **Status**: [~]
- **Assessment**: now phrased as a direct application of the **Carleson embedding / H¹–BMO pairing theorem** (Garnett VI.1.1 / Stein), together with the local Carleson-energy bound on $Q(I)$ for fixed compact $I$ (`cor:xi-carleson-all-I`). This is the right abstraction; a referee may still want the precise definition of the local `H^1(I)` norm used here (area function) stated once.
- **Referee checkpoints**
  - Ensure `H^1(I)` is explicitly defined (e.g. via Lusin area function on cones of aperture $\alpha$) and matches the cited Carleson embedding theorem.
  - Confirm the local Carleson constant in `cor:xi-carleson-all-I` is sufficient for the fixed dilation `Q(\alpha I)` used here.

#### `cor:conservative-closure` (L627–L646)
- **Status**: [x] (patched to be symbolic by default; diagnostics gated)
- **Notes**
  - The corollary statement is now **symbolic** (no numeric plugging) in the default flow; the optional numeric plug-in is behind `\ifshownumerics`.
  - Still confirm later sections do not accidentally use any diagnostic numeric `Υ_diag` for a load-bearing step (closure is via `Υ_Whit(c)`).

#### (N2) proof block + `lem:hs-diagonal` (L648–L667)
- **Status**: [x]
- **Assessment**: correct for the diagonal prime operator `A(s)`.
- **Notes**: This is important for the pinch: it guarantees `det₂(I-A(ρ)) ≠ 0` at ξ-zeros in `Ω`.

#### `lem:zeta-normalization` (L671–L707) + “No CP/CGamma” corollary (L711–L716)
- **Status**: [~]
- **Assessment**: conceptually sound; the key cancellation `∂_σ Im log(O_X/O_Z) = -∂_σ Im log G` can be justified cleanly from Cauchy–Riemann plus the boundary modulus relation `Re log(O_X/O_Z) = -Re log G` (distributionally on the boundary).
- **Referee checklist**
  - Double-check the sign conventions: which term is being claimed to vanish on the boundary (phase derivative), and how the ratio of outers cancels the `Γ/π` factor via `lem:outer-phase-HT`.
  - Confirm the Blaschke compensator `B(s)=(s-1)/s` is the correct half-plane factor for the simple pole/zero at `s=1` in the ζ-normalized gauge and that `|B|=1` on `Re s=1/2`.
  - Make sure the argument clarifies what regularity is used to interpret boundary CR identities in `𝒟'(ℝ)` (this is standard for analytic functions with `L¹_loc` boundary traces).

### Pass 1 — Chunk 6 (L761–L918): window/Hilbert constants + a numeric block + outer normalization setup
- **Status**: [~]

#### `lem:CH-derivative-explicit` (L722–L782) — Hilbert transform derivative envelope
- **Status**: [~]
- **Assessment**: the scaling reduction is standard; the “worst case between ramps” argument is plausible but uses an informal rearrangement/endpoint principle.
- **Referee checklist**
  - Verify the “endpoint principle” bound in Step 3 carefully (monotone kernel + monotone density). If needed, replace with a short rigorous argument (e.g. compare against a point mass at the endpoint via Chebyshev sum inequality / monotone rearrangement).
  - Check Step 4 claim (“outside plateau strictly smaller”) is not required for the stated bound; the stated proof effectively only needs a global sup bound, so Step 4 could be shortened/removed if it’s delicate.

#### Ungated numeric block: “Certificate — weighted p-adaptive model at σ₀=0.6” (L787–L861)
- **Status**: [x] **fixed**
- **Notes**
  - This block is now wrapped in `\ifshownumerics ... \fi`, so it is **off by default** and no longer conflicts with the paper’s gating claim.

#### `cor:det2-boundary` (L862–L871)
- **Status**: [x]
- **Assessment**: direct restatement of `lem:det2-unsmoothed` with a σ-shift; fine.

#### `prop:outer-central` (L874–L883) — outer normalization existence/limit
- **Status**: [x] (patched)
- **Assessment**: updated to cite the Carleson⇒BMO boundary trace theorem (`lem:desmooth-L1`) for the required `L¹_loc` convergence, and then uses the standard Poisson/outer representation for local-uniform convergence of outers.

### Pass 1 — Chunk 7 (L884–L1118): Carleson energy backbone (prime tail + ξ) + cutoff pairing
- **Status**: [~]

#### `lem:carleson-arith` (L887–L904)
- **Status**: [x]
- **Assessment**: correct. The single-mode bound reduces to `sup_{a>0} ∫_0^{a} x e^{-2x} dx = 1/4`.

#### `lem:annular-balayage` (L919–L955)
- **Status**: [~]
- **Assessment**: plausible, with a long but standard diagonal/off-diagonal kernel estimate.
- **Referee checkpoints**
  - Confirm the off-diagonal step “Schur test” is stated precisely enough (or replace with a short lemma about convolution-type kernels on an interval).
  - Check constants and scaling: the claimed `|I| 4^{-k} ν_k` is a deliberately weak but sufficient bound; ensure no hidden dependence on `T` appears.
  - **Note (recent patch)**: the diagonal estimate should use
    `K_σ(x)^2 = (σ/(x^2+σ^2))^2 ≤ (σ/d^2)·K_σ(x)` on `|x|≥d`,
    hence `∫_I K_σ(·-γ)^2 ≤ (σ/d^2)∫_ℝ K_σ = πσ/d^2` with `d≈2^{k-1}L`. This gives the correct Whitney scaling after integrating in `σ`.

#### `lem:carleson-xi` (L957–L1004)
- **Status**: [~]
- **Assessment**: The overall strategy is standard: neutralize near zeros, bound far-field via annular decomposition + local zero count, then use Whitney scale to make the sum `O(1)`.  
  But a referee will likely ask for more explicit detail in two places.
- **Referee checkpoints**
  - **Neutralization**: precisely define the half-plane Blaschke product `B_I` on the chosen dilate and justify the energy comparability
    `∬ |∇U_ξ|^2 σ ≍ ∬ |∇Ũ_ξ|^2 σ + O(|I|)`.
  - **Harmonic gradient equivalence**: the step “`|∇U|^2 ≍ |∂_σ U|^2`” should be justified (it’s true up to constants because `|∇U|^2 = (∂_σ U)^2 + (∂_t U)^2` and Cauchy–Riemann gives `∂_t U = -∂_σ V`, etc; but the proof should be explicit about what is being bounded).
  - **Zero count input**: the clean way to close the annular sum uniformly is to use the short-interval count stated earlier in the manuscript (`N(T;H) ≤ A₀ + A₁ H log⟨T⟩` for `0<H≤1`), plus a crude RvM bound for the finitely many annuli with `2^kL>1`. With this split, `∑ 4^{-k} ν_k ≲ 1 + L log⟨T⟩`, hence `O(1)` on Whitney scale `L=c/log⟨T⟩`.

#### `prop:Kxi-finite` (L1006–L1020)
- **Status**: [~]
- **Assessment**: correct assuming `lem:carleson-xi` + `lem:carleson-arith` + `lem:carleson-sum`.

#### `lem:cutoff-pairing` (L1099–L1127)
- **Status**: [~]
- **Assessment**: standard Green identity + cutoff decomposition.
- **Referee checkpoint**: confirm the exact regularity assumptions on `Ũ` to apply Green’s identity on the box with cutoff (usually fine after neutralization), and clarify what object is denoted by the boundary symbol `u(t)` in the bottom-edge identity (it looks like it should be the phase distribution `-w'` tested against `ψ_{L,t0}` rather than a modulus function).

### Pass 1 — Chunk 8 (L1130–~1275): CR–Green pairing + outer cancellation + “sharp Kξ” bookkeeping + admissible tests
- **Status**: [~]

#### `lem:CR-green-phase` (L1130–L1151)
- **Status**: [~]
- **Assessment**: core identity is standard (Green + CR on bottom edge). The “uniform constant” extraction into `C(ψ)` depends on bounding the Poisson test energy uniformly in `L,t0`.
- **Referee checkpoint**: ensure the test-energy bound is proven once (it’s later referenced via `𝒜(ψ)`), and that it is independent of the Whitney scale.

#### `lem:outer-cancel` (L1152–L1160) + remainder corollary (L1161–L1176)
- **Status**: [~]
- **Assessment**: plausible; needs careful bookkeeping to avoid circularity (“outer contribution already subsumed in -w′”).
 - **Referee checkpoint**: the proof uses a term written as `\mathsf H[u']`; ensure notation is consistent with the global Hilbert transform macro `\Hilb` and spell out precisely which outer-term is being cancelled (and where it was incorporated into `-w'`).

#### `lem:outer-energy-bookkeeping` (L1179–L1228) — **high-signal**
- **Status**: [~]
- **Key point**: this is where the paper explains why the paired energy can be taken as **ξ-only** (`K_ξ`) after outer cancellation.
- **Referee checkpoint**
  - Verify `U_0 = Poisson[u_0]` is legitimate (requires non-tangential boundary values for `log det₂`, which should follow from analyticity and nonvanishing).
  - Verify the claim “`U_ξ - Poisson[u_ξ]` is the neutralized Green potential of zeros” matches the neutralization used in `lem:carleson-xi`.
  - Clarify the meaning of the boundary function `u_ξ(t):=\log|\xi(1/2+it)|` at critical-line zeros (where it is `-∞`) and how the “outer on Ω with boundary modulus `exp(u_0-u_ξ)`” is defined in the presence of these atoms/singularities. This ties directly into the still-open boundary passage / outer-normalization issue.

#### `def:admissible-class` + `lem:uniform-CRG-A` (L1242–L1274)
- **Status**: [~]
- **Assessment**: framework looks sound; the key is ensuring the existence of an atom-safe admissible family and that its energy bound `A_*` is truly uniform.

#### Continuation: `cor:atom-safe` + `rem:wedge-application` (L1299–L1327) — **wedge closure mismatch**
- **Status**: [x] (issue is now explicitly isolated in the TeX)
- **What’s good**
  - `cor:atom-safe` is straightforward given the phase–velocity identity: if the test function vanishes at atoms, the discrete sum is killed.
- **Issue (open load-bearing step)**  
  - The TeX now explicitly states that a \emph{global} a.e. boundary wedge after a single rotation does **not** follow from Whitney-local bounds alone, and it isolates the missing “Whitney-local ⇒ global (P+)” implication as the remaining open step.
- **Counterexample (shows the naive implication “Whitney-local phase-mass bound ⇒ global a.e. wedge” is false without extra hypotheses)**  
  Let `J(s):=exp(-a(s-1/2))` on `Ω={Re s>1/2}`. Then `|J(1/2+it)|=1` a.e. and the boundary phase can be taken as `w(t)=-a t`, so `-w' = a\,dt` is a positive Radon measure.  
  For any Whitney interval `I` with `|I|=2L≤2L_*`, one has `∫_I (-w') = a|I| ≤ 2aL_*`. Choosing `a ≤ (πΥ)/(2L_*)` makes `∫_I (-w') ≤ πΥ` hold on **every** Whitney interval with any fixed `Υ<1/2`.  
  However `Re J(1/2+it)=cos(at)` changes sign on sets of positive measure, so (P+) fails for every unimodular rotation.  
  **Referee takeaway**: to deduce (P+) from Whitney-local bounds, the manuscript needs an additional ingredient controlling *global phase drift* / excluding an “exponential inner factor” (a singular component at infinity) in the inner/outer calculus.
- **Action items (make this referee-checkable)**
  - Decide which wedge-closure interface is intended, and make the hypotheses match the actually-proved inequalities:
    - either prove a **centered-exhaustion oscillation bound** `osc_{[-N,N]} w ≤ π·Υ` (all `N`) and then apply a local-to-global lemma (as in the BRF formalization), or
    - replace `lem:local-to-global-wedge` with the correct criterion that uses the **mass‑1 admissible class** and prove (or cite) the resulting global a.e. wedge.
  - Make explicit where the *global rotation* (the unimodular constant ambiguity in the outer normalizer) is fixed, since (P+) is a statement about the rotated boundary phase.

### Pass 1 — Chunk 9 (L1328–~1470): BMO/Carleson → window constants; Hilbert pairing; printed window + plateau
- **Status**: [~] (partial)

#### `cor:CH-Mpsi-final` (L1328–L1350)
- **Status**: [~]
- **Assessment**: bookkeeping only; depends on `lem:Mpsi-correct` + `lem:hilbert-H1BMO` + Carleson embedding constant normalization.

#### `lem:poisson-bmo-strip` (L1351–L1366)
- **Status**: [x]
- **Assessment**: standard BMO → bounded Poisson extension on fixed height strips; proof sketch is fine.

#### `lem:hilbert-H1BMO` / `lem:hilbert` (L1370–L1394)
- **Status**: [~]
- **Assessment**: after fixing the scaling for the mass‑1 test window energy (the test-field should scale like `L^{-1/2}`), the argument is plausible: local box pairing + Carleson energy gives a uniform-in-(T,L) bound. It still depends on the (now [~]) ξ Carleson-energy lemma for the neutralized area bound.
  - existence/definition of the affine calibrant `ℓ_I`
  - the “Dirichlet test field” for `(H[φ_I])'` with the claimed energy scaling
  - and the neutralized energy bound from `lem:carleson-xi`.

- **Referee check**: ensure the “Dirichlet test field” construction is either cited (standard H¹ square-function representation) or sketched enough that the `L^{-1/2}` scaling is clear.

#### Printed window + Poisson plateau (`lem:poisson-plateau`, L1400–L1440)
- **Status**: [x]
- **Assessment**: correct; monotonicity argument to locate infimum at `(x,b)=(1,1)` is standard.

#### Continuation: `lem:CH-derivative-2pi` + `lem:Mpsi-correct` + prime-tail bounds (L1471–L1599)
- **Status**: [~]
- **Notes**
  - `lem:CH-derivative-2pi` is a quick corollary of the earlier envelope/derivative arguments; fine.
  - `lem:Mpsi-correct` is standard H¹–BMO duality + Carleson embedding; however, the statement currently uses a **Whitney-only** box constant `C_box^(Whitney)` while the Carleson/BMO characterization is normally stated with a supremum over **all** intervals. Either (i) replace `C_box^(Whitney)` by the all-interval version (using `cor:xi-carleson-all-I`-type extension), or (ii) explicitly justify why Whitney control suffices for the `H^1` test family used here.
  - The “Numeric instantiation (diagnostic; gated)” appendix section is not wrapped in `\ifshownumerics` (it is, however, explicitly labeled diagnostic). This is now consistent with the updated reader-guide language (“gated or diagnostic appendices”).
  - Prime-tail bounds (`eq:P1`, `eq:P1uniform`, Dusart/integer alternatives) are classical and appear correct.

### Pass 1 — Chunk 10 (L1600–L1748): finite-block certificate material + rectangle limit + Schur/Herglotz closure
- **Status**: [~]
- **Notes**
  - The finite-block spectral gap / truncation tail control sections appear to be **auxiliary / alternative-route** material. They are not referenced in the load-bearing chain; consider moving to an appendix or gating them to preserve the “single route” narrative.
  - Load-bearing items here:
    - `thm:limit-rect`, `cor:Schur-off-zeros`, `lem:removable-schur`, `cor:poisson-herglotz`, `cor:cayley-schur`, `thm:globalize-main`, `cor:RH`.
    - These are standard complex-analysis/Herglotz/Schur arguments and look correct **assuming (P+) is actually established**.
  - **Global dependency reminder**: regardless of how clean the pinch is, the paper still needs a correct, explicit bridge “Whitney-uniform phase-mass bound ⇒ (P+)” (currently flagged unresolved).

### Pass 1 — Chunk 11 (L1749–L1959): appendices + numeric protocols + bibliography
- **Status**: [~]
- **Notes**
  - `lem:CE-constant-one` is more a **normalization choice** than a theorem: passing from `Q(I)` to `Q(α I)` changes constants by an α-dependent factor. If the paper uses it quantitatively, it should either (i) keep an explicit `C_CE(α)` throughout, or (ii) define `C_CE(α)` so that it equals 1 by convention and explicitly note what geometric dilation is being absorbed.
  - The “Numerical evaluation of `C_ψ^{(H^1)}`” appendix describes an interval-arithmetic protocol but does not include code or explicit error bounds beyond a summary. If this is intended for external audit, consider adding a reproducibility artifact (script or detailed parameter list).
  - Bibliography looks consistent with cited items (Garnett, Duren, Stein, Titchmarsh, etc.).

---

## D. Referee template (copy/paste per lemma)

Use this template under each lemma as we start review:

```text
### <label> (<type>, Lstart–Lend): <title>
- Status: [ ] / [~] / [x] / [!] / [?]
- Reviewer:
- Date started / completed:

#### Claim (restate)
...

#### Dependencies (internal)
- Depends on:

#### External results used (cite + hypotheses)
- ...

#### What must be checked (mechanical checklist)
- [ ] Domain assumptions match later usage
- [ ] Differentiation/integration justified (Fubini/Tonelli, dominated convergence)
- [ ] Boundary limits handled correctly
- [ ] Constants and scaling in L are correct
- [ ] Any “almost everywhere” statements are used safely
- [ ] Any “atoms” / exceptional sets handled

#### Outcome
- ...

#### Action items
- ...
```

---

## E. “Axiom-like” dependencies to watch for (paper-level)

Even if the paper is “unconditional,” some steps rely on deep standard theorems. We will track any use of:
- Carleson measure characterizations of BMO / H¹–BMO duality
- boundary uniqueness theorems for Smirnov/Hardy classes on half-planes/rectangles
- zero-density bounds used with explicit constants (Vinogradov–Korobov / RvM short interval counts)
- continuity/analyticity properties of det₂ and the HS topology

Each time we encounter one, we must record:
- exact theorem statement needed,
- where it is proved/cited,
- whether the hypotheses are satisfied in-context.


