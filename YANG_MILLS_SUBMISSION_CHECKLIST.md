### Purpose (read this first)

You are working on making `Yang-Mills.tex` **submission-ready for a top-tier math journal** while keeping all “unconditional vs conditional” claims honest and auditable.

This file is a **living prompt + checklist**. Use it at the start of every session to decide what to do, and update it as you discover new submission blockers.

---

### Session trigger (run at the start of every session)

- **Step 0 — Load context**
  - Read: `Yang-Mills.tex`
  - Read: `YANG_MILLS_PROOF_TRACK.md` (especially the ledger table and the “Main-chain claim map”)
  - Read the active operational plans (as needed):
    - `UCIS_OPERATIONAL_PLAN.md` (interface smoothing / minorization)
    - `U1_OPERATIONAL_PLAN.md` (UEI/tightness on fixed regions; Track-J vs raw small-field)
    - `OS1_OPERATIONAL_PLAN.md` (Euclidean invariance route decision + dependencies)
    - `U2_OPERATIONAL_PLAN.md` (U2b bridge / operator-norm NRC blocker; B1–B2 plan)

- **Step 1 — Identify the single highest-impact blocker**
  - A blocker is something that would make a referee stop: an unproved load-bearing claim, an undefined object, an unjustified limit/interchange, a missing hypothesis, a mis-stated “unconditional” claim, or a citation without theorem number when a theorem number exists.
  - If you cannot name *one* blocker, **do not edit the paper**. Instead, write a short list of “next questions to resolve” and stop.

- **Step 2 — Choose the minimal edit that removes the blocker**
  - Prefer: add a lemma, tighten a statement, add an explicit reference (with theorem number), insert a short proof, or isolate a deep external input into a named lemma.
  - Avoid: global rewrites, notation refactors across the file, reordering sections for aesthetics, or “beautifying”.

- **Step 3 — Execute + record evidence**
  - Make the change in `Yang-Mills.tex`.
  - Update `YANG_MILLS_PROOF_TRACK.md` (ledger / checklist / main-chain map).
  - If relevant, update the specific operational plan (`UCIS_OPERATIONAL_PLAN.md`, `U1_OPERATIONAL_PLAN.md`, `OS1_OPERATIONAL_PLAN.md`).

- **Hard stop rule**
  - If after 60–90 minutes you didn’t remove a blocker, stop and write down exactly what is missing (a specific lemma, a reference, a computation, a uniformity check), so the next session can begin there.

---

### Anti-perpetual-improvement rule (do not violate)

Only make edits that satisfy **at least one** of:

- **Correctness**: fixes a real mathematical error or closes a logical gap.
- **Referee survivability**: adds missing definitions/hypotheses/citations needed to justify a step.
- **Dependency clarity**: isolates a deep external input into a clearly labeled lemma/proposition and cites the best source.
- **Reproducibility**: makes constants/uniformities auditable (what depends on \(a,\beta,L\), what does not).
- **Navigation**: improves the reader’s ability to find where something is proved (roadmap, lemma pointers, “used in” remarks).

Edits that do *not* count (unless they unlock one of the above):

- rewriting for style/tone/flow
- reorganizing sections for aesthetics
- renaming notation across many pages
- adding motivational prose

---

### Definition of “submission-ready” (acceptance criteria)

This project has two “readiness levels”; we should be explicit which one we are targeting at any given time.

#### A. Referee-survivable roadmap (honest conditional preprint)

The manuscript is referee-survivable when:

- **No hidden assumptions** in the load-bearing chain. If something is RG-grade, it is clearly labeled as such (assumption/target/ledger item).
- **Every load-bearing imported theorem** has a **precise citation** (paper/book + theorem number + hypotheses checked against our setting).
- **Every object is defined before use** (kernels, measures, embeddings, calibrators, defect operators, projectors, schedules).
- **All limit/interchange steps used in the main chain** are explicitly justified or precisely cited (dominated convergence, tightness, Fubini/Tonelli, continuity of semigroups, OS reconstruction).
- **All “unconditional” language is accurate** (lattice-only vs continuum). Any “Clay-level” language is gated behind a clearly named hypothesis set.
- **LaTeX compiles cleanly** with a standard toolchain and the bibliography is complete.

#### B. Clay/Millennium-ready (unconditional YM + mass gap)

Everything in (A), plus:

- **No RG-grade assumptions remain** in the continuum chain: the fixed-region inputs (U1, OS1) and NRC uniqueness inputs are proved (or reduced to standard external theorems with theorem numbers).
- **Uniformities are correct** (in \(a\downarrow 0\), van Hove \(L\to\infty\), scaling schedules, boundary conditions).

---

### File/packaging requirements (journal mechanics)

- **Single source of truth**: `Yang-Mills.tex` is the canonical manuscript.
- **Compilation**: `pdflatex -halt-on-error Yang-Mills.tex` (and bib passes) should work without local paths. ✅ (2025-12-25: `pdflatex` completes with **no undefined references/citations**; `lastpage` is optional (footer degrades gracefully when absent); and hyperref PDF-bookmark warnings have been eliminated by bookmark-safe headings.)
- **Bibliography hygiene**:
  - Every deep imported theorem has a strong reference with theorem number where possible.
  - No “folklore” statements in the load-bearing chain without citations.
  - URLs are acceptable only as a secondary pointer; they should not be the only evidence.

---

### Mathematical correctness checklist (load-bearing chain)

This is not a full proof inventory (that lives in `YANG_MILLS_PROOF_TRACK.md`); it’s the referee-facing “red flag list”.

#### 0) Global honesty audit (do this often)

- **0.1 Unconditional language**: “unconditional” is used only for lattice-only statements, unless the continuum inputs are actually proved. ✅ (2025-12-25: audited Abstract + Main Theorem/Clay pack + the earlier E1/E2 global theorem block; continuum NRC/gap/OS→Wightman statements are explicitly conditional on UCIS\(_{\rm SW}\) + fixed-region inputs and, in particular, `assump:U2b`.)
- ✅ (2025-12-25: title/front-matter) Title and PDF metadata now explicitly label the continuum construction as **conditional**, matching the abstract and the dependency story.
- **0.2 Conditional language**: the scaling-window interface closure is explicitly stated as such (UCIS\(_{\rm SW}\) under `eq:ucis-sw-window`). ✅ (2025-12-25: front-matter + Clay/global pack now consistently reference UCIS\(_{\rm SW}\) / `prop:os35-limit`; legacy one-step coarse-refresh route explicitly marked “not used in main chain”.)

#### 1) Lattice OS structure and transfer operator (fixed \(a\))

- **1.1 OS2 / transfer**: `thm:os` and the OS/GNS transfer construction are fully proved and internally consistent.
- **1.2 Interface kernel definition**: the “one tick”/interface Markov kernel is precisely defined and its factorization/locality hypotheses are explicit.

#### 2) Interface smoothing / minorization (gap mechanism)

- **2.1 Active closure**: interface smoothing is currently closed by **UCIS\(_{\rm SW}\)**:
  - `thm:ucis-sw` under `eq:ucis-sw-window`
  - Track-B analytic core: `lem:scaled-ball-to-hk`
  - External input (now cited): `lem:ballwalk-diffusive` (Hebisch–Saloff-Coste 1993, Thm 5.1)
- **2.2 Downstream callsites**: no remaining “one-step unconditional Doeblin” language in load-bearing parts; all callsites accept UCIS\(_{\rm SW}\). ✅ (2025-12-25: Main theorem box / referee quick-check / reader’s guide / constants table + Clay map + Clay-critical theorems + the earlier E1/E2 global theorem block now consistently use UCIS\(_{\rm SW}\) (scaling-window) and remove “β-uniform one-step Doeblin” overclaims; any coarse-refresh material is labeled legacy/not-main-chain.)
  - ✅ (2025-12-25: Appendix U referee checklist bullets updated to reference UCIS\(_{\rm SW}\) (and mark the schedule-free one-step Doeblin route as legacy/not main chain).)

#### 3) Fixed-region tightness / U1 (two closure routes)

- **3.1 Theorem shape**: `thm:uei-fixed-region` is explicitly split:
  - **Route A (raw small-field)**: `lem:U1-B-smallfield` + `assump:uei-mean` + Lipschitz/LSI payload.
  - **Route J (Track-J)**: `lem:U1-J1-smoothed-lsi` + `lem:U1-J2-universality`.
- **3.2 Track-J hygiene**:
  - `lem:U1-J1-smoothed-lsi` cites a named single-site input: `lem:heatkernel-lsi-compactG`.
  - `lem:heatkernel-lsi-compactG` has a precise reference path (LSI on Haar + Holley–Stroock bounded perturbation).

#### 4) OS1 (Euclidean invariance)

- **4.1 Route decision**: primary = calibrator route; commutator route is optional cross-check.
- **4.2 Dependencies**: calibrator construction + isotropy defect bounds are explicit; any use of UEI/equicontinuity is clearly stated.
- **4.3 Optional commutator route**: any invocation of `TS:sandwich_main` is clearly marked “outline-only / optional”.
  - ✅ (2025-12-25: commutator-route hygiene) The commutator-route chain (`thm:emergent-sym`, `lem:local-commutator-Oa2`, `prop:resolvent-from-commutator`) is explicitly labeled **optional cross-check**, and its reliance on the outline-only sandwich input `TS:sandwich_main` is explicit. Also the embedding notation there now uses `I_{a,L}` (no collision with the comparison-model `J_a`).
- **4.4 Classical DEC input hygiene**: `DEC:plaquette-F2` has a proof that matches its statement (classical plaquette holonomy/BCH expansion, with explicit coupling normalization and technical hypotheses). ✅ (2025-12-25: fixed a proof/statement mismatch; see session log in `YANG_MILLS_PROOF_TRACK.md`.)

#### 5) U2 / NRC uniqueness / operator-norm convergence

- **5.1 Deep quantitative inputs**: graph-defect control, low-energy projector bounds, and resolvent comparison are either proved or isolated as explicit RG-grade assumptions/targets. ✅ (2025-12-25: isolated as `assump:U2b` and rewired major callsites; also fixed notation collision so embedding/isometry defect uses `C_{\rm iso}` rather than overloading `C_D`.)
- **5.2 Hypotheses checked**: wherever operator-norm resolvent convergence is used, the hypotheses are spelled out (domain/core, uniform bounds, compactness arguments). ✅ (2025-12-25: key operator-norm NRC/gap callsites explicitly reference `assump:U2b` rather than implying U2 is proved.)
- **5.3 Single crisp remaining U2 blocker**: proving `assump:U2b` requires a quantitative **bridge lemma** relating the OS/GNS embedding-side objects \((I_{a,L},H_{a,L},H)\) to a concrete discretization/comparison model where $O(a)$ defect/projector bounds are proved (e.g. the fixed-slab $J_a$ model or the calibrated slab model). This bridge is currently **RG-grade / BLOCKED**; see `YANG_MILLS_PROOF_TRACK.md` ledger entry **#26** and the in-text target statement `lem:bridge-U2b-target` (under `assump:U2b`). The comparison-side low-energy approximation \(\|(I-J_a^*J_a)E_H([0,\Lambda])\|\lesssim a\) is now supplied in-text by `lem:cell-avg-lowenergy`, so the remaining bridge inputs are the true quasi-unitary matching conditions (B1)–(B2). (Note: because U2b’s defect input is stated in the two-sided graph-weighted form, (B1) now includes the corresponding $(H+1)^{1/2}$ / $(H_{a,L}+1)^{1/2}$ graph-control needed to actually imply that defect bound.)
  - ✅ (2025-12-25: bridge formulation tightened) The remark after `lem:bridge-U2b-target` now gives an explicit **form-level graph-boundedness criterion on an operator core** for (B2) (a bilinear estimate for $V_{a,L}^*H_aV_{a,L}-H_{a,L}$ relative to the $(H_{a,L}+1)^{1/2}$ norm; conceptually aligned with `NRC:form` / `NRC:form-thm` without overstating an implication from abstract form convergence alone), and explains (B1) as a deterministic geometric approximation between the polygonal/smoothed embedding (`I_{a,L}`) and the piecewise-constant extension (`J_a^*`) after identifying lattice degrees of freedom.

#### 6) Gap persistence and OS → Wightman export

- **6.1 Gap persistence**: `thm:gap-persist-cont` states exactly what mode of convergence is assumed and what spectral conclusion follows.
- **6.2 Export**: OS0–OS5 and OS→Wightman statements cite a standard reference and match the function class/observables actually constructed.

---

### Current route decisions (as of 2025-12-24)

- **Interface smoothing**: UCIS\(_{\rm SW}\) (scaling-window) is the active closure (`thm:ucis-sw` + `eq:ucis-sw-window`).
- **U1 (fixed-region tightness)**: Track-J is the preferred closure path; raw small-field route remains an optional/parallel target.
- **OS1 (Euclidean invariance)**: calibrator route is the mainline; commutator route is a cross-check.

---

### How to update this file

- When you find a new submission blocker:
  - Add a bullet above (in the relevant section) with:
    - **what** is missing/wrong,
    - **where** (label/section),
    - **why it matters** (load-bearing?),
    - **what evidence closes it** (proof vs citation + theorem number).
- When you fix something:
  - Mark it with **✅** and include the label(s) and/or the exact theorem reference added.


