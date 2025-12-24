## UCIS (Uniform Coarse Interface Smoothing) — Operational Plan

**Date**: 2025-12-23  
**Purpose**: Define a single, sharply targetable *classical* theorem that would close the key lattice-side blocker in `Yang-Mills.tex`, together with an executable decomposition into sublemmas and a repo-facing checklist.

---

## Current implementation status (in this repo)

- **Wired into the manuscript**:
  - UCIS is now present in `Yang-Mills.tex` as `thm:ucis`, with lemma stubs `lem:ucis-A-*` … `lem:ucis-E-*` and a bookkeeping corollary `cor:ucis-L2-contraction`.
  - The chosen Track B replacement is now also wired in as the **scaling-window** variant `thm:ucis-sw` (UCIS\(_{\rm SW}\)), together with its core analytic target `lem:scaled-ball-to-hk` and window hypothesis `eq:ucis-sw-window`.
- **Proved/reduced pieces**:
  - **UCIS-A** is now proved as a reduction to existing coarse-interface geometry (`lem:coarse-interface-construction`, `lem:cell-disjoint-links`).
  - **UCIS-D** is proved as a clean reduction to factorization (`lem:plaquette-factorization`) once UCIS-C holds.
  - **UCIS-E** is now proved as a reduction to compact-group smoothing (`lem:ball-conv-lower`) in increment coordinates consistent with `P_{t_0}(U,·)`.
  - Added an unconditional one-link helper lemma `lem:one-link-ball-maximizer-unif` (β-uniform *mass* near the polar maximizer), useful for diagnosing why fixed-radius **measure** minorization is harder.
- **Still open (core blocker)**:
  - **Unconditional UCIS-C** remains blocked: a truly β-uniform *single-cell* **measure** minorization / refresh mechanism.
  - **Track B (scaling-window) status**: `lem:scaled-ball-to-hk` is now implemented in `Yang-Mills.tex` and the remaining analytic input `lem:ballwalk-diffusive` is now **precisely cited + hypothesis-checked** in-text via Hebisch–Saloff-Coste (1993), Theorem 5.1 (Gaussian lower bound for convolution powers on groups). The purely algebraic piece `lem:central-mixture-binomial` is proved in-text.
  - We now have an explicit **one-link no-go** lemma (`lem:no-unifball-doeblin-fixed-radius`) showing that fixed-radius β-uniform domination by the **uniform ball law** cannot hold even for the basic one-link matrix-Fisher conditionals. This clarifies that UCIS-C cannot be obtained by “one-link Doeblin at fixed radius” and must instead come from an additional **cell-level smoothing/pulse** or a **physically scaled multi-step** mechanism.

---

## UCIS-C replacement mechanisms: Pulse/Sandwich vs Physically Scaled Multi-Step (work-through + best track)

We now need to decide how to replace UCIS-C with something that can plausibly be proved classically and that actually plugs into the existing contraction/gap chain.

### Track A — Pulse/Sandwich route (smoothing-based)

**Target shape.** Prove a *cell/interface-level* lower bound by a strictly positive “pulse” kernel (ideally a heat-kernel pulse) with constants independent of \((\beta,L,a)\), e.g.
\[
  K_{\mathrm{cell}}^{M}(U,\cdot)\ \ge\ c_*\,P_{t_*}(U,\cdot).
\]

**What exists in `Yang-Mills.tex` today.**
- `prop:sandwich-pulse` shows: **if** you already have an operator inequality \(K^{\circ M}\ge c_*\mathcal H_{t_*}\), then you get a Doeblin/minorization event for a block.
- `prop:sandwich` works with a **smoothed kernel** \(\widetilde K:=\mathsf S_\rho\circ K\circ\mathsf S_\rho\) and is currently labeled “external input”.

**Key obstacle (why this track is not yet closing UCIS-C).**
- Any pulse mechanism that is *not already present in the physical Wilson kernel* must be connected back to the original kernel by a **comparison theorem** (e.g. “gap of smoothed kernel ⇒ gap of original kernel” or “original kernel dominates a pulse kernel”). That comparison theorem is currently missing and is itself nontrivial.
- If the smoothing uses a compactly supported ball-average, it does not automatically remove β-dependence; at large β the unsmoothed kernel can remain extremely concentrated and smoothing may not yield uniform-in-β lower bounds without additional structure.

**When Track A would win.**
- If we can prove an inequality of the form
  \[
    K_{\rm int}^{(a)\,M}(U,\cdot)\ \ge\ c_*\,\mathcal H_{t_*}(U,\cdot)
  \]
  (or a direct \(P_{t_*}\) minorization) **for the actual Wilson kernel**, uniformly in \(\beta\), then UCIS-C becomes solvable.

### Track B — Physically scaled multi-step route (diffusive accumulation)

**Target shape.** Replace “one-step fixed-radius Doeblin” by a statement that after physical time \(T_{\rm phys}\) (i.e. \(M(a)=\lceil T_{\rm phys}/a\rceil\) ticks), the coarse increment has accumulated enough dispersion to yield a β-uniform smoothing component.

**What exists in `Yang-Mills.tex` today.**
- Scale-adapted refresh lemmas (`lem:single-link-refresh`, `lem:g-one-link-refresh`) naturally produce “small-step” mass at radius \(\asymp \beta^{-1/2}\), **uniformly in β** (for β large).

**Key obstacle (why Track B is inherently a scaling-window statement).**
- A step size \(\asymp \beta^{-1/2}\) typically needs \(\gtrsim \beta\) steps to achieve \(O(1)\) dispersion.
- With \(M(a)\sim 1/a\), this suggests a condition like \(M(a)\gg \beta\), i.e. \(\beta(a)\ll 1/a\), to get a schedule-compatible, physically fixed \(T_{\rm phys}\) smoothing theorem.
- Therefore, Track B most naturally yields a **scaling-window UCIS**: prove UCIS along an admissible schedule \(\beta=\beta(a)\) satisfying a growth condition that makes \(M(a)\) dominate the mixing time.

### Best track (recommendation)

- For a genuinely **unconditional** statement “uniform for all \(\beta\ge 0\) and all \(a\in(0,a_0]\)”, both tracks are extremely hard; the one-link no-go lemma shows why naïve fixed-radius Doeblin cannot work.
- For the most **implementable classical progress** with minimal new machinery, **Track B (physically scaled multi-step)** is the best next move, but it should be implemented explicitly as a **scaling-window theorem** (i.e. it will require an explicit hypothesis tying \(\beta\) to \(a\) so that \(M(a)\) is large enough).
- Track A can be kept as an optional route, but it likely requires adding a new comparison theorem connecting the smoothed/pulsed dynamics back to the original Wilson kernel before it can close UCIS-C.

---

### Track B — Concrete “scaling-window UCIS” statement (what we should implement next)

To operationalize Track B, define an explicit **admissible scaling window** hypothesis on \((a,\beta)\) that guarantees enough steps for diffusion to accumulate:

- **(SW)** There exists a constant \(C_{\rm SW}>0\) such that along the schedule \(\beta=\beta(a)\),
  \[
    \beta(a)\ \le\ C_{\rm SW}\,M(a)\ \asymp\ \frac{C_{\rm SW}\,T_{\rm phys}}{a}.
  \]

Then the target replacement theorem becomes:

> **UCIS\(_{\rm SW}\)**: Under (SW) (plus the existing near-identity window + scale-adapted refresh lemmas), there exist \(\theta_*,t_0>0\) depending only on \((G,\varepsilon,T_{\rm phys},C_{\rm SW})\) such that  
> \[
>   K_{\rm int}^{(a)\,M(a)}(U,\cdot)\ \ge\ \theta_*\,P_{t_0}(U,\cdot)
> \]
> holds along the schedule \(a\downarrow 0\).

**Repo implementation note (current).**
- The scaling-window theorem is now inserted into `Yang-Mills.tex` as `thm:ucis-sw`, with the window hypothesis labeled `eq:ucis-sw-window`.
- The Track B core analytic target is now a single labeled lemma `lem:scaled-ball-to-hk` (also in `Yang-Mills.tex`).

**What this reduces UCIS-C to proving (Track B core lemma).**

You need a quantitative random-walk/diffusion statement on compact Lie groups of the following flavor:

- If a one-step increment kernel has a scale-adapted small-ball component at radius \(r(\beta)\asymp \beta^{-1/2}\) with weight bounded below uniformly in \(\beta\), then after \(n\asymp \beta\) steps the \(n\)-fold increment law dominates a fixed heat kernel \(p_{t_0}\) with constants independent of \(\beta\).

In other words, Track B shifts the difficulty from “one-step fixed-radius measure minorization” to “multi-step diffusion/mixing at the correct time scale”, which is closer to known local CLT / spectral-gap technology for random walks on compact groups.

---

## Goal (what “DONE” means)

- **Goal**: Prove a **β-uniform, scaling-compatible minorization** for the *coarse* interface Markov kernel on a fixed physical slab, strong enough to feed the existing chain:
  - convex split ⇒ \(L^2\) contraction ⇒ odd-cone contraction ⇒ slab gap.
- **DONE**: A theorem (UCIS) with a referee-grade proof is written into `Yang-Mills.tex` (S3+), the dependency chain in `YANG_MILLS_PROOF_TRACK.md` is updated, and the previous blocker ledger items (notably #12–#13) are either closed or reduced to clearly smaller lemmas.

---

## Target Theorem (UCIS) — Exact Statement to Prove

### UCIS: Uniform Coarse Interface Smoothing

Fix:
- a compact gauge group \(G\) (e.g. \(G=\mathrm{SU}(N)\)),
- a **physical slab thickness** \(T_{\mathrm{phys}}>0\),
- a **coarse interface resolution** \(\varepsilon\in(0,\varepsilon_0]\) so the coarse interface state space is \(G^m\) with
  \[
    m=m(\varepsilon)\quad\text{independent of the lattice spacing }a,
  \]
- a maximal lattice spacing \(a_0>0\).

Let
\[
  M(a):=\left\lceil \frac{T_{\mathrm{phys}}}{a}\right\rceil,\qquad a\in(0,a_0].
\]

Let \(K_{\mathrm{int}}^{(a)}\) be the (coarse) interface Markov kernel on \(G^m\) induced by the Wilson lattice gauge specification on the slab (as in `Yang-Mills.tex`, “interface kernel” section). Let \(P_{t_0}(U,\cdot)\) denote the **product heat kernel** on \(G^m\) started at \(U\), at time \(t_0\).

**Claim (UCIS).** There exist constants \(\theta_*>0\) and \(t_0>0\) depending only on \((G,\varepsilon,T_{\mathrm{phys}})\) such that for **all**
- \(a\in(0,a_0]\),
- \(\beta\ge 0\),
- volumes/boundary conditions (finite tori / slabs, any exterior boundary data),

one has the kernel minorization
\[
  K_{\mathrm{int}}^{(a)\,M(a)}(U,\cdot)\ \ge\ \theta_*\,P_{t_0}(U,\cdot)
\]
as kernels on \(G^m\), uniformly in \(U\in G^m\).

### Why UCIS is the right closure theorem

- **It matches the missing ingredient**: a β-uniform (or β-window-compatible) Doeblin/HK component on a *fixed physical slab*.
- **It’s physically consistent**: fixed physical thickness means **\(M(a)\sim 1/a\)**, so the statement is stable under \(a\downarrow 0\).
- **It plugs directly into existing code**: it implies the convex split with a β-independent weight, which makes downstream contraction/gap bounds classical bookkeeping.

---

## Where UCIS plugs into the current Yang–Mills chain

UCIS is meant to discharge the role currently played (or claimed) by:

- `lem:beta-L-independent-minorization`
- `lem:coarse-refresh`, `lem:coarse-hk-domination`, `prop:coarse-doeblin`
- `prop:doeblin-full` / `prop:explicit-doeblin-constants`
- `cor:hk-convex-split-explicit` (already audited once a HK split exists)

**Operational intent**:
- Replace the “citation-heavy” / “β-explicit one-link” pieces with UCIS.
- Keep the already-audited contraction machinery unchanged once UCIS provides \((\theta_*,t_0)\).

---

## Proof Decomposition (what must be proved, in classical math)

UCIS should be proved by composing **three** core ingredients. If any ingredient fails, the failure point is explicit.

### Ingredient 1 — Cell selection / factorization (geometry + combinatorics)

**Lemma A (Coarse cell decomposition + disjoint support).**

- **Statement (target)**: Decompose the slab/interface into finitely many coarse cells (depending only on \(\varepsilon, T_{\mathrm{phys}}\)) and in each cell select a set of interior link variables such that:
  - **Disjoint support**: the selected interior variables for distinct cells are disjoint (or can be made so after gauge fixing / choice of spanning trees).
  - **Local influence**: each cell’s selected variables influence only that cell’s **coarse outgoing interface increment**.

- **Deliverable**: an explicit “cell skeleton” + a mapping from selected interior variables to coarse increments.

**Lemma B (Controlled Jacobian map on a good set).**

- **Statement (target)**: For each coarse cell, the map
  \[
    \Phi_{\mathrm{cell}}:\ (\text{selected interior links}) \to (\text{coarse increment in }G)
  \]
  is smooth and has Jacobian bounded below on a “good” set of configurations with positive Haar measure, with constants depending only on \((G,\varepsilon,T_{\mathrm{phys}})\) (not on \(a,\beta,L\)).

- **Key output**: a uniform pushforward lower bound of Haar mass onto a fixed-radius ball in \(G\), conditional on being in the good set.

**Notes**:
- This is the natural home for your existing ideas labeled like “cell-disjoint-links” / “plaquette-factorization” in the YM tracker.

---

### Ingredient 2 — Single-cell pushforward has a β-uniform ball-density (analysis on compact groups)

**Lemma C (Single-cell β-uniform small-ball minorization).**

> For every boundary condition and every \(\beta\ge 0\), the conditional law of the cell’s coarse increment has a density bounded below on a fixed-radius ball (in a fixed bi-invariant metric on \(G\)), with constants independent of \(\beta\).

Concretely, for each cell there exist \(r_*>0\) and \(p_*>0\) depending only on \((G,\varepsilon,T_{\mathrm{phys}})\) such that:
\[
  \mathbb P\big(\Delta_{\mathrm{cell}}\in B_{r_*}(\mathbf 1)\mid \text{boundary}\big)\ \ge\ p_*,
  \qquad\text{uniformly in }\beta\ge 0.
\]

**Why this is the analytic core**:
- It is **finite-dimensional** (no continuum limit yet).
- It isolates the obstruction: the Wilson weight can concentrate as \(\beta\to\infty\), and one must show this does not kill a uniform “refresh” event at coarse scale.

**Classical tools to attempt**:
- **Gauge fixing on a spanning tree** inside the cell (reduce to chord variables).
- **Heat-bath / matrix-Fisher style bounds** for one-link conditionals:
  \[
    d\mu(U)\ \propto\ \exp\big(\beta\,\mathrm{Re}\,\mathrm{Tr}(US)\big)\,dU.
  \]
- **Compactness + smoothness**: once you have a β-uniform lower bound on a ball for enough (approximately independent) increments, convolution yields smoothing.

---

### Ingredient 3 — Convolution ⇒ heat-kernel minorization (standard once 1–2 hold)

Assume each cell produces a small-ball component with weight \(p_*>0\), and cells factorize up to a chessboard constant \(c_{\mathrm{geo}}\in(0,1]\).

**Lemma D (Factorized small-ball ⇒ product small-ball).**

- **Statement (target)**: Across the \(m\) coarse interface sites, the joint law has a product small-ball component on \(G^m\) with weight comparable to \((c_{\mathrm{geo}}\,p_*)^{m}\).

**Lemma E (Ball-to-heat-kernel lower bound).**

- **Statement (target)**: For \(G^m\), there exist \(t_0>0\) and \(c_*(G,r_*)>0\) such that the \(M\)-fold convolution power of a measure with a ball-lower-bound dominates the heat kernel at time \(t_0\), i.e.
  \[
    \nu^{*M}\ \ge\ c_*\ P_{t_0}
  \]
  (Diaconis–Saloff-Coste / compact-group smoothing style).

---

## Assembly: how A–E imply UCIS

1. Use Lemmas A–B to express each cell’s coarse increment as a pushforward of selected interior link variables with controlled Jacobian on a good set.
2. Prove Lemma C: on the good set, the Wilson conditional law yields a β-uniform small-ball event for the coarse increment.
3. Use Lemma D: combine cells using chessboard/reflection factorization to obtain a product small-ball component on \(G^m\).
4. Use Lemma E to upgrade the product small-ball component to a **product heat-kernel** component after \(M(a)\) steps.
5. Conclude UCIS: \(K_{\mathrm{int}}^{(a)\,M(a)} \ge \theta_* P_{t_0}\) with \(\theta_*,t_0\) independent of \((a,\beta,L)\).

---

## Fallback theorem (staged target)

### UCIS(β ≥ β₀)

Same statement as UCIS, but only for \(\beta\ge \beta_0\) (some fixed threshold).

- **Use**: combine with the strong-coupling gap (small β) to give a “best-of-two” lattice gap statement.
- **Limit**: does **not** by itself solve the continuum scaling window issues, but can solidify the lattice-only part of the manuscript.

---

## Repo-facing checklist (operational)

### Step 0 — Decide which target we pursue

- [x] **Target choice (current)**: pursue **Track B / scaling-window** UCIS\(_{\rm SW}\) (`thm:ucis-sw`) as the implementable classical next step.
- [ ] **Stretch target**: UCIS (full β-uniform, all \(\beta\ge 0\), all \(a\in(0,a_0]\)) via a true cell-level pulse/sandwich comparison (Track A), or a new β-uniform refresh mechanism.
- [ ] **Fallback lattice-only target**: UCIS(\(\beta\ge\beta_0\)) staged target (useful for lattice gap bookkeeping, but not by itself a continuum closure).

### Step 1 — Add theorem skeletons to the manuscript

- [x] Add a new theorem statement in `Yang-Mills.tex` with a stable label, e.g. `thm:ucis`.
- [x] Add lemma stubs (A–E) with labels and clearly stated dependencies.
- [x] Add the scaling-window replacement theorem `thm:ucis-sw` plus its window label `eq:ucis-sw-window` and Track-B core lemma `lem:scaled-ball-to-hk`.
- [x] Update `YANG_MILLS_PROOF_TRACK.md`:
  - add UCIS to the “Main-chain claim map”
  - link UCIS as the replacement for ledger #12–#13 blockers
  - register `thm:ucis-sw` and the new core blocker `lem:scaled-ball-to-hk`

### Step 2 — Prove the geometry/combinatorics lemmas (A–B)

- [x] Lemma A (disjoint support) *(implemented as a reduction in `Yang-Mills.tex` via `lem:ucis-A-cell-decomp`)*
- [ ] Lemma B (controlled Jacobian) *(Track A–style ingredient; not currently needed for UCIS\(_{\rm SW}\) as implemented)*

### Step 3 — Prove the analytic single-cell lemma (C)

- [ ] Lemma C (β-uniform ball-density pushforward) *(unconditional UCIS route; blocked by the one-link no-go at fixed radius)*
- [x] Track B replacement: `lem:scaled-ball-to-hk` is now implemented in `Yang-Mills.tex` as a reduction.
- [x] Remaining Track B analytic input: `lem:ballwalk-diffusive` is now cited in `Yang-Mills.tex` (Hebisch–Saloff-Coste (1993), Thm 5.1) with hypotheses checked for the uniform ball walk on compact \(G\).

### Step 4 — Prove smoothing upgrade (D–E)

- [x] Lemma D (cell factorization ⇒ product ball) *(implemented as a reduction once the cell-level smoothing input is available)*
- [x] Lemma E (ball ⇒ heat kernel) *(implemented as a reduction to `lem:ball-conv-lower`)*

### Step 5 — Wire into the existing gap chain

- [x] Show UCIS ⇒ convex split with β-independent \(\theta_*\) and fixed \(t_0\). *(bookkeeping corollary inserted as `cor:ucis-L2-contraction`)*
- [x] Ensure it feeds the existing audited `cor:hk-convex-split-explicit` / odd-cone contraction chain unchanged.

---

## Acceptance criteria (non-negotiable)

- **Uniformities (UCIS)**: constants \(\theta_*, t_0\) depend only on \((G,\varepsilon,T_{\mathrm{phys}})\), not on \((a,\beta,L)\) or boundary conditions.
- **Uniformities (UCIS\(_{\rm SW}\))**: constants \(\theta_*, t_0\) depend only on \((G,\varepsilon,T_{\mathrm{phys}},C_{\rm SW})\), and the minorization holds along schedules satisfying `eq:ucis-sw-window`.
- **Correct scaling**: \(M(a)=\lceil T_{\mathrm{phys}}/a\rceil\) must be present; no “fixed power” statements that silently break as \(a\downarrow 0\).
- **Kernel form**: \(P_{t_0}(U,\cdot)\) must be the product heat kernel on \(G^m\) (or an explicitly equivalent smoothing reference).
- **No hidden assumptions**: no appeal to area law, confinement, or AF/Mosco as an “input” in the main line unless explicitly moved to a conditional appendix.

---

## Notes (what’s genuinely hard / where novelty lives)

- The novelty is almost entirely concentrated in **Lemma C** (β-uniform small-ball for the Wilson conditional on a coarse cell).  
  Everything else is geometry/factorization + standard compact-group smoothing once you have a uniform small-ball event.
- UCIS is a **local nonperturbative smoothing theorem** for the Wilson slab conditional law. If proved in the strength stated, it is a substantive new constructive-QFT tool.


