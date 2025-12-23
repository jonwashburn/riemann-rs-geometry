## UCIS (Uniform Coarse Interface Smoothing) — Operational Plan

**Date**: 2025-12-23  
**Purpose**: Define a single, sharply targetable *classical* theorem that would close the key lattice-side blocker in `Yang-Mills.tex`, together with an executable decomposition into sublemmas and a repo-facing checklist.

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

- [ ] **Target choice**: UCIS (full β-uniform) vs UCIS(β≥β₀) (staged).

### Step 1 — Add theorem skeletons to the manuscript

- [ ] Add a new theorem statement in `Yang-Mills.tex` with a stable label, e.g. `thm:ucis`.
- [ ] Add lemma stubs (A–E) with labels and clearly stated dependencies.
- [ ] Update `YANG_MILLS_PROOF_TRACK.md`:
  - add UCIS to the “Main-chain claim map”
  - link UCIS as the replacement for ledger #12–#13 blockers

### Step 2 — Prove the geometry/combinatorics lemmas (A–B)

- [ ] Lemma A (disjoint support)
- [ ] Lemma B (controlled Jacobian)

### Step 3 — Prove the analytic single-cell lemma (C)

- [ ] Lemma C (β-uniform ball-density pushforward)

### Step 4 — Prove smoothing upgrade (D–E)

- [ ] Lemma D (cell factorization ⇒ product ball)
- [ ] Lemma E (ball ⇒ heat kernel)

### Step 5 — Wire into the existing gap chain

- [ ] Show UCIS ⇒ convex split with β-independent \(\theta_*\) and fixed \(t_0\).
- [ ] Ensure it feeds the existing audited `cor:hk-convex-split-explicit` / odd-cone contraction chain unchanged.

---

## Acceptance criteria (non-negotiable)

- **Uniformities**: constants \(\theta_*, t_0\) depend only on \((G,\varepsilon,T_{\mathrm{phys}})\), not on \((a,\beta,L)\) or boundary conditions.
- **Correct scaling**: \(M(a)=\lceil T_{\mathrm{phys}}/a\rceil\) must be present; no “fixed power” statements that silently break as \(a\downarrow 0\).
- **Kernel form**: \(P_{t_0}(U,\cdot)\) must be the product heat kernel on \(G^m\) (or an explicitly equivalent smoothing reference).
- **No hidden assumptions**: no appeal to area law, confinement, or AF/Mosco as an “input” in the main line unless explicitly moved to a conditional appendix.

---

## Notes (what’s genuinely hard / where novelty lives)

- The novelty is almost entirely concentrated in **Lemma C** (β-uniform small-ball for the Wilson conditional on a coarse cell).  
  Everything else is geometry/factorization + standard compact-group smoothing once you have a uniform small-ball event.
- UCIS is a **local nonperturbative smoothing theorem** for the Wilson slab conditional law. If proved in the strength stated, it is a substantive new constructive-QFT tool.


