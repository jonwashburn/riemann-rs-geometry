## U1 (UEI / Tightness on Fixed Regions) — Operational Plan

**Date**: 2025-12-24  
**Purpose**: Define the next *single, sharply targetable classical theorem* needed to move the Yang–Mills manuscript from “lattice gap + conditional continuum packaging” toward an **unconditional continuum construction** on fixed regions. This plan is the analogue of `UCIS_OPERATIONAL_PLAN.md`, but for the **U1** bottleneck: UEI/tightness (and the local LSI/concentration machinery it requires).

---

## Current status (in this repo)

- **Where U1 lives in the manuscript**: `Yang-Mills.tex`, U0/U1 section and the appendix block “Tree–Gauge UEI”.
- **What is now explicit (good)**:
  - The fixed-region UEI statement `thm:uei-fixed-region` has been made explicitly **scaling-window** and is now **conditional** on a named RG-grade mean bound `assump:uei-mean` (no longer hidden as an “and one expects…” sentence).
  - The proof tracker ledger item for U1 (`YANG_MILLS_PROOF_TRACK.md`, ledger #18) has been updated to reflect this conditionalization.
- **What remains genuinely open (core blocker)**:
  - A rigorous, dimension/stencil-uniform mechanism forcing a **small-field regime on fixed physical regions** along the weak-coupling schedule \(\beta=\beta(a)\), strong enough to yield:
    - uniform control of \(\mathbb E[S_R]\) (discharging `assump:uei-mean`),
    - the gradient/Lipschitz estimates used in Herbst,
    - and a usable LSI/concentration inequality for the tree-gauge chord Gibbs measure that does not silently degrade with \(m(R,a)\asymp a^{-4}\).

---

## Goal (“DONE”)

- **Goal**: Replace `assump:uei-mean` by a proved theorem and make the U1 package (UEI/tightness on fixed regions) referee-grade, with constants and uniformities stated correctly along the scaling schedule.
- **DONE means**:
  - `Yang-Mills.tex` contains a theorem that implies tightness on each fixed region \(R\Subset\mathbb R^4\) along van Hove scaling sequences,
  - the downstream limit-closure steps (OS0/OS2 closure, OS1 route(s), and NRC uniqueness) can cite this theorem without hidden RG leaps,
  - `YANG_MILLS_PROOF_TRACK.md` ledger #18 is either closed or reduced to a smaller explicitly named lemma.

---

## Target theorem (U1 closure target) — exact shape

Fix a bounded physical region \(R\Subset\mathbb R^4\). Let
\[
S_R(U)\ :=\ \sum_{p\subset R}\phi(U_p),\qquad \phi(U)=1-\tfrac1N\Re\Tr(U)\in[0,2],
\]
and let \(\mu_{a,L}\) be the Wilson lattice measures along a weak-coupling schedule \(\beta=\beta(a)\) and a van Hove volume choice \(L=L(a)\).

> **U1–UEI (fixed-region UEI/tightness; closure target).**  
> Along the scaling window, there exist constants \(\eta_R>0\) and \(C_R<\infty\) depending only on \((R,N)\) (and the declared schedule parameters) such that for all sufficiently small \(a\) and all admissible \(L\),
> \[
>   \mathbb E_{\mu_{a,L}}\big[e^{\eta_R S_R}\big]\ \le\ C_R,
> \]
> uniformly over boundary configurations outside \(R\). Consequently, cylinder laws on \(R\) are tight and OS0/OS2 pass to subsequential limits.

This is the precise missing “tightness engine” in the continuum spine.

---

## Proof decomposition (failure points you can actually audit)

### U1-A — Tree gauge reduction + bounded interaction degree (STD)

- **Deliverable**: After tree gauge on \(R\), represent the interior law as a Gibbs measure on chord variables \(X\in G^{m(R,a)}\) with interaction graph degree bounded by a constant \(d_0(R)\) independent of \(a\).
- **Status**: standard, but must be written with correct scaling \(m(R,a)\asymp a^{-4}\) and explicit boundary-condition dependence.

### U1-B — Small-field concentration on fixed regions (RG-grade core)

- **Target**: a theorem that forces, with high probability along the schedule, that all plaquettes in \(R\) lie within an \(O(a^2)\) neighborhood of \(\mathbf 1\) (in a fixed bi-invariant metric). Any quantitative version that implies \(S_R=O(1)\) in expectation suffices.
- **Why it’s core**: without small-field control, neither the mean bound nor the Lipschitz/gradient bounds used in Herbst can be uniform in \(a\) on a fixed physical region.

### U1-C — Mean bound for \(S_R\) (discharge `assump:uei-mean`)

- **Target**: prove \(\sup_{a}\mathbb E[S_R]\le M_R<\infty\) along the schedule (uniform in \(L\) and boundary outside \(R\)).
- **Reduction**: U1-B ⇒ U1-C via the trivial bound \(0\le \phi\le 2\) and the small-field scaling \(\phi(U_p)\lesssim a^4\) on the good event.

### U1-D — Gradient/Lipschitz controls for Herbst (STD once U1-B exists)

- **Target**: show the observables needed downstream (in particular \(S_R\) and the staple/loop maps used in equicontinuity) have Lipschitz constants compatible with the LSI constant so that the Herbst exponent is \(O(1)\) uniformly in \(a\).
- **Note**: any claim like \(\|\nabla S_R\|^2\lesssim a^4\) must be explicitly derived from U1-B (it is not true without small-field).

### U1-E — A usable LSI / concentration inequality for the chord Gibbs law (RG-grade)

- **Target**: an LSI (or a substitute concentration inequality) on the chord Gibbs measure that remains usable as \(m(R,a)\to\infty\), i.e. does not silently degrade with \(a^{-4}\).
- **Typical strategies** (each requires real work):
  - **Uniform convexity on a dominant good set** + a robust “local-to-global” transfer (Wang-type) with constants tracked,
  - **Dynamic approach**: a log-Sobolev inequality for a heat-bath / Langevin dynamics on the finite region with constants controlled by a spectral gap + local curvature,
  - **Smoothing/comparison approach**: compare to a positive-time heat-smoothed reference with known LSI, then control the Radon–Nikodym distortion (requires a new comparison theorem).

### U1-F — Close the tightness/OS0 step and remove conditional language

- Once U1-C and U1-E are proved with explicit constants, `thm:uei-fixed-region` becomes unconditional (no `assump:uei-mean`), and `prop:os0os2-closure` is genuinely closed.

---

## RS-guided “creative bypass” for U1-B: J-cost / heat-kernel smoothing route (Track J)

RS (T5) singles out a unique convex cost
\[
  J(x)=\tfrac12(x+1/x)-1,
\]
and RS (T6/T7) treats smoothing/regularization as structural rather than parameter-driven. A classical correspondence that **may bypass** the hardest “prove small-field for the raw Wilson measure” step is:

- **Replace “small-field of the unsmoothed Wilson law” by “dimension-free regularity of a J-cost–regularized (heat-smoothed) law”**, then prove that this regularization does not change the continuum limit (universality).

Concretely:

### U1-J1 — Dimension-free LSI after positive-time group heat smoothing (analysis on compact groups)

Define a heat-smoothed measure on link configurations by pushing the Wilson law forward under independent left-multiplication by a heat increment of time \(t>0\) on each link (equivalently: convolve the lattice law with the product heat kernel on \(G^{E(R,a)}\)).

Target: show the smoothed law satisfies an LSI (and hence Herbst subgaussian bounds) with a constant depending only on \((G,t)\), **independent of**:
- the original interaction (Wilson plaquette potential),
- \(\beta\),
- and the dimension \(|E(R,a)|\) (tensorization).

This is the key “dimension-free functional inequality” lever: it would give U1-E without any small-field theorem for the raw Wilson law.

### U1-J2 — Universality/commutation: smoothing does not change the continuum limit

Target: prove that for each fixed bounded region \(R\), applying the heat-smoothing (or the equivalent “J-cost regularization” operator on observables) at a scale \(t=t(a)\downarrow 0\) does **not** change the limiting Schwinger functions as \(a\downarrow 0\).

In other words, show that “take the continuum limit” and “apply the smoothing calibrator” commute on the cylinder algebra, so one may:
\[
  \lim_{a\downarrow 0}\ \mu_{a,L}(F)\ =\ \lim_{t\downarrow 0}\ \lim_{a\downarrow 0}\ \mu^{(t)}_{a,L}(F)
\]
for the relevant local observables \(F\) (loops + renormalized local fields).

### U1-J3 — Use the smoothed LSI/Herbst bounds to get tightness

Once U1-J1 and U1-J2 are in place, tightness/OS0 closure can be proved using uniform subgaussian bounds under the smoothed measures, plus the \(t\downarrow 0\) commutation to transfer bounds back to the intended continuum theory.

**Net effect:** U1-B (raw small-field) and U1-C (raw mean bound) are replaced by a single “universality under smoothing” theorem plus a dimension-free LSI statement for the smoothed law. This is a genuine “zoom-out” reparameterization of the bottleneck consistent with the RS bridge document’s J-cost regularization idea.

---

## Quick reality check: attack both routes, compare difficulty

### Route 1 — Raw small-field (U1-B → U1-C/U1-D/U1-E)

- **What you must really prove**: a high-probability small-field regime on a fixed physical region with \(|\mathcal P_R|\asymp a^{-4}\) plaquettes, strong enough to control \(\mathbb E S_R\) and the Lipschitz constants used in Herbst.
- **Why it looks hard**: existing “finite stencil” estimates in the manuscript (e.g. `TS:ball_weight`) typically give only polynomial tails like \(O(a^2)\) for a *fixed* stencil, which is far too weak to control an extensive sum over \(a^{-4}\) plaquettes. Closing this route appears to require a genuine RG-grade mechanism (constructive control of weak coupling).

### Route 2 — Track J (U1-J1 + U1-J2)

- **What you must prove**:
  - **U1-J1**: dimension-free LSI/Herbst for the heat-smoothed local laws (this is close to standard entropy-chain/tensorization once single-site heat-kernel LSI is cited).
  - **U1-J2**: smoothing-limit commutation/universality on cylinder observables (often a uniform sup-norm approximation argument on compact groups).
- **Why it looks more promising**: U1-J2 is essentially measure-independent for bounded continuous cylinder observables, and U1-J1 can be reduced to classical compact-group functional inequalities plus an entropy chain rule. The remaining “hard theorem” becomes a universality statement for passing \(t\downarrow 0\) after \(a\downarrow 0\) for the specific unbounded field observables (if needed), rather than proving raw small-field concentration for the full Wilson law.

---

## Repo integration checklist (operational)

- [ ] Add a named theorem block in `Yang-Mills.tex` that replaces `assump:uei-mean` (or proves it under explicit hypotheses).
- [ ] Refactor `thm:uei-fixed-region` so the centered Herbst bound and the mean-removal step are clearly separated.
- [ ] Update `YANG_MILLS_PROOF_TRACK.md`:
  - register the new U1 closure theorem and its sublemmas,
  - mark which parts are STD vs RG-grade,
  - close or refine ledger #18 accordingly.

---

## Acceptance criteria (non-negotiable)

- **Correct scaling**: all statements must be consistent with \(m(R,a)\asymp a^{-4}\) and \(|\mathcal P_R|\asymp a^{-4}\) for fixed physical \(R\).
- **Uniformities**: the final UEI/tightness constants must be uniform in \(L\) and in exterior boundary configurations, and must specify exactly what dependence on the scaling schedule is assumed.
- **No hidden “small-field”**: any small-field regime must be either proved or isolated as a named assumption/theorem (no hand-waving inside proofs).


