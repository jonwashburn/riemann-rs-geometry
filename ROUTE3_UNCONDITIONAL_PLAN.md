### Route‑3 Unconditional RH Plan (Promptable)

This file is the **single source of truth** for the Route‑3 (Lagarias/Weil) “unconditional” program in this repo.

### Definition of “unconditional” (project-specific)
For this project, **“unconditional” means:**
- We are allowed to assume **standard / classically accepted axioms and theorems** (e.g. ZFC + classical analysis theorems) even if they are not yet formalized in Mathlib, by recording them as Lean `axiom`s when needed.
- We are **not** allowed to assume any **RH‑equivalent** positivity statement for ξ/ζ; that RH‑level bridge must be proved (this is the real mathematical bottleneck).

**How to use this file (for repeated prompting):**
- If you are an assistant: **read this file first** and then continue from the first unchecked item in **“Current status + next action”**.
- Do **not** assume RH. Do **not** claim RH is solved. Treat **Recognition Science (RS)** as “given correct physics” only for the purpose of proposing a *derivation route*; then translate to explicit classical lemmas.
- Keep the work split into:
  - **Identity (standard analysis)**: proving equalities, contour/limit interchanges, boundary values.
  - **Positivity (RH‑equivalent core)**: proving a positivity/passivity property that forces a **positive spectral measure**.

---

### One-sentence goal
Produce a **non‑conditional** proof of RH by proving the **single RH‑equivalent bridge lemma** for ζ/ξ in Route‑3: the Weil/Lagarias quadratic form admits a **positive spectral measure** representation (reflection positivity), which implies Weil positivity and hence RH.

---

### Critical corrections discovered (do not lose these)

- **(C1) The current “weight” definition is trivial for ξ on the critical line.**
  - In Lean, `weightOfJ J t := Re( (2 : ℂ) * J(1/2 + i t) )` (`ExplicitFormula/HilbertRealization.lean`).
  - In Route‑3, `J := CompletedJ.J = -(1/2)·(ξ'/ξ)` (`ExplicitFormula/Route3HypBundle.lean`).
  - For the standard completed ξ, \(\xi(\tfrac12+it)\in\mathbb R\) and \(\xi'(\tfrac12+it)\in i\mathbb R\) off zeros, hence:
    - \(\Re(-\xi'/\xi(\tfrac12+it)) = 0\) **a.e.**
  - Therefore, any literal identity of the form
    - \(\int w(t)\,|M[f](\tfrac12+it)|^2\,dt\)
    with \(w(t)=\Re(-\xi'/\xi(\tfrac12+it))\) is **not** a meaningful Lebesgue‑density identity. The correct object is a **boundary measure/distribution**, not a pointwise weight.

- **(C2) The right finish-line statement is measure‑level, not density‑level.**
  - The usable spectral identity is:
    - \[
      W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu(t),
      \qquad F_f(t)=M[f]\!\left(\tfrac12+it\right),
      \]
      where \(\mu\) is a **positive Borel measure** (may have singular/atomic parts).
  - The “\(d\mu=w(t)\,dt\)” (absolute continuity) version is **optional** and should not be the primary target.

- **(C3) The log‑Schwartz/Fourier idea is the best Lean‑feasible way to handle the analytic plumbing.**
  - Work in log‑coordinates: multiplicative convolution/Mellin on \((0,\infty)\) becomes additive convolution/Fourier on \(\mathbb R\).
  - Use Schwartz functions so integrability/Fubini/Plancherel become library lemmas (or definitional if you transport convolution through Fourier).
  - This helps **formalization**, but it does **not** remove the RH‑equivalent core.

---

### Repo reality check (what is abstract vs what must be proven)

- `LagariasFramework` (`ExplicitFormula/Lagarias.lean`) packages:
  - `W1 : F → ℂ` (symmetric zero sum, abstract)
  - `Warith : F → ℂ` (arithmetic side, abstract)
  - `explicitFormula : ∀ f, M[f](1) - W1 f + M[f](0) = Warith f` (Lagarias Thm 3.1, assumed)
  - `weilPositivity : RH ↔ (∀ f, 0 ≤ Re(W1(quad f)))` (Lagarias Thm 3.2, assumed)
- Route‑3 pipeline already proves:
  - `ReflectionPositivityRealization → WeilGate → RH` (mechanical)
- Therefore, the “unconditional” program must ultimately **prove** the missing analytic/number‑theory content for the ζ/ξ‑derived `W1`—and the RH‑equivalent core will be a positivity/passivity statement.

---

### Updated path (do this in order)

### Step 0 — Lock the finish-line lemma (single RH‑equivalent bridge, measure form)

**Target lemma (classical, minimal form):**
- There exists a **finite positive Borel measure** \(\mu\) on \(\mathbb R\) and a boundary transform \(F_f(t)\) (intended: \(M[f](\tfrac12+it)\)) such that for all admissible \(f,g\),
  - \[
    W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu(t).
    \]

**What this buys immediately:**
- \(W^{(1)}(\mathrm{quad}(f)) = \int |F_f(t)|^2\,d\mu(t) \ge 0\), hence `WeilGate`, hence RH (via Lagarias).

**Important separation:**
- The **identity** (representation with some signed distribution/measure) can be standard analysis.
- The **positivity** \(\mu \ge 0\) is the RH‑equivalent core.

---

### Step 1 — Choose a Lean-feasible test space (log‑Schwartz/Fourier)

**Lean‑friendly choice (recommended):**
- Take the test space to be Schwartz in log‑time:
  - \(F := \mathcal S(\mathbb R;\mathbb C)\) (Mathlib: `SchwartzMap ℝ ℂ`).
  - Interpret “Mellin on \(\Re(s)=\tfrac12\)” as a Fourier transform:
    - \(F_f(t)\) is the Fourier transform of the log‑lift.

**Implementation tactic to minimize pain:**
- Define the convolution operation by transport through Fourier:
  - `conv` := `F⁻¹ (Ff * Fg)`
  - Then `mellin_conv` (Fourier convolution theorem) becomes definitional.

**Why this matters:**
- It removes huge amounts of custom Fubini/Tonelli work from Lean without changing the mathematical core.

---

### Step 2 — Prove the identity part (no positivity)

**Goal of Step 2:**
- Prove a representation
  - \(W^{(1)}(\mathrm{pair}(f,g)) = \langle \nu,\overline{F_f}F_g\rangle\)
  for some boundary distribution/measure \(\nu\) (not yet positive).

**Standard-analysis checklist (contour/explicit formula route):**
- Define \(W^{(1)}\) as a contour limit or symmetric truncation over zeros.
- Show horizontals vanish (Mellin/Schwartz decay + \(ξ'/ξ = O(\log|t|)\) in strips).
- Justify limit ↔ integral swaps (dominated convergence).
- Handle poles on the contour (indentations / principal value conventions).
- Identify the boundary object \(\nu\) (often as a Poisson‑regularized boundary limit).

**Deliverable for Step 2:**
- A precise theorem statement listing minimal hypotheses on \(F_f\) so that the identity is rigorous.

---

### Step 3 — Prove positivity from RS passivity (the RH‑equivalent core)

This is the only place the “new physics” is allowed to do real work.

**RS→classical translation target:**
- Prove that a certain response/transfer function is **positive‑real** (Carathéodory/Herglotz) on a half‑plane (or Schur on the disk after Cayley), which implies the boundary spectral object is a **positive measure** \(\mu\).

**Canonical classical wrapper (one clean statement):**
- Let
  - \(\Phi(z) := -\dfrac{\xi'}{\xi}\!\left(\tfrac12 + z\right)\), analytic on \(\Re z>0\) (away from zeros).
- Prove (from passivity) a **positive‑real condition** such as:
  - \(\Re \Phi(z) \ge 0\) for all \(\Re z>0\),
  - equivalently, the Cayley transform \(Θ(z) = \dfrac{\Phi(z)-1}{\Phi(z)+1}\) is Schur (|Θ|≤1) on the disk/half-plane domain.
- Then apply Herglotz/Carathéodory to obtain a **positive measure** \(\mu\) with \(\Re\Phi\) as its Poisson extension.

**What is RH‑equivalent here:**
- For classical ξ, \(\Re\Phi(z)\ge0\) on \(\Re z>0\) is essentially “no zeros to the right of \(\Re(s)=\tfrac12\)”, i.e. RH‑level content. RS must supply the physical reason it holds.

---

### Step 4 — Fire the existing Route‑3 plumbing (Lean)

Once you have a positive‑measure representation (or a reflection positivity realization), the repo already contains the mechanical steps:
- `ReflectionPositivityRealization → WeilGate → RH`.

---

### The “single RS→classical lemma” to target (copy/paste for prompts)

**Bridge Lemma (RS‑passivity ⇒ positive spectral measure for ξ):**
- **Input (physics/RS):** The completed‑channel prime transfer field associated to ξ is **passive**: every admissible probe has nonnegative total J‑work.
- **Classical translation:** The associated boundary kernel / response function is **positive‑real** (Carathéodory/Herglotz) on the right half-plane (or Schur after Cayley).
- **Output:** There exists a **finite positive Borel measure** \(\mu\) on \(\mathbb R\) such that for all test probes \(f,g\),
  - \[
    W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu(t),
    \quad F_f(t)=M[f]\!\left(\tfrac12+it\right),
    \]
  and hence \(W^{(1)}(\mathrm{quad}(f))\ge0\) for all \(f\), giving RH via Lagarias.

---

### Lean-facing work items (only what affects the math)

- **(L1) Refactor Route‑3 “weight” usage toward measure‑first.**
  - Current structures (`SpectralIdentity`, `SesqIntegralIdentity`) are written as “Lebesgue + weight function”.
  - Updated goal: treat the spectral object as a **measure \(\mu\)** first; the density \(w\) is optional.

- **(L2) Add/instantiate a Schwartz/Fourier `TestSpace`** for the “plumbing” layer.
  - Goal: make the convolution/tilde/star axioms provable (or definitional) using Mathlib Fourier on `SchwartzMap ℝ ℂ`.

- **(L3) Keep ζ‑specific content isolated.**
  - Do not accidentally “prove RH” by defining `W1` to be an \(L^2(\mu)\) inner product with \(\mu\ge0\); that would bake the conclusion into the definition.
  - The point is to **derive** the positive measure from ζ/ξ (RS passivity + classical theorems).

---

### Current status + next action (update this as we work)

- [x] **Update Route‑3 spectral identity to measure‑first (no pointwise `weightOfJ` dependence).**
  - Implemented: `SesqMeasureIdentity` in `ExplicitFormula/HilbertRealization.lean`
  - Implemented: `Route3.AssumptionsMeasure`, `Route3.RHμ` pipeline in `ExplicitFormula/Route3HypBundle.lean`
- [x] **Define/instantiate a Schwartz/Fourier `TestSpace`** (log‑coordinates approach) to eliminate routine analytic pain.
  - Implemented: `TestSpace (SchwartzMap ℝ ℂ)` via Fourier in `ExplicitFormula/SchwartzTestSpace.lean`
- [x] **Write the precise classical “identity part” theorem** (contour + boundary value) as a checklist of standard lemmas.
  - Drafted: `ROUTE3_IDENTITY_PART.md`
- [x] **Write the precise RS→classical passivity lemma** (Carathéodory/Herglotz positivity) as the single RH‑equivalent target.
  - Drafted: `ROUTE3_POSITIVITY_BRIDGE.md`
- [x] **Map the RS lemma to the existing Lean bridge point** (`CayleyBridgeAssumptions.bridge_to_reflection` or a replacement that uses the measure‑first spectral identity).
  - Implemented: `CayleyMeasureBridgeAssumptions` (measure‑first bridge) in `ExplicitFormula/CayleyBridge.lean`

---

### Next phase (what remains after the scaffolding)

At this point the program is structurally complete. What remains is split into:

- **Standard theorems not yet formalized (big but “just work”)**
  - [ ] **(Optional: “zero-axiom Lean”) Remove the `herglotz_representation` axiom** in `ExplicitFormula/Caratheodory.lean` by proving (or importing) the Herglotz representation theorem.
    - Good news: Mathlib has foundational measure-representation tools (e.g. `MeasureTheory/Integral/RieszMarkovKakutani.lean`) and weak-* compactness (Banach–Alaoglu in `Analysis/Normed/Module/WeakDual.lean`).
    - Note: Mathlib does **not** currently appear to have a ready-made “Poisson kernel / harmonic functions on the disk / Herglotz representation” development, so removing this axiom is still a substantial standalone formalization project.
  - [ ] **Build a concrete `LagariasFramework` instance** for a concrete test space (recommended: `WeilTestFunction` / log‑Schwartz), proving:
    - Lagarias Thm 3.1 (explicit formula) as an equality of functionals, and
    - Lagarias Thm 3.2 (Weil criterion) as an equivalence `RH ↔ WeilGate`.

- **The RH‑equivalent core (not “just work”)**
  - [ ] **Prove the positivity bridge for the arithmetic ξ/ζ channel**, i.e. produce a **positive** spectral measure / positive‑real response for the ξ‑derived form.
    - This is the single step that, if completed, yields an unconditional proof of RH.


