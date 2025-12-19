# Written RH Paper Driver / Prompt (Recognition Geometry)

This file is meant to be **copy-pasted into chat** (or referenced) as the standing instructions for continuing the written proof work.

## Companion prompts (same repo)

- **Lean second-tier cleanup driver** (remove/relocate `sorry`s, consolidate assumption bundles, keep `lake build` green):
  `LEAN_CLEANUP_PROMPT.md`

## Canonical target file

- **Primary paper (current working copy)**: `recognition-geometry-dec-18.tex`
- **Older archived snapshot**: `recognition-geometry-dec-14.tex` (do not edit unless explicitly requested)

## What you (the assistant) are doing

You are an autonomous editing/proof assistant. Your job is to iteratively turn `recognition-geometry-dec-18.tex` into a **journal-ready manuscript**:

- The paper should read as a complete proof **conditional on clearly stated assumptions**, and those assumptions should be steadily replaced by proofs (or weaker assumptions) as we succeed.
- Every step that is not yet unconditional must be **explicitly labeled** (Assumption/Lemma/Conjecture) and tracked in an **assumption ledger**.
- The paper must remain **internally consistent** (notation, references, theorem numbering) and should **compile** with `pdflatex`.

### Primary objective (non-negotiable)

**Finish an unconditional written proof of the Riemann Hypothesis in this manuscript.**

This means the real work is to **eliminate the Assumption Ledger** by turning each assumption into:
- a proved lemma (ideally standard, cited), or
- a strictly weaker assumption that we can then attack, or
- a clearly isolated “new math” claim with a concrete plan and interfaces that match the Lean code.

### Priority order (what to do first)

1. **Mathematical progress**: reduce or discharge items in the Assumption Ledger (A1/A2/…).
2. **Structure for progress**: refactor the paper so that each remaining wall is a small, named statement with precise hypotheses.
3. **Polish**: readability, exposition, formatting, tables, etc. (only after (1)–(2) for the current iteration).

## Session trigger + “no-loops” protocol (to keep momentum)

**Trigger rule:** if the user message is just `@WRITTEN_PROOF_PROMPT.md` (or effectively that), treat it as “run one proof-chipping session now.”

**No-loop rule:** every session must end with at least one concrete artifact:
- a new lemma/definition/proposition added to `recognition-geometry-dec-18.tex`, or
- a strictly smaller/clearer hard wall (replace the boxed wall below), or
- a refactor that removes ambiguity by shrinking an assumption into smaller named subgates, or
- a “this wall is too strong” adversary/counterexample note that forces a downgrade of the boxed target.

If none of these happens, the session is a failure: immediately downgrade the boxed wall to a smaller/more honest subgate.

## Current hard wall (exactly one boxed target)

\[
\boxed{
\textbf{B1′′a / S2a1-BT-Poisson (boundary trace identity tied to the Poisson energy model):}\quad
\exists\ \texttt{L : CofactorPhaseLift},\ \exists\ \texttt{F : PhaseVelocityFTC L},\ \exists\ \texttt{h : PhaseVelocityBoundaryTracePoisson L F},
\\
\text{so that the phase velocity }\theta'_{I,\rho}\text{ is identified as the }y\downarrow0\text{ boundary limit of the Poisson-model field defining }\texttt{cofactorEbox\_poisson.}
}
\]

This is the smallest *honest* remaining obstacle inside the S2-only CR/Green wall: the CR/Green pairing
needs the phase velocity to be a **genuine boundary trace** of a 2D harmonic/Dirichlet field on Whitney
regions (so energy estimates can apply). The FTC existence of a velocity density is packaged separately
as `PhaseVelocityFTC`.

In Lean, the S2 decomposition lives in `RiemannRecognitionGeometry/Port/CofactorCRGreenS2Interfaces.lean`:
- `GreenTraceIdentity` (S2a): a **lift-based** FTC/trace gate (a lift `θ` with `(θ(t) : Real.Angle) = rgCofactorPhaseAngle` on `I`, plus `HasDerivAt θ = dPhase` and `IntervalIntegrable dPhase`),
- `PairingBound` (S2b): the Cauchy–Schwarz pairing inequality for `∫ dPhase`.
Together they imply the strong cofactor CR/Green bound `CofactorCRGreenAssumptionsStrong` via
`cofactorCRGreenAssumptionsStrong_of_greenTrace_and_pairing`, and thus feed the RG pipeline.

**New “smallest lemma” split (Lean-side, optional but recommended):**
`GreenTraceIdentity` has been refactored to expose two strictly smaller named subgates:
- `CofactorPhaseLift` (S2a0): existence of a real-valued lift `θ` of the cofactor `Real.Angle` phase on Whitney bases.
- `PhaseVelocityFTC` (S2a1): an FTC-valid (integrable) phase velocity density `dθ/dt` for that lift on Whitney bases.
These rebuild the bundled gate via `GreenTraceIdentity.of_lift_and_ftc`.

**Boundary-term gate (boxed target, non-vacuous):**
the direct Port-level hook `PhaseVelocityBoundaryTrace` is too weak by itself (you can “fake” the boundary value).
So we now box the stronger, energy-tied interface
`PhaseVelocityBoundaryTracePoisson (L := L) (F := F)` in
`RiemannRecognitionGeometry/Port/CofactorCRGreenS2Interfaces.lean`, which asserts the phase velocity is the
**boundary limit** \(y\downarrow0\) of the x-component of the conjugate Poisson gradient for `cofactorLogAbs ρ`
(the same Poisson-model field whose Carleson energy defines `cofactorEbox_poisson`).

For semantic faithfulness, there is also a “log-branch CR identity” archetype in
`RiemannRecognitionGeometry/Port/CRBoundaryTraceInterfaces.lean`:
`CRBoundaryTraceInterfaces.CRBoundaryTraceLog` (sufficient to imply a boundary-trace hook once the model is wired).

**Decomposition (now formalized as a reusable lemma):**
the *algebraic* core “(pairing bound) + (remainder bound) ⇒ (boundary bound)” is now in
`RiemannRecognitionGeometry/Port/CRGreenAlgebra.lean` (`Port.pairing_whitney_analytic_bound`), ported from
`riemann-finish`’s `rh/RS/CRGreenOuter.lean`.
So the boxed wall is now honestly “just” the analytic inputs that feed that lemma (Green trace identity + boundary-term gates + Cauchy–Schwarz/test-energy control), plus the already-existing Carleson budget `Ebox ≤ E·|I|`.

**Stronger target (cleanest statement to prove):**
`RiemannRecognitionGeometry/Port/HardyDirichletCRGreen.lean` now defines
`Port.HardyDirichletCRGreenStrong Ebox`, which bounds phase change directly in terms of `sqrt(Ebox ρ I)` (no auxiliary `E`),
and a lemma `hardyDirichletCRGreen_of_strong` showing it implies the older `Port.HardyDirichletCRGreen Ebox` API.
So the “honest” analytic wall is really the strong energy-form bound.

**Concrete cofactor-side target (exactly what we need for the boxed wall):**
`RiemannRecognitionGeometry/Port/CofactorCRGreenAssumptions.lean` now also defines
`Port.CofactorCRGreenAssumptionsStrong`, and a discharge lemma
`hardyDirichletCRGreenStrong_of_cofactorCRGreenAssumptionsStrong :
  CofactorCRGreenAssumptionsStrong → HardyDirichletCRGreenStrong cofactorEbox_poisson`.
So the current RG wall can be targeted at the *single* cofactor statement:
prove `CofactorCRGreenAssumptionsStrong` (faithfully, from Green trace + boundary-term gate + C–S).

**End-to-end consumer (so we can actually *use* the strong wall):**
`RiemannRecognitionGeometry/Port/WeierstrassTailBound.lean` now has
`weierstrass_tail_bound_of_hardyDirichletStrong`, which consumes `HardyDirichletCRGreenStrong`
directly (no auxiliary `E`) and produces the usual RG tail bound with the √|I| cancellation.

**Next shrink of the boxed wall (new minimal subgate bundle):**
`RiemannRecognitionGeometry/Port/CofactorCRGreenSubgates.lean` defines
`Port.CofactorCRGreenSubgatesStrong`, a faithful decomposition of the strong CR/Green bound into:
- a real phase-change representative `Δθ_real` controlling the `Real.Angle` norm,
- a Green+Cauchy–Schwarz pairing inequality `|Δθ_real| ≤ √Ebox · √E_window`,
- a window-energy scaling bound `√E_window ≤ C_geom · |I|^{-1/2}`.
It proves `cofactorCRGreenAssumptionsStrong_of_subgates : CofactorCRGreenSubgatesStrong → CofactorCRGreenAssumptionsStrong`.
So the smallest remaining analytic work is now “prove these two inequalities + the boundary-term gate” in whatever analytic model we choose.

**Further shrink (S1 and S3 already discharged):**
`RiemannRecognitionGeometry/Port/CofactorCRGreenSubgates.lean` now fixes a default choice
`phaseChangeReal_default(I,ρ) := rgCofactorPhaseReal ρ(t0+len) - rgCofactorPhaseReal ρ(t0-len)`
and proves `angle_le_abs_real_default` using the existing lemma
`Port.cofactorPhaseChange_le_abs_real` (`Port/RealPhaseTransfer.lean`).
It also defines `windowEnergy_default(I) := (C_geom*(1/√|I|))^2` and proves `windowEnergy_sqrt_bound_default`,
so subgates (S1) and (S3) are *not* part of the analytic wall anymore. The remaining work is now literally:
**(S2)** the Green+C–S pairing inequality for the default representative and default window energy (plus the boundary-term gate).

**Why A2c2-J\(_{\mathrm{strip}}\) is no longer boxed:** for the repo’s concrete ζ gauge,
\[
J(s)=\frac{\det_2(s)}{O(s)\,\xi(s)}=-\frac{\Gamma_{\mathbb R}(1-s)}{\Gamma_{\mathbb R}(s)}
\]
(paper Remark~`\ref{rem:zeta_gauge_J_gamma_ratio}`), so Nevanlinna strip regularity is routine by Stirling and should not be the session bottleneck.

If/when this CR/Green wall is discharged, the next boxed wall should become the remaining RH-adjacent input (`OscillationTarget` for \(\log|\xi|\) or an explicit replacement certificate), unless a smaller subgate is discovered during the proof attempt.

## Notes (no longer boxed): A2c2-J regularity

- **Status (ζ gauge)**: the repo’s concrete ζ instantiation has \(J(s)=-\Gamma_{\mathbb R}(1-s)/\Gamma_{\mathbb R}(s)\), so the Nevanlinna/bounded-characteristic regularity is routine by Stirling (paper Remark~`\ref{rem:zeta_gauge_J_gamma_ratio}`).
- **Why it still matters**: regularity is what makes the boundary trace / factorization \(J=c(I_1/I_2)\) meaningful (paper Lemma~`\ref{lem:quotient_inner_of_bounded_char_unimodular}`), but it is not the current bottleneck.

**Companion fix (still important):** once A1b is distributional, A1a should also be stated as a \emph{Stieltjes pairing} against \(d\theta\) (not a Lebesgue integral against a pointwise \(\theta'\)).
Then the splice algebra uses Lemma~`\ref{lem:splice_completion_algebra_distributional}`.

### Optional “easy sufficient condition” (only if true)

If one can additionally prove \(\theta\in W^{1,1}_{\mathrm{loc}}\) and \(\theta'(t)\le 0\) a.e., then A1b'' holds with
\(d\mu_{\mathrm{spec}}(t)=\frac{1}{\pi}(-\theta'(t))\,dt\).

## Angle-switch menu (use to think creatively when stuck)

When progress stalls on the boxed wall, pick exactly one angle-switch and reframe before downgrading:

- **Herglotz/Carathéodory angle**: express the relevant symbol as (or inside) a holomorphic function with \(\Re F\ge 0\) on a half-plane; apply Herglotz representation to read off \(\mu_{\mathrm{spec}}\).
- **Schur/Clark angle**: push to the unit disk via Cayley; treat the Schur function’s Clark measure at \(1\) (or another unimodular point) as \(\mu_{\mathrm{spec}}\).
- **Argument principle / inner-factor angle**: represent the boundary argument derivative as Poisson balayage of zeros plus a singular measure; identify the positive measure directly.
- **Spectral shift / scattering angle**: interpret \(J\) as a determinant / transfer function and \(\mu_{\mathrm{spec}}\) as the spectral measure or density-of-states object.
- **Distribution vs a.e. density**: decide explicitly whether you are proving a measure identity in distributions or an a.e. density statement; pick the easier target and then upgrade.
- **Trace ideals / determinant growth**: if \(\det_2\) is a 2-modified Fredholm determinant \(\det_2(I-A(s))\), use trace-ideal bounds \(\log|\det_2(I-A)|\lesssim \|A\|_{\mathrm{HS}}^2\) to reduce A2c2-BT\(_{\mathrm{Nev}}\) to uniform Hilbert--Schmidt norm control for \(A(\sigma+it)\). This may dovetail with RG energy-budget estimates (B1).

## Micro-goal for the next session (pick ONE; do not do all)

- **CR/Green micro-goal (preferred)**: prove the *smallest analytic subgate* needed to feed `Port.pairing_whitney_analytic_bound` (e.g. a faithful Green trace identity on Whitney boxes, or the test-energy/Cauchy–Schwarz bound), and then derive `Port.HardyDirichletCRGreen cofactorEbox_poisson`.
- **Boundary-term micro-goal**: isolate and prove the “no boundary term at infinity” gate needed for the Green identity on Whitney boxes (this is usually where hidden assumptions live).
- **Oscillation micro-goal**: prove `OscillationTarget` for `logAbsXi` (or a strictly weaker replacement certificate that still closes the wedge).
- **Lean-interface micro-goal**: generalize Lean `phase_velocity_identity` to the distributional/measure form (test functions), so we can stop hard-coding pointwise `deriv boundaryPhase`.

## Operating procedure (every time you work)

1. **Read context**
   - Open `recognition-geometry-dec-18.tex` and identify the section(s) relevant to the new instruction.
   - Open this file (`WRITTEN_PROOF_PROMPT.md`) and apply its rules.

2. **Update this prompt file FIRST (yes, this file)**
   - Add the new instruction to **“Instruction Inbox”** with today’s date.
   - Translate it into 1–5 concrete edits under **“Next edits (short queue)”**.
   - If the instruction touches a “hard wall”, add/update an item under **“Hard walls backlog”** and link it to an assumption ID.

3. **Edit the paper**
   - Implement the requested changes in `recognition-geometry-dec-18.tex`.
   - Maintain journal style: definitions before use, explicit hypotheses, clear theorem chains, proper citations, no overclaims.

4. **Keep it compiling**
   - Run `pdflatex -interaction=nonstopmode -halt-on-error recognition-geometry-dec-18.tex` and fix any LaTeX errors you introduced.

5. **Post-edit cleanup**
   - Update the **Assumption Ledger** (below): mark items as `open / weakened / proved / removed`.
   - Update **Change Log** (below) with a 3–10 line summary of what changed.

## Quality bars (journal-ready)

- **No hidden axioms**: anything not proved in the paper is labeled and enumerated.
- **No ambiguous “we assume positivity”**: state the exact proposition (domain, measure class, regularity).
- **Stable notation**: one definition per symbol; maintain a notation index.
- **Citations**: every classical theorem used (Weil explicit formula, Li criterion, Herglotz/Carathéodory, GNS/RKHS) has a bib entry.
- **Conditional vs unconditional clarity**: theorems that depend on open assumptions must say so explicitly.

## Improvement loop (always-on, but low-churn)

After completing the user’s explicit request, do *one* improvement pass (only if it won’t cause large disruptive churn).
**But**: prefer an improvement that creates mathematical progress (e.g. replacing an assumption with a standard cited lemma) over purely stylistic edits.

- tighten theorem statements (remove vagueness like “sufficiently rich” by pointing to a definition or class),
- add missing citations,
- reduce repetition and convert narrative “strategy” into lemma-proof structure,
- align paper statements with the formal objects in `RiemannRecognitionGeometry/ExplicitFormula/` where possible.

If an improvement would require many edits, add it to “Hard walls backlog” instead of making a huge change.

## Versioning rule

When we hit any of these milestones, create a new dated snapshot `recognition-geometry-dec-XX.tex` and keep working in the newest file:

- we remove/replace a major assumption,
- we prove a previously assumed lemma,
- we restructure the main theorem chain,
- or the user explicitly requests a snapshot.

## Instruction Inbox (append-only)

- **2025-12-18**: Create this prompt/driver file and create a Dec-18 snapshot of the paper.
- **2025-12-18**: Start using this driver to push the written proof forward: add a paper-facing Assumption Ledger, decompose the Route~3 “spectral identity” into smaller named sub-claims (identity vs positivity vs analytic interchange/boundary limits), and add missing classical citations (Herglotz/Carathéodory, RKHS/GNS/OS as needed).
- **2025-12-18**: Tighten the Route~3 “spectral identity” assumptions so the \(H=L^2(\mu)\) step is formally correct (explicit \(L^2\) integrability, and if \(\mu\) is allowed to be complex/signed then use total variation \(|\mu|\)).
- **2025-12-18**: Split Assumption A2 into named sub-assumptions that mirror the actual analytic steps (Fourier inversion, Mellin inversion/change-of-variables, contour-to-boundary limits, Fubini/Tonelli interchanges) and reflect that split both in this driver and in the paper’s Assumption Ledger.
- **2025-12-18**: Start discharging A2 items: first, replace “Fourier inversion” (A2a) with a standard cited lemma for Schwartz functions, so A2a reduces to verifying Schwartzness/compatibility for the specific transforms \(F_f\).
- **2025-12-18**: Update the driver to make “unconditional RH proof” the explicit priority and to prefer mathematical progress (discharging assumptions) over polish whenever possible.
- **2025-12-18**: Align the driver’s assumption ledger with the repo’s *actual unconditional blockers* (see `REMAINING_WORK.md` / `PROOF_STATUS_CURRENT.md`): include the RG track gaps (Carleson-energy bottleneck + oscillation/BMO certificate + remaining classical-analysis axioms) alongside the Route~3 gaps.
- **2025-12-18**: Discharge B3 for the *written* proof by replacing “classical-analysis axioms” with precise standard citations and minimal hypothesis checks (still leaving Lean to later port/prove).
- **2025-12-18**: Chip away at A2d by splitting it into standard measure-theory interchanges (Fubini/Tonelli + dominated convergence) vs the genuinely RH-adjacent “prime-sum interchange” estimates; discharge the standard part in the written proof via citations and isolate the remaining analytic condition explicitly.
- **2025-12-18**: Discharge A2d3 for the written proof by routing prime-sum interchanges through the absolutely convergent region \(\Re(s)>1\) and then using analytic continuation/identity theorems to extend equalities, avoiding non-justified interchange at the critical line.
- **2025-12-18**: Discharge the *standard* part of A2c for the written proof by citing Hardy-space boundary limits (Fatou theorem) on a half-plane, and rewrite A2c so it reduces to verifying the needed Hardy/growth hypotheses for the specific functions appearing in Route~3.
- **2025-12-18**: Make the “extend equalities by analytic continuation” step fully explicit in the paper by adding a cited identity-theorem lemma and referencing it where we route prime-sum interchanges through \(\Re(s)>1\).
- **2025-12-18**: Make A2c2 explicit by naming the concrete Route~3 symbol \(J=\det_2/(O\,\xi)\) and stating the exact boundary/phase/log-derivative hypotheses required (Hardy/bounded-type + unimodular trace + phase regularity sufficient to interpret \(J'/J=\theta'\) a.e.).
- **2025-12-18**: Decompose the Route~3 “spectral identity” (A1) into splice-completion inputs matching `ExplicitFormula/ContourToBoundary.lean` (explicit-formula cancellation + phase–velocity identity + normalization + pair factorization), and mirror that decomposition in both the driver and the paper.
- **2025-12-18**: For the written proof, explicitly cite Lagarias’ survey (Thm 3.1 / Guinand–Weil explicit formula) as the source of the explicit-formula cancellation step in the splice-completion chain, so the remaining novelty is isolated to the phase–velocity/spectral-measure step.
- **2025-12-18**: Refactor the Route~3 theorem chain in the paper so the “assumption” matches the splice-completion interface (positive spectral measure + pair factorization + normalization), rather than a generic \(\exists\mu\) spectral identity.
- **2025-12-18**: Split A1 into A1a–A1d mirroring the splice chain (`explicit_formula_cancellation`, `phase_velocity_identity`, pair factorization, normalization) so each subclaim can be attacked independently in the written proof and in Lean.
- **2025-12-18**: Make A1b (phase–velocity identity) explicit in the paper/driver in the exact “test function” form used in Lean: \(\int \phi\,\theta' \,dt = -\pi\int \phi\, d\mu_{\mathrm{spec}}\), and record the a.e. density interpretation \(\theta'=-\pi\rho\) when \(\mu_{\mathrm{spec}}\ll dt\).
- **2025-12-18**: Add a “no-loops” hard-wall chipping protocol (single boxed wall + angle-switch menu) so each session either makes a concrete artifact or explicitly downgrades the current wall.
- **2025-12-18**: Downgrade the boxed A1b wall to the smallest equivalent “density gate” A1b': \(\theta\in W^{1,1}_{loc}\) and \(\theta'\le0\) a.e. (then \(\mu_{\mathrm{spec}}\) is definitional); add fallback A1b'' (distributional/measure form) if a.e. differentiability is too strong.
- **2025-12-18**: Add a reality-check note: the ζ concrete stub’s \(\theta=-2\arg\Gamma_{\mathbb R}(1/2+it)-\pi\) has \(\theta'(0)>0\), so A1b' may be false globally; be ready to downgrade to A1b'' (Herglotz/Clark measure form).
- **2025-12-18**: Actually downgrade the single boxed hard wall to A1b'' (distributional positive-measure form), since A1b' (global \(\theta'\le0\)) is likely false for the ζ gamma-ratio model.
- **2025-12-18**: Add a paper lemma showing A1b'' follows from a standard \emph{co-inner} hypothesis on \(J\) (canonical factorization / boundary argument BV \(\Rightarrow\) positive measure), so the hard wall becomes: prove \(1/J\) is inner.
- **2025-12-18**: Add a paper lemma making the subgate explicit: bounded-type + unimodular boundary values \(\Rightarrow\) \(J\) inner \(\Rightarrow\) A1b'' (positive measure).
- **2025-12-18**: Add a Lean-interface note: `phase_velocity_identity` should be generalized to the distributional/measure form (test functions) to match the honest A1b'' wall and avoid forcing absolute continuity/densities.
- **2025-12-18**: Record a key reduction: A1b'' likely follows from the A2c2 Hardy/bounded-type package plus unimodular boundary values (bounded-type \(\Rightarrow\) inner \(\Rightarrow\) BV argument \(\Rightarrow\) positive measure).
- **2025-12-18**: Add paper lemmas spelling out bounded type facts: (i) bounded type \(\Leftrightarrow\) harmonic majorant for \(\log^{+}|J|\), and (ii) closure under products/quotients. Use these to make the A2c2-BT wall more concrete.
- **2025-12-18**: Re-box the hard wall as the explicit Nevanlinna integral bound for \(J\), and add the paper lemma `\ref{lem:bounded_type_nevanlinna_integral}` equating this to bounded type.
- **2025-12-18**: Add a one-line sufficient condition: uniform polynomial growth on vertical lines \(\Rightarrow\) Nevanlinna bound (paper Lemma~`\ref{lem:poly_growth_implies_nevanlinna}`), plus a sanity-check remark that the zeta gamma-ratio model satisfies it by Stirling.
- **2025-12-18**: Add an “operator-theoretic angle” for the bounded-type wall: if \(\det_2=\det_2(I-A)\), trace-ideal bounds reduce the Nevanlinna condition to uniform control of \(\|A(\sigma+it)\|_{\mathrm{HS}}\) (potentially linking Route~3 A2c2-BT to RG energy-budget B1).
- **2025-12-18**: Add a practical “strip + far-right” reduction note for A2c2-BT\(_{\mathrm{Nev}}\): bound the Nevanlinna integral on \(1/2<\sigma\le\sigma_0\) and separately show uniform boundedness for \(\sigma\ge\sigma_0\) from normalization/absolute convergence/determinant bounds.
- **2025-12-18**: Add a component-wise reduction note: bounded type for \(J=\det_2/(O\,\xi)\) reduces to bounded type of \(\det_2,O,\xi\) and nonvanishing of \(O,\xi\), so the “truth serum” is growth control for \(\det_2\) (or the underlying operator \(A\)).
- **2025-12-18**: Fix the component-wise reduction note (again, more honestly): bounded type is a \emph{meromorphic} notion, so we do *not* assume \(\xi\) nonvanishing on \(\Omega\) and we do not require cancellation/removability at \(\xi\)-zeros. Poles are allowed; the Nevanlinna integral bound is the real regularity target.
- **2025-12-18**: Add a pole sanity-check: \(\xi\) is order 1/genus 1 so its zeros satisfy \(\sum|\rho|^{-2}<\infty\), hence the half-plane Blaschke sum converges; poles of \(J\) at \(\xi\)-zeros do not automatically obstruct bounded type (paper Lemma~`\ref{lem:blaschke_sum_from_genus_one}` + Remark~`\ref{rem:xi_blaschke_condition}`).
- **2025-12-18**: Fix a paper overclaim: bounded type + unimodular boundary values does *not* imply A1b'' positivity for the (meromorphic) PSC ratio \(J\); it only yields a quotient-of-inner factorization with a signed phase measure. Positivity is the RH-adjacent step that rules out the inner denominator.
- **2025-12-18**: Add a paper lemma formalizing the “quotient of inner factors” statement for meromorphic bounded characteristic \(J\) with unimodular boundary values (Lemma~`\ref{lem:quotient_inner_of_bounded_char_unimodular}`), so the regularity⇒signed-measure step is pinned down precisely.
- **2025-12-18**: Add a paper lemma/remark splitting the Nevanlinna strip wall for \(J=\det_2/(O\,\xi)\) into three separate strip-integral bounds via \(\log^{+}\) subadditivity (Lemma~`\ref{lem:logplus_mul}` + Remark~`\ref{rem:logplus_split_J}`).
- **2025-12-18**: Add a paper lemma packaging this reduction as a single implication: three strip-integral bounds (for \(\det_2\), \(1/O\), \(1/\xi\)) imply the strip Nevanlinna bound for \(J\) (Lemma~`\ref{lem:nevanlinna_strip_from_components}`).
- **2025-12-18**: Add a paper lemma isolating the outer-factor subgate: under standard outer/Poisson hypotheses and boundary log-integrability, the strip Nevanlinna bound for \(\log^{+}|1/O|\) holds (Lemma~`\ref{lem:outer_inverse_strip_bound}`).
- **2025-12-18**: Fix an overly-strong decomposition: do not split \(J=\det_2/(O\,\xi)\) into separate \(\det_2\) and \(1/\xi\) Nevanlinna subgates (this ignores cancellation and fails in the \(\zeta\)-gauge). Re-box the wall in terms of the cancellation ratio \(F=\det_2/\xi\) and rewrite the strip reduction accordingly.
- **2025-12-18**: Fix another over-strengthening: do not re-box the wall in terms of a Nevanlinna strip bound for \(F=\det_2/\xi\) (too strong: outer normalization is designed to cancel \(F\)'s growth). Re-box the wall as the Nevanlinna strip bound for the PSC ratio \(J=\det_2/(O\,\xi)\).
- **2025-12-18**: Add a standard lemma that a Blaschke-summable inner denominator contributes a controlled Nevanlinna strip term (Lemma~`\ref{lem:blaschke_inverse_strip_nevanlinna}`), so pole contributions are not the main obstruction.
- **2025-12-18**: Add a ζ-gauge sanity check: in the repo’s concrete ζ instantiation, \(J\) cancels to a pure gamma ratio \(-\Gamma_{\mathbb R}(1-s)/\Gamma_{\mathbb R}(s)\) (paper Remark~`\ref{rem:zeta_gauge_J_gamma_ratio}`), so the Nevanlinna strip wall is routine by Stirling in that gauge.
- **2025-12-18**: Fix a definition-level mismatch: the boxed wall is about a meromorphic \(J\), so update the paper lemma `\ref{lem:bounded_type_nevanlinna_integral}` to the meromorphic “bounded characteristic” form and stop advertising the holomorphic harmonic-majorant equivalence as an equivalence for \(J\).
- **2025-12-18**: Re-box the hard wall to the boundary strip \(1/2<\sigma\le 1\) and add a paper lemma handling the far-right region \(\sigma\ge 1\) from a polynomial-growth bound (Lemma~`\ref{lem:nevanlinna_far_right_poly}`).
- **2025-12-18**: Add a distributional splice note: once A1b is phrased via \(d\theta\), A1a should be phrased as a Stieltjes pairing \(\int F_h\,d\theta\), and the algebraic splice uses Lemma~`\ref{lem:splice_completion_algebra_distributional}`.
- **2025-12-18**: Re-box the single current hard wall away from Route-3 Nevanlinna regularity (routine in the ζ-gauge) and onto the actual RG analytic bottleneck: the CR/Green “energy → phase” bound `Port.HardyDirichletCRGreen cofactorEbox_poisson`.
- **2025-12-18**: Mine `riemann-finish`’s `CRGreenOuter.lean` for the minimal subgates (pairing bound + remainder bound ⇒ boundary bound; then Carleson budget ⇒ uniform bound) and port the *algebraic* core into this repo as a reusable lemma.
- **2025-12-19**: Chip the RG boundary-term gate: re-box the single hard wall to the *direct* Port hook `PhaseVelocityBoundaryTrace` (and treat `CRBoundaryTraceLog` as an archetype sufficient condition). Add a paper lemma clarifying the equivalent boundary-trace forms (x-derivative vs normal-derivative) so the written proof matches the Lean interface choice.

## Next edits (short queue)

- [x] Fix Assumption A1a/A1b in the paper so \(T:\mathcal{T}\to L^2(\mu)\) is well-defined (require \(F_f\in L^2(|\mu|)\) and positivity upgrades to \(\mu\ge0\)).
- [x] Add a dedicated “Assumption Ledger” section to the paper body (not just in repo docs).
- [x] Split “Route 3 reduction” into smaller named lemmas/assumptions that match Lean modules (spectral identity vs positivity of boundary measure vs interchange/Fubini/boundary limits).
- [x] Add citations for Herglotz/Carathéodory and (optionally) RKHS/GNS/OS.
- [x] Split A2 into A2a–A2d (paper + driver) and attach each to concrete Lean files/modules where the corresponding lemmas live.
- [x] Add a paper lemma “Fourier inversion for Schwartz functions” + citation, and update A2a to only require Schwartzness/compatibility of \(F_f\).
- [x] Reduce A2b (Mellin inversion/change-of-variables) to a proved log-Schwartz lemma derived from Fourier inversion; leave only the “verify log-Schwartz + match normalization” obligations.
- [x] Discharge B3 in the written proof: replace the “classical-analysis axioms” bullet with explicit theorem names + citations (JN, Fefferman–Stein duality, BMO→Carleson via Poisson extension, η–ζ relation/analytic continuation).
- [x] Add RG-track blockers (G1–G3) to the driver’s Assumption Ledger + Hard walls backlog, and mirror them in the paper’s Assumption Ledger section.
- [x] Split A2d into (i) standard interchanges (Fubini/Tonelli + dominated convergence) vs (ii) prime-sum interchange, and discharge (i) in the written proof via citations.
- [x] Discharge A2d3 for the written proof: add a cited lemma on absolute convergence of \(-\zeta'/\zeta\) Dirichlet series for \(\Re(s)>1\) and explain how analytic continuation avoids further prime-sum interchanges.
- [x] Discharge the standard part of A2c in the written proof: add a cited Hardy/Fatou boundary-limit lemma (half-plane) and reduce A2c to verifying \(H^p\)/growth hypotheses for the specific symbols.
- [x] Add a cited “identity theorem / analytic continuation” lemma to the paper and reference it in the A2d3 discussion.
- [x] Make A2c2 explicit (paper + driver): specify the symbol \(J\), the half-plane, which \(H^p\) (or bounded-type) hypothesis is needed, and the minimal phase regularity needed so \(J'/J=\theta'\) is meaningful a.e.
- [x] Decompose A1 (paper + driver) into the concrete splice-completion subclaims and point each subclaim at the corresponding Lean locus (`ContourToBoundary.lean`, `ZetaRightEdgePhaseLimit.lean`, `PSCSplice.lean`).
- [x] Add a precise Lagarias (2007) citation in the paper for the explicit-formula cancellation step (A1-cancel) and add the corresponding bibliography entry.
- [x] Refactor the Route~3 theorem chain assumptions to match splice completion (positive \(\mu_{\mathrm{spec}}\), factorization \(F_{\mathrm{pair}}=\overline{F_f}F_g\), normalization), and update the corresponding assumption labels/ledger text.
- [x] Split A1 into A1a–A1d (paper + driver), and update A1’s status/plan to track which pieces are “cite Lagarias” vs genuinely new.
- [x] Make A1b (phase–velocity) explicit in both driver and paper, matching the Lean interface and clarifying the density interpretation.
- [ ] Strengthen the boundary-term gate interface to be non-vacuous: tie the `PhaseVelocityBoundaryTrace` “trace field” to the same 2D harmonic field whose Carleson-box energy defines `cofactorEbox_poisson` (Poisson/conjugate-Poisson model + boundary trace as a limit, not point-evaluation).

## Assumption Ledger (paper-facing map)

Each assumption must have: **ID**, **statement (1–5 lines)**, **where used**, **status**, and a **next-proof plan**.

- **A1 (Route3 spectral identity via splice completion)**  
  - **Statement**: Identify the Weil pairing \(B(f,g)=W^{(1)}(f\star_m \widetilde{\overline g})\) with a positive-measure boundary pairing
    \[
      B(f,g)=\frac12\int_{\mathbb{R}} \overline{F_f(t)}\,F_g(t)\,d\mu_{\mathrm{spec}}(t),
    \]
    where \(F_f\) is the Route~3 boundary transform (Mellin/Fourier-normalized) and \(\mu_{\mathrm{spec}}\) is a positive spectral measure.  
  - **Where used**: `Route 3` theorem chain (spectral identity ⇒ RP realization ⇒ Weil gate ⇒ RH).  
  - **Status**: open  
  - **Next-proof plan**: prove the \emph{splice completion} chain matching `ExplicitFormula/ContourToBoundary.lean`:
    (i) an explicit-formula cancellation identity reducing \(W^{(1)}\) to a boundary pairing against the PSC boundary phase derivative,
    and (ii) a phase–velocity identity identifying that derivative with a positive boundary measure \(\mu_{\mathrm{spec}}\).
    The remaining analytic bookkeeping is normalization (the \(1/2\) factor) and the pair-factorization \(F_{\mathrm{pair}(f,g)}=\overline{F_f}\,F_g\).
  - **Lean locus**: `RiemannRecognitionGeometry/ExplicitFormula/ContourToBoundary.lean` (definitions `explicit_formula_cancellation`, `complex_phase_velocity_identity`, theorem `splice_completion_with_normalization`);
    `.../ZetaRightEdgePhaseLimit.lean` (right-edge limit scaffolding);
    `.../PSCSplice.lean` (wiring into the Route~3 pipeline).

- **A2 (Route3-FourierInversion / boundary limits)**  
  - **Statement**: the analytic inversion/limit/interchange steps needed to identify the transform side with the Weil functional, split as A2a–A2d below.  
  - **Where used**: construction of \(F_f\), justification of the identity in A1a.  
  - **Status**: open  
  - **Next-proof plan**: discharge A2a–A2d one-by-one, tightening hypotheses to the concrete test space used in Route~3.

- **A2a (Fourier inversion on test space)**  
  - **Statement**: Fourier inversion for the specific boundary transforms \(F_f\) used in Route~3.  
  - **Where used**: A1a identity (turn boundary integrals into \(F_f\)).  
  - **Lean locus**: `RiemannRecognitionGeometry/ExplicitFormula/ZetaFourierInversionWeil.lean`  

- **A2b (Mellin inversion / change-of-variables)**  
  - **Statement**: Mellin-side change-of-variables and inversion compatibilities aligning Lagarias normalization with multiplicative convolution/involution.  
  - **Where used**: A1a identity (normalization alignment).  
  - **Lean locus**: `.../MathlibBridge.lean`, `.../MulConvolution.lean`, `.../Lagarias.lean`  

- **A2c (Contour → boundary limits / right-edge limits)**  
  - **Statement**: boundary-limit results (Fatou-type / distributional boundary values) and right-edge limiting procedure needed to identify contour expressions with boundary objects. Split as A2c1–A2c2.  
  - **Where used**: A1a identity (contour-to-boundary reduction).  
  - **Status**: paper: A2c1 closed (cited), A2c2 open; Lean: open  
  - **Lean locus**: `.../ContourToBoundary.lean`, `.../ZetaRightEdgePhaseLimit.lean`, `.../LagariasContour.lean`  

- **A2c1 (Hardy/Fatou boundary limits on a half-plane)**  
  - **Statement**: if a holomorphic function lies in a Hardy space \(H^p\) on a half-plane, then it has a.e. nontangential boundary limits and Poisson representation.  
  - **Status**: paper: closed (standard); Lean: open  

- **A2c2 (Verify Hardy/growth hypotheses for the Route~3 symbols)**  
  - **Statement**: for the PSC ratio
    \(J(s)=\det_2(s)/(O(s)\,\xi(s))\) on \(\Omega=\{\Re(s)>1/2\}\),
    verify a bounded-type/Hardy hypothesis (e.g. \(J\in H^\infty(\Omega)\) or \(J\) is inner on \(\Omega\)) giving a.e. boundary limits,
    together with a measurable phase \(\theta\) such that \(J(1/2+it)=e^{i\theta(t)}\) a.e. and enough regularity on \(\theta\) (e.g. \(\theta\in W^{1,1}_{\mathrm{loc}}\))
    so that the boundary log-derivative identity \(J'/J=\theta'\) is meaningful a.e.  
  - **Status**: open  

- **A2d (Interchange: Fubini/Tonelli + prime-sum interchanges)**  
  - **Statement**: interchange steps needed to swap integrals, limits, and (where applicable) prime sums in the explicit formula manipulations. Split as A2d1–A2d3.  
  - **Where used**: A1a identity (justification of interchanges).  
  - **Status**: paper: A2d1/A2d2/A2d3 closed (cited/route through \(\Re(s)>1\)); Lean: open  
  - **Lean locus**: `.../Route3FubiniTonelliLemmas.lean` and dependent analytic files.

- **A2d1 (Fubini/Tonelli for the relevant integrals)**  
  - **Statement**: justify swapping iterated integrals by absolute integrability (or nonnegativity).  
  - **Status**: paper: closed (standard); Lean: open  

- **A2d2 (Dominated convergence / limit–integral interchange)**  
  - **Statement**: justify exchanging limits with integrals under an integrable dominating function.  
  - **Status**: paper: closed (standard); Lean: open  

- **A2d3 (Prime-sum interchange / absolute convergence control)**  
  - **Statement**: justify exchanging explicit-formula prime sums (or Dirichlet series expansions) with integrals/limits in the region of interest, using absolute convergence or uniform dominated bounds.  
  - **Status**: paper: closed (route through \(\Re(s)>1\) + analytic continuation); Lean: open  

### Route 3 (ExplicitFormula) assumptions (decomposed)

- **A1a (Explicit-formula cancellation / contour → boundary)**  
  - **Statement**: prove the explicit-formula cancellation step that reduces \(W^{(1)}(h)\) to a boundary integral against the PSC boundary phase derivative (Lagarias Thm 3.1 as the source statement; plus contour-to-boundary limit justifications).  
  - **Status**: open  
  - **Lean locus**: `.../ContourToBoundary.lean` (`explicit_formula_cancellation`, `..._contour`, and the right-edge limit scaffolding in `ZetaRightEdgePhaseLimit.lean`)

- **A1b (Phase–velocity / spectral measure identity)**  
  - **Statement**: identify the boundary phase derivative with a positive spectral measure \(\mu_{\mathrm{spec}}\) (the “phase–velocity identity”).
    In the current Lean interface (integrating \(\theta'(t)\) against Lebesgue measure), this is equivalent to requiring an a.e. density
    \[
      \theta'(t) = -\pi\,\rho(t)\quad \text{a.e.},\qquad \rho(t)\ge0,
    \]
    and then \(\mu_{\mathrm{spec}}=\rho(t)\,dt\).  
  - **Lean note (current ζ stub)**: `ZetaInstantiation.lean` defines
    `μ_spec_zeta := volume.withDensity (t ↦ ENNReal.ofReal (-(1/π) * θ'(t)))`;
    to make the phase–velocity identity tautological (no `ofReal` clipping), it suffices to prove \(\theta'(t)\le 0\) a.e.
  - **Status**: open  
  - **Lean locus**: `.../ContourToBoundary.lean` (`PSCComponents.phase_velocity_identity`, `complex_phase_velocity_identity`)

- **A1c (Pair factorization of boundary transforms)**  
  - **Statement**: for \(h=\mathrm{pair}(f,g)\), the boundary transform factors as \(F_h=\overline{F_f}\,F_g\).  
  - **Status**: open  
  - **Lean locus**: `.../PSCSplice.lean` / test-space wiring

- **A1d (Normalization tracking)**  
  - **Statement**: track the global constants (the \(1/2\) factor) in the splice-completion identity.  
  - **Status**: mostly bookkeeping  
  - **Lean locus**: `.../ContourToBoundary.lean` (`splice_completion_with_normalization`) and the written lemma `splice completion (algebraic step)`

### Recognition Geometry (RG) track assumptions (Main.lean route)

- **B1 (RG bottleneck: Carleson energy budget)**  
  - **Statement**: discharge `RGAssumptions.j_carleson_energy_axiom_statement` (the “energy budget” per Whitney interval / tent region).  
  - **Where used**: RG main theorem (`RiemannRecognitionGeometry/Main.lean`) via the boundary-certificate / tail-budget chain.  
  - **Status**: open  
  - **Next-proof plan**: port the statement-shape from the HardyDirichlet blueprints (`REALITY_PORT_PLAN.md`) and prove it via a CR–Green + Carleson/Hardy pipeline (or VK-density packing bounds), explicitly tracking constants.

- **B2 (Oscillation certificate for \(\log|\xi|\))**  
  - **Statement**: produce `OscillationTarget := ∃ M, InBMOWithBound logAbsXi M ∧ M ≤ C_tail`.  
  - **Where used**: RG main theorem (`RiemannRecognitionGeometry/Main.lean`).  
  - **Status**: open  
  - **Next-proof plan**: prove a concrete BMO/oscillation bound for `logAbsXi` (or a replacement certificate) sufficient to feed the tail-budget inequality.

- **B3 (Remaining classical-analysis axioms in compiled RG modules)**  
  - **Statement**: replace remaining global `axiom` declarations (e.g. John–Nirenberg / Fefferman–Stein / BMO→Carleson embedding / η–ζ identity principle) by cited theorems or full proofs.  
  - **Where used**: RG track infrastructure and the “classical analysis inputs” bundle.  
  - **Status**: paper: closed (cited); Lean: open (axioms)  
  - **Next-proof plan**: for the written proof, cite standard references and state precisely how each theorem is used; for Lean, port/prove the needed forms gradually.

## Hard walls backlog (track + chip away)

These are “hard elements” that will take multiple iterations. Keep each item tight, with a target deliverable.

- **HW1: Route-3 spectral identity**  
  - **Deliverable**: a paper lemma “Spectral identity for \(W^{(1)}\)” with explicit hypotheses and a proof outline that cleanly separates: (i) explicit formula algebra, (ii) interchanges, (iii) boundary values.  
  - **Links**: Assumption A1.

- **HW2: Positivity of boundary measure / kernel**  
  - **Deliverable**: a precise statement equivalent to \(\mu\ge0\) (Pick/Schur kernel positivity, Herglotz representation) and a plan for proving it from the arithmetic input.  
  - **Links**: Assumption A1.

- **HW3: Fourier/Mellin inversion & change-of-variables**  
  - **Deliverable**: finalize the inversion lemmas needed to connect test-function transforms to the explicit formula (and remove the remaining Lean sorries in the Fourier inversion file).  
  - **Links**: Assumption A2.

- **HW4: RG Carleson-energy bottleneck (G1)**  
  - **Deliverable**: a paper lemma (with explicit constants and hypotheses) that implies `RGAssumptions.j_carleson_energy_axiom_statement`, plus a proof plan aligned with the HardyDirichlet blueprints.  
  - **Links**: Assumption B1.

- **HW5: RG oscillation certificate (G2)**  
  - **Deliverable**: a paper theorem producing an explicit oscillation/BMO certificate for \(\log|\xi|\) adequate for the RG chain, with a clear map to what must be formalized.  
  - **Links**: Assumption B2.

## Change Log

- **2025-12-18**: Created `WRITTEN_PROOF_PROMPT.md`. Created `recognition-geometry-dec-18.tex` as a snapshot and updated its `\\date{...}` to “December 18, 2025”.
- **2025-12-18**: Updated `recognition-geometry-dec-18.tex` with a paper-facing Assumption Ledger section; split Route~3’s “spectral identity” into separate (A1a) identity and (A1b) positivity assumptions; added standard references for \(H^p\)/Herglotz-Carathéodory, RKHS, and OS reflection positivity.
- **2025-12-18**: Tightened Route~3 Assumption A1a to a complex-measure form with \(F_f\in L^2(|\mu|)\) (total variation), so the \(H=L^2(\mu)\) realization step is formally correct once A1b (\(\mu\ge0\)) is assumed.
- **2025-12-18**: Split A2 into A2a–A2d (Fourier inversion; Mellin inversion/change-of-variables; contour-to-boundary/right-edge limits; Fubini/Tonelli + prime-sum interchanges) and mirrored that split in both the driver and the paper’s Assumption Ledger, with pointers to the corresponding Lean files.
- **2025-12-18**: Added a cited paper lemma for Fourier inversion on Schwartz functions and updated A2a so it reduces to verifying \(F_f\in\mathcal{S}(\mathbb{R})\) (with the chosen normalization).
- **2025-12-18**: Updated this driver to explicitly prioritize finishing an unconditional RH proof by discharging the Assumption Ledger (math progress first; polish last).
- **2025-12-18**: Added a paper lemma reducing Mellin inversion/change-of-variables (A2b) to Fourier inversion in a log-Schwartz setting; updated A2b so the remaining work is verifying log-Schwartz regularity and matching the Mellin normalization.
- **2025-12-18**: Discharged B3 for the written proof by replacing “classical-analysis axioms” with explicit standard citations (John--Nirenberg, Fefferman--Stein, BMO\(\to\)Carleson via Poisson extension, and \(\eta\)/\(\zeta\) analytic continuation references).
- **2025-12-18**: Discharged the standard part of A2d in the written proof by adding cited lemmas for Fubini/Tonelli (including series–integral interchange) and dominated convergence; isolated the remaining “prime-sum interchange” as the real analytic obligation (A2d3).
- **2025-12-18**: Discharged A2d3 for the written proof by citing absolute convergence of \(-\zeta'/\zeta\) on \(\Re(s)>1\) and routing prime-sum interchanges through that region, then extending equalities by analytic continuation.
- **2025-12-18**: Discharged the standard part of A2c for the written proof by adding a cited Hardy/Fatou boundary-limit lemma on a half-plane; reduced A2c to verifying the Hardy/growth hypotheses for the specific Route~3 symbols and matching boundary values.
- **2025-12-18**: Made the analytic-continuation step explicit by adding a cited identity-theorem lemma and referencing it in the A2d3 “route through \(\Re(s)>1\)” justification.
- **2025-12-18**: Made A2c2 explicit by naming the PSC ratio \(J=\det_2/(O\,\xi)\), stating the needed bounded-type/Hardy + unimodular phase-trace + phase-regularity hypotheses, and adding a lemma computing \(J'/J=\theta'\) under pointwise \(C^1\) trace regularity.
- **2025-12-18**: Decomposed A1 (Route~3 spectral identity) into splice-completion inputs (explicit-formula cancellation + phase–velocity identity + pair factorization + normalization) and pointed the written proof/driver to the corresponding Lean loci in `ExplicitFormula/ContourToBoundary.lean` and related files.
- **2025-12-18**: Added a small “splice completion algebra” lemma to the paper to make the cancellation + phase–velocity ⇒ measure-pairing step completely explicit (mirrors `splice_completion_with_normalization` in the Lean file).
- **2025-12-18**: Cited Lagarias’ survey (Thm.~3.1) as the source for the explicit-formula cancellation step in the Route~3 splice-completion chain; added a `Lagarias2007` bibliography entry.
- **2025-12-18**: Refactored the Route~3 theorem chain to assume the splice-completion spectral identity directly (positive \(\mu_{\mathrm{spec}}\) and the \(1/2\) normalization), aligning the paper’s assumption with the Lean splice pipeline.
- **2025-12-18**: Split Route~3 A1 into A1a–A1d (explicit-formula cancellation, phase–velocity identity, pair factorization, normalization) to match the splice-completion pipeline and make the remaining hard steps maximally explicit.
- **2025-12-18**: Made A1b (phase–velocity identity) explicit in the test-function form used in Lean, and recorded the a.e. density interpretation \(\theta'=-\pi\rho\) when \(\mu_{\mathrm{spec}}\ll dt\).
- **2025-12-18**: Added a session trigger + “no-loops” protocol; declared a single boxed hard wall (A1b) and an angle-switch menu to force creative reframings before downgrading.
- **2025-12-18**: Refined the A1b hard wall to emphasize the absolutely-continuous “density” regime: \(d\mu_{\mathrm{spec}}=\frac{1}{\pi}(-\theta')\,dt\), so the remaining content is sign/regularity (\(\theta'\le0\) a.e.) plus integrability.
- **2025-12-18**: Replaced the boxed hard wall with the strictly smaller A1b' “phase monotonicity/density gate” and added an explicit fallback A1b'' (distributional/Clark/Herglotz measure form) to keep chipping honest if a.e. differentiability is unrealistic.
- **2025-12-18**: Added an explicit “reality check” warning that A1b' (global \(\theta'\le0\)) may fail for the ζ gamma-ratio model; updated the chipping plan to treat A1b'' (positive measure / Clark/Herglotz) as the likely honest endpoint.
- **2025-12-18**: Replaced the boxed hard wall with A1b'' (distributional phase–velocity / positive measure), and added micro-goals prioritizing a Clark/Herglotz lemma that produces \(\mu_{\mathrm{spec}}\ge0\) from Schur/Carathéodory hypotheses.
- **2025-12-18**: Added a paper-facing lemma: A1b'' follows from a co-inner hypothesis on the PSC ratio \(J\) via standard inner-function boundary theory (canonical factorization); updated the driver to treat “prove \(1/J\) is inner” as the next honest subgate.
- **2025-12-18**: Added a driver note/micro-goal to generalize the Lean `phase_velocity_identity` interface to the distributional/measure form, aligning Lean with the honest A1b'' wall.
- **2025-12-18**: Added a driver-level reduction showing how A1b'' can plausibly be discharged from A2c2 once the Hardy/bounded-type hypothesis for the PSC ratio \(J\) is proved.
- **2025-12-18**: Added a driver note and micro-goal to rewrite A1a in distributional/Stieltjes form to match A1b'', so the splice completion becomes pure measure-algebra (no pointwise \(\theta'\) needed).
- **2025-12-18**: Added Lemma~`\ref{lem:inner_of_bounded_type_unimodular}` to the paper and recorded it in the driver: A2c2 (bounded type + unimodular boundary) should imply \(J\) is inner, which in turn standardly yields A1b''.
- **2025-12-18**: Added paper Lemma~`\ref{lem:bounded_type_harmonic_majorant}` (bounded type \(\Leftrightarrow\) harmonic majorant for \(\log^{+}|f|\)) and Lemma~`\ref{lem:bounded_type_closed}` (closure under products/quotients), and updated the driver with equivalent bounded-type formulations.
- **2025-12-18**: Added paper Lemma~`\ref{lem:bounded_type_nevanlinna_integral}` (bounded type \(\Leftrightarrow\) Nevanlinna integral bound) and updated the driver’s boxed hard wall to this explicit inequality for \(J\).
- **2025-12-18**: Updated paper Lemma~`\ref{lem:bounded_type_nevanlinna_integral}` to the correct meromorphic “bounded characteristic” formulation (since \(J\) is expected meromorphic on \(\Omega\)); updated the driver to treat the Nevanlinna integral as the primary check for \(J\).
- **2025-12-18**: Re-boxed the Nevanlinna wall to the boundary strip \(1/2<\sigma\le 1\) and added paper Lemma~`\ref{lem:nevanlinna_far_right_poly}` to isolate the far-right \(\sigma\ge 1\) part as a routine growth check.
- **2025-12-18**: Added paper Lemma~`\ref{lem:poly_growth_implies_nevanlinna}` (uniform polynomial growth \(\Rightarrow\) Nevanlinna bound) and a sanity-check remark for the zeta gamma-ratio model.
- **2025-12-18**: Added a paper remark linking bounded type for \(J=\det_2/(O\,\xi)\) to trace-ideal growth bounds for a determinant model \(\det_2(I-A)\), and added a corresponding angle-switch in the driver.
- **2025-12-18**: Added a paper remark explaining the standard “boundary strip vs far-right region” strategy for checking the Nevanlinna supremum, and recorded the same reduction in the driver.
- **2025-12-18**: Added a paper remark making the bounded-type wall component-wise: \(J\) bounded type follows from bounded type of \(\det_2,O,\xi\) + nonvanishing, sharpening the target to “control \(\det_2\)” (or \(\|A\|_{\mathrm{HS}}\)” in the determinant model.
- **2025-12-18**: Corrected the component-wise bounded-type remark to avoid smuggling RH \emph{without} adding extra cancellation hypotheses: treat \(J\) as meromorphic bounded type (poles allowed at \(\xi\)-zeros), and separate this regularity wall from the RH-adjacent positivity wall (ruling out an inner denominator).
- **2025-12-18**: Added a paper lemma/remark that the \(\xi\)-zero set satisfies the half-plane Blaschke summability condition (genus-one implies \(\sum|\rho|^{-2}<\infty\)), and updated the driver with the corresponding pole sanity-check for the bounded-type wall.
- **2025-12-18**: Corrected the paper narrative to separate bounded-type regularity (Nevanlinna class for meromorphic \(J\)) from the RH-adjacent positivity wall (ruling out an inner denominator); removed the implication “bounded type ⇒ A1b'' positivity” as an overclaim.
- **2025-12-18**: Added paper Lemma~`\ref{lem:quotient_inner_of_bounded_char_unimodular}` and updated the driver/paper text to cite it where we talk about the canonical factorization \(J=(I_1/I_2)\cdot c\).
- **2025-12-18**: Added paper Lemma~`\ref{lem:logplus_mul}` and Remark~`\ref{rem:logplus_split_J}` to reduce A2c2-BT\(_{\mathrm{strip}}\) to three explicit strip-integral subgates for \(\det_2\), \(1/O\), and \(1/\xi\).
- **2025-12-18**: Added paper Lemma~`\ref{lem:nevanlinna_strip_from_components}` formalizing that the three component strip bounds imply A2c2-BT\(_{\mathrm{strip}}\), and updated the driver to cite it.
- **2025-12-18**: Added paper Lemma~`\ref{lem:outer_inverse_strip_bound}` showing the \(1/O\) strip bound follows from outer-function boundary log-integrability + Poisson representation, marking the outer term as a likely-easy subgate.
- **2025-12-18**: Re-boxed the Nevanlinna strip wall in terms of \(F=\det_2/\xi\) and updated the driver/paper strip reduction (Remark~`\ref{rem:logplus_split_J}` + Lemma~`\ref{lem:nevanlinna_strip_from_components}`) to respect cancellation.
- **2025-12-18**: Re-boxed the Nevanlinna strip wall back to the PSC ratio \(J\) (not \(F\)), since the outer normalization is supposed to cancel \(F\)'s outer growth; updated the driver to treat \(J\)-Nevanlinna as the correct regularity target.
- **2025-12-18**: Added paper Lemma~`\ref{lem:blaschke_inverse_strip_nevanlinna}` controlling the Nevanlinna contribution of a Blaschke inner denominator and updated the driver with the corresponding “pole contribution is controlled” note.
- **2025-12-18**: Added paper Remark~`\ref{rem:zeta_gauge_J_gamma_ratio}` and updated the driver to record that A2c2-J\(_{\mathrm{strip}}\) is routine in the concrete ζ-gauge used in the repo (gamma-ratio cancellation + Stirling).
- **2025-12-18**: Re-boxed the single “Current hard wall” to the RG CR/Green bottleneck `Port.HardyDirichletCRGreen cofactorEbox_poisson` (energy \(\Rightarrow\) cofactor phase bound); moved the Nevanlinna discussion to “notes” since it’s routine in the ζ-gauge.
- **2025-12-18**: Updated `recognition-geometry-dec-18.tex` to split the RG bottleneck B1 into B1a (Carleson energy budget) and B1b (CR/Green energy \(\Rightarrow\) cofactor phase bound), explicitly pointing to the Lean interface `Port.HardyDirichletCRGreen cofactorEbox_poisson`.
- **2025-12-18**: Added `RiemannRecognitionGeometry/Port/CRGreenAlgebra.lean`, porting the “pairing bound + remainder bound ⇒ boundary bound” algebra from `riemann-finish` and re-exported it via `RiemannRecognitionGeometry/Port.lean`.
- **2025-12-18**: Added `Port.HardyDirichletCRGreenStrong` (energy-form CR/Green bound) and `hardyDirichletCRGreen_of_strong` in `RiemannRecognitionGeometry/Port/HardyDirichletCRGreen.lean`, so the boxed wall can be targeted in its cleanest “sqrt(Ebox)” form.
- **2025-12-18**: Added `Port.CofactorCRGreenAssumptionsStrong` and the discharge lemma to `HardyDirichletCRGreenStrong cofactorEbox_poisson` (in `RiemannRecognitionGeometry/Port/CofactorCRGreenAssumptions.lean`), so the boxed wall has a single concrete cofactor-side target statement.
- **2025-12-18**: Added `weierstrass_tail_bound_of_hardyDirichletStrong` to `RiemannRecognitionGeometry/Port/WeierstrassTailBound.lean`, so downstream RG tail bounds can consume the strong energy-form CR/Green wall directly.
- **2025-12-18**: Added `RiemannRecognitionGeometry/Port/CofactorCRGreenSubgates.lean`, packaging the strong CR/Green wall into two clean analytic sub-inequalities (Green+Cauchy–Schwarz pairing + window-energy scaling) plus the `Real.Angle` representative link, and proved it implies `CofactorCRGreenAssumptionsStrong`.
- **2025-12-18**: Further discharged the “real representative ⇒ angle norm” subgate (S1) by defining `phaseChangeReal_default` and proving `angle_le_abs_real_default` using `Port.cofactorPhaseChange_le_abs_real` (RealPhaseTransfer). Remaining analytic work is now precisely the Green+C–S pairing inequality (S2) and the window-energy scaling bound (S3), plus the boundary-term gate.
- **2025-12-18**: Discharged the window-energy scaling subgate (S3) by defining `windowEnergy_default(I) := (C_geom*(1/√|I|))^2` and proving `windowEnergy_sqrt_bound_default`. Remaining analytic work is now literally the Green+C–S pairing inequality (S2) (plus the boundary-term gate).
- **2025-12-18**: Re-boxed the current hard wall down to S2 only, and added `RiemannRecognitionGeometry/Port/CofactorCRGreenS2.lean` (now: `Port.CofactorCRGreenS2.Assumptions := ∃ T, PairingBound T`) plus `cofactorCRGreenAssumptionsStrong_of_S2`, so proving the two S2 subgates yields the strong energy-form cofactor CR/Green bound.
- **2025-12-18**: Added `RiemannRecognitionGeometry/Port/CofactorCRGreenS2Interfaces.lean`, decomposing the strong cofactor CR/Green bound into the two standard analytic subgates: (S2a) a faithful lift-based trace/FTC gate (`GreenTraceIdentity`) and (S2b) the Cauchy–Schwarz pairing inequality (`PairingBound`), with a lemma producing `Port.CofactorCRGreenAssumptionsStrong` directly.
- **2025-12-18**: Re-boxed the single current hard wall from “S2 inequality” to the strictly smaller “S2a Green trace identity + boundary-term gate” target (`GreenTraceIdentity`), since the pairing bound is now a separate interface.
- **2025-12-19**: Honesty fix: strengthened `Port.CofactorCRGreenS2Interfaces.GreenTraceIdentity` from a vacuous “∃ integrand” statement to a non-vacuous FTC/derivative gate (provides a true phase-velocity density `dPhase` for `rgCofactorPhaseReal` on the Whitney base interval, plus `IntervalIntegrable`), and proved the trace identity via `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
- **2025-12-19**: Faithfulness fix: rewrote the S2a gate to avoid differentiating the principal-branch `arg`. `GreenTraceIdentity` now includes a real-valued lift `theta` whose coercion to `Real.Angle` agrees with `rgCofactorPhaseAngle` on the Whitney base, and the FTC is applied to that lift.
- **2025-12-19**: Further shrink: split the bundled S2a gate into two explicit subgates (`CofactorPhaseLift` and `PhaseVelocityFTC`), and added `GreenTraceIdentity.of_lift_and_ftc` to rebuild the bundled trace gate from the smaller pieces.
- **2025-12-19**: Re-boxed the single “Current hard wall” to the boundary-term gate: the log-branch CR boundary trace identity interface `CRBoundaryTraceInterfaces.CRBoundaryTraceLog` (Lean file `Port/CRBoundaryTraceInterfaces.lean`), which implies the generic `PhaseVelocityBoundaryTrace` hook.
- **2025-12-19**: Refined the boxed wall to the *direct* Port-level boundary-term hook `PhaseVelocityBoundaryTrace` (in `Port/CofactorCRGreenS2Interfaces.lean`), and demoted `CRBoundaryTraceLog` to a semantic “archetype sufficient condition” implying it. Added a non-vacuity note: in any discharge, the trace field must be tied to the same energy model defining `cofactorEbox_poisson`.
- **2025-12-19**: Strengthened the boxed wall again (honesty): replaced the too-weak trace hook by the Poisson-model boundary-limit gate `PhaseVelocityBoundaryTracePoisson` (in `Port/CofactorCRGreenS2Interfaces.lean`), which ties the phase velocity to the \(y\downarrow0\) boundary limit of the conjugate Poisson gradient of `cofactorLogAbs` (the same field defining `cofactorEbox_poisson`).


