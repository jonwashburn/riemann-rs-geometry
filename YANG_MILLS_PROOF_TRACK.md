## Yang–Mills Proof Track (multi-session)

- **Source**: `Yang-Mills.tex`
- **Inventoried on**: 2025-12-20
- **Claim blocks found**: 323  (assumption=1, corollary=46, definition=11, lemma=97, prop=1, proposition=54, remark=13, theorem=100)

## Session log

- **2025-12-20**: Built the complete claim inventory (323 theorem-like blocks) and started full-detail audits. First audited module: OS reflection positivity / transfer operator (`thm:os`, plus `lem:char-pd`, `prop:psd-crossing-gram`, `lem:os-gns-transfer`). Also fixed two correctness issues in `Yang-Mills.tex`: (i) the convex-split \(L^2\) contraction constant, and (ii) an incorrect internal citation in `prop:psd-crossing-gram`. Added missing `\label{...}` tags for 15 proof-relevant unlabeled claims.
- **2025-12-21**: Audited the UEI normalization convention: confirmed `thm:uei-fixed-region`/`thm:U1-lsi-uei` use \(S_R:=\sum_{p\subset R}\phi(U_p)\) (Wilson weight \(e^{-\beta S_R}\), no extra \(a^4\) prefactor). Added ledger #18 (scaling/notation ambiguity) and checked off the corresponding subclaim in the bottleneck checklist. TeX hygiene: renamed the β-weighted local action in `prop:interface-density-ball-avg` to `\mathcal S_R` to avoid silent convention swaps; fixed the sign in the UEI proof Step 2 definition of the “negative log-density” \(V_R\).

## What this file is for

This is the *single place* to (1) enumerate every theorem-like claim in `Yang-Mills.tex`, (2) track proof confidence for each one, and (3) record blockers/conditionals so we can close gaps across multiple sessions without losing context.

For a short start-of-session playbook and “submission readiness” checklist, see `YANG_MILLS_SUBMISSION_CHECKLIST.md`.

**Current single highest-impact blocker (as of 2025-12-24):** closing the fixed-region continuum inputs (U1 tightness + OS1 + NRC uniqueness) beyond a conditional roadmap; Track‑J is the most “finite-dimensional classical” path, but still needs theorem-number-grade citations and any remaining uniformity checks.

## Millennium alignment (Clay YM: unconditional target)

The Clay problem requires an **unconditional** proof of:
- **(Existence)**: a mathematically rigorous 4D quantum Yang–Mills theory for each compact simple gauge group \(G\), satisfying the usual axioms (OS/Wightman framework).
- **(Mass gap)**: a strictly positive continuum spectral gap above the vacuum (in physical units).

This tracker contains a mix of **lattice-only** results (important, but not sufficient by themselves), **continuum-construction** claims (needed to build the continuum theory), and **bottlenecks** (places where the current manuscript is still conditional or would require a genuinely new breakthrough to become Millennium-level unconditional).

### Lattice-only (necessary but not sufficient for Clay)

- **OS positivity / transfer on the lattice**:
  - `thm:os` (YM-0001)
  - `lem:char-pd` (YM-0129), `prop:psd-crossing-gram` (YM-0130), `lem:os-gns-transfer` (YM-0131)
- **Fixed-\(a\) lattice gap mechanisms** (can be fully rigorous at fixed lattice spacing; does not by itself build the \(a\downarrow 0\) continuum theory):
  - `cor:hk-convex-split-explicit` (interface \(L^2\) contraction once a Doeblin/HK split is granted)
  - `prop:int-to-transfer` (YM-0040), `cor:odd-contraction-from-Kint` (YM-0041), `thm:uniform-odd-contraction` (YM-0043), `thm:eight-tick-uniform` (YM-0054)

### Continuum-construction (must be proved for Clay)

These are the steps that actually construct the continuum OS/Wightman theory and transport spectral information to the limit:
- **Tightness / OS axioms on fixed regions**: e.g. `thm:uei-fixed-region`, `prop:os0os2-closure`, `thm:os1-unconditional` (and the global OS packages).
- **Operator convergence (NRC) and uniqueness of the continuum generator**: e.g. `thm:U2-nrc-unique`, `thm:gap-persist-cont`.
- **OS → Wightman export**: `thm:os-to-wightman` (and global variants).
- **Main “existence + gap” theorem as stated in the manuscript**: `thm:main-af-free` (and any global existence theorem it depends on).

### Current open bottlenecks (what blocks an unconditional Clay-level proof *in this manuscript*)

- **Interface smoothing / minorization on fixed slabs (gap mechanism)**:
  - **Active closure (conditional)**: scaling-window UCIS\(_{\rm SW}\) (`thm:ucis-sw` under `eq:ucis-sw-window`) is wired into the main “interface → odd → slab gap” chain (see ledger #21–#23).
  - **Unconditional β-uniform route**: a truly β-uniform, schedule-free one-step minorization remains blocked (legacy coarse-refresh/Doeblin route: ledger #12–#13; full UCIS closure target blocked at `lem:ucis-C-cell-ball`, ledger #20).
- **Existence of the 4D continuum scaling limit at weak coupling**:
  - Any claim asserting a fully constructed global continuum measure/Schwinger functions on \(\mathbb R^4\) (and not just on fixed \(a\) / fixed slabs) is a Clay-level bottleneck unless proved from first principles (typically via a nonperturbative RG/constructive-QFT program).

### Bottleneck worksheet: Continuum existence + OS axioms + NRC (unchecked spine items)

Legend for the “Type” column:
- **STD**: a standard theorem once its hypotheses hold (functional analysis / OS reconstruction / tightness logic)
- **RG**: would require a genuinely nonperturbative 4D construction (RG / constructive QFT) or equally deep new estimates
- **LEAP**: currently an unsupported leap in this manuscript (asserts an outcome without supplying the RG‑grade inputs)

| Claim (label; ID) | Role in the Clay target | What it would actually require | Type | Notes (what to look for in the TeX) |
|---|---|---|:--:|---|
| `thm:uei-fixed-region` (YM-0178) | Tightness / moment control on fixed regions | Nonperturbative control of the weak-coupling regime along \(\beta(a)\to\infty\): uniform exponential (or high-moment) bounds for local observables | **RG** | Now explicitly split into two closure routes (raw small-field vs Track‑J smoothing/universality). Track‑J is designed to reduce the hard “dimension \(m(R,a)\asymp a^{-4}\)” obstruction to a named single-site compact-group input (positive-time heat-kernel LSI) plus a smoothing/limit-commutation step. |
| `lem:os0-explicit-constants` (YM-0258) | OS0 (temperedness) in the limit | Usually follows from UEI/tightness + uniform local polynomial bounds | **STD** | “Standard” conditional on having UEI-type estimates; otherwise as hard as UEI |
| `prop:os0os2-closure` (YM-0181) | Pass OS0/OS2 from lattice to limits | Weak convergence + uniform integrability; reflection positivity preserved under limits | **STD** | Check: the topology used for convergence, and that OS2 positivity is stable under that convergence mode |
| `lem:os2-limit` (YM-0259) | OS2 preserved under limits (global) | Same as above; mostly bookkeeping once the limit measure exists | **STD** | Should reduce to “limits of PSD forms are PSD” on a dense test algebra |
| `thm:os1-unconditional` (YM-0187) | Euclidean invariance OS1 on fixed regions | Isotropy restoration / symmetry recovery as \(a\downarrow 0\) (typically RG-level) | **RG** | Look for where discrete rotational symmetry is upgraded to full \(E(4)\); this is usually a major nonperturbative step |
| `thm:U2-nrc-unique` (YM-0294) | Operator-norm NRC + uniqueness of the continuum generator | Quantitative defect/projector estimates strong enough to upgrade strong-resolvent to **operator-norm resolvent** control uniformly along van Hove nets | **RG** | The abstract functional analysis is standard; the YM verification requires deep quantitative bounds (graph-defect, low-energy projectors, uniform calibrators) |
| `thm:gap-persist-cont` (YM-0095) | Transport a uniform spectral gap to the limit | Standard spectral perturbation once NRC (or strong enough convergence) is proved | **STD** | The bottleneck is not this lemma, but proving its hypotheses for 4D YM |
| `lem:os3-limit` (YM-0260) / `lem:os5-limit` (YM-0261) | OS3/OS5 (clustering + unique vacuum) in the limit | Requires a genuine continuum gap + control of the vacuum sector in the scaling limit | **RG** | If OS3/OS5 are deduced from a proven gap, they become standard; otherwise they are part of the hard problem |
| `thm:global-OS` (YM-0151) / `thm:global-OS0-5` (YM-0068) | A full global continuum OS theory on \(\mathbb R^4\) | Construction of the global continuum measure/Schwinger functions at weak coupling + verification of OS0–OS5 | **RG / LEAP** | This is essentially the “existence” half of the Clay problem; treat as a core bottleneck unless backed by a full constructive program |
| `thm:os-to-wightman` (YM-0207) | Export OS → Wightman; interpret mass gap | Standard OS reconstruction once OS0–OS5 are proved | **STD** | This is “standard” conditional on OS0–OS5; does not solve existence/gap by itself |
| `thm:main-af-free` (YM-0208) | The manuscript’s claimed Clay-level conclusion | Needs both: (i) a real continuum construction at weak coupling, and (ii) a mass-gap mechanism compatible with \(\beta(a)\to\infty\) (currently blocked by β-uniformity, ledger #12) | **RG / LEAP** | This is the end-to-end bottleneck; the tracker should treat it as conditional until the RG-grade inputs are provided |

### Subclaim decompositions (actionable checklists for the three continuum/NRC spine items)

These checklists are meant to be *worked*: each checkbox is a concrete subclaim that should become either (i) a proved lemma/proposition in `Yang-Mills.tex`, or (ii) an explicitly cited external theorem with hypotheses matched and constants/uniformities tracked.

#### `thm:uei-fixed-region` (YM-0178) — UEI/tightness on fixed regions

- [x] **Normalize the quantity being controlled (confirmed)**: in `Yang-Mills.tex` both `thm:uei-fixed-region` and `thm:U1-lsi-uei` use the **standard Wilson normalization**
  \(S_R:=\sum_{p\subset R}\phi(U_p)\) (no extra \(a^4\) prefactor; \(\phi(U_p)\) itself has an \(a^4\) leading term in the small-field expansion). The Gibbs weight is \(e^{-\beta S_R}\).
  **Notation collision to fix**: elsewhere the manuscript also writes \(e^{-S_R(\cdot)}\) where \(S_R\) already *includes* \(\beta\) (see e.g. `prop:interface-density-ball-avg` remark “\(S_R\) carries an explicit factor \(\beta\)”). We should rename one of these to avoid silently swapping conventions.
- [ ] **Tree-gauge reduction (STD)**: gauge-fix on a spanning tree in \(R\), identify the chord variables, and write the induced finite-dimensional Gibbs density with a uniform interaction degree bound \(d_0(R)\); check dependence on exterior boundary conditions.
- [ ] **U1-A (tree gauge reduction; labeled target)**: `lem:U1-A-tree-gauge`.
- [ ] **Uniform LSI on the chord Gibbs measure (RG)**: justify a log–Sobolev constant \(\rho_R\) that is uniform in volume/boundary and compatible with the continuum regime (typically along \(\beta(a)\to\infty\)); address nonconvexity away from the identity (global patching/perturbation on compact groups).
- [ ] **U1-E (LSI/concentration; labeled target)**: `lem:U1-E-lsi-chords`.
- [ ] **Gradient/Lipschitz bound for the chosen local observable (STD/LEAP check)**: prove the bound on \(\|\nabla S_R\|^2\) used in Herbst, and verify it does not hide an \(a^{-k}\) blowup from the number of plaquettes/links in \(R\).
- [ ] **U1-D (gradient/Lipschitz from small field; labeled target)**: `lem:U1-D-lipschitz` (designed to be reduced to U1-B).
- [ ] **Herbst \(\Rightarrow\) Laplace bound (STD)**: run the Herbst argument with explicit constants, choose \(\eta_R\) independent of \(a,L\), and record exactly what dependence on \(\beta_{\min}\) (or a scaling schedule) remains.
- [x] **Uniform control of \(\mathbb E S_R\) (RG/LEAP)**: made explicit as a named RG-grade assumption in `Yang-Mills.tex` (`assump:uei-mean`, also labeled `lem:U1-C-mean`), so the centering-removal step is no longer a hidden divergence. This mean bound is **optional for tightness** if the Track-J smoothing/universality closure is used; it is only needed for the stronger uncentered action-moment bound \(\mathbb E e^{\eta S_R}\).
- [ ] **U1-B (small-field concentration; core labeled target)**: `lem:U1-B-smallfield` (intended to imply U1-C and U1-D, and to feed U1-E via standard compact-manifold arguments once the measure concentrates near $\mathbf 1$).
- [ ] **Track J (creative bypass; labeled targets)**:
  - [ ] **U1-J1 (heat-smoothing ⇒ dimension-free LSI/Herbst)**: `lem:U1-J1-smoothed-lsi` (now reduced to a named single-site input `lem:heatkernel-lsi-compactG` + tensorization/entropy chain rule; remaining work is to make the citation fully theorem-number-grade and check any hidden uniformities)
  - [x] **U1-J2 (smoothing-limit commutation / universality)**: `lem:U1-J2-universality` (proved in TeX for bounded continuous cylinder observables via \( \mathbb E_{\mu^{(t)}}[F]=\mathbb E_{\mu}[P_tF]\) and \(\|P_tF-F\|_\infty\to 0\))
- [ ] **Boundary-condition robustness (STD)**: show the constants do not depend on the exterior configuration outside \(R\).

**Audit notes (2025-12-21; decision point).**
- **Tree gauge step**: the reduction to a finite-dimensional chord Gibbs law is standard, but the scaling in the current TeX was inconsistent: if \(R\subset\BR^4\) is a fixed physical region, then the number of chord/link variables grows like \(m(R,a)=O(a^{-4})\) (not \(O(a^{-3})\)). This was corrected in `Yang-Mills.tex`.
- **Gradient/Lipschitz step**: as written, the claimed global bound \(\|\nabla S_R\|^2\lesssim a^4\) is only plausible under a **small-field/weak-coupling regime** where plaquette holonomies stay within \(O(a^2)\) of \(\mathbf 1\), so \(\|\nabla\phi(U_p)\|=O(a^2)\). Without such control, the trivial bound is \(\|\nabla S_R\|^2\lesssim m(R,a)\asymp a^{-4}\), which is incompatible with the later “uniform in \(a\)” Herbst/UEI conclusions at fixed \(\beta\).
- **Mean bound step**: the step “\(\sup_a \BE S_R<\infty\) because \(S_R\) is a Riemann sum” likewise implicitly assumes weak-coupling scaling; at fixed \(\beta\) independent of \(a\), \(|\mathcal P_R|\asymp a^{-4}\) and one expects \(\BE S_R\) to grow proportionally, so \(\sup_a \BE e^{\eta S_R}\) cannot stay bounded for any fixed \(\eta>0\).
- **Raw small-field warning**: even fairly strong *fixed-stencil* small-field bounds (e.g. `TS:ball_weight` in TeX gives $\mathbb P(\mathcal B_{r_0}^c)\le C_U a^2$ on a finite update stencil under a weak-coupling schedule) are far too weak to control an extensive fixed-region sum over $|\mathcal P_R|\asymp a^{-4}$ plaquettes: $a^2\cdot a^{-4}$ still diverges. Any viable raw U1-B route must therefore deliver substantially stronger tails/large-deviation control on fixed regions.
- **Decision**: to be internally consistent, the UEI/tightness package must be **tied to a weak-coupling scaling window** \(\beta=\beta(a)\to\infty\) (and in practice requires RG-grade small-field control). Treat the “β-uniform for all \(\beta\ge\beta_{\min}\)” phrasing as not credible without major new input.

#### `thm:os1-unconditional` (YM-0187) — OS1 on fixed regions (Euclidean invariance)

- [x] **Lock the route + dependency graph (meta)**: Primary = calibrator route (`prop:hk-calibrators-constructed` ⇒ `thm:os1-calibrator-route` ⇒ `thm:os1-unconditional`), Optional cross-check = commutator route (`lem:local-commutator-Oa2` ⇒ `prop:resolvent-from-commutator` ⇒ `thm:emergent-sym`). Note: the commutator route invokes `TS:sandwich_main` (explicitly labeled an outline in TeX), so it is kept as a cross-check rather than the mainline OS1 closure. See `OS1_OPERATIONAL_PLAN.md` for a closure-target decomposition.
- [ ] **Define the lattice action of rigid motions \(U_a(G)\) (STD)**: specify how \(G\in E(4)\) acts on lattice cylinders/loops and prove \(U_a(G)\) is unitary on the OS/GNS quotient and compatible with embeddings.
- [ ] **Prove `TS:sandwich_main` in the uniform form actually used (RG/LEAP)**: a Strang/sandwich approximation for \(e^{-tH_{a,L}}\) with an \(O(a^2 t)\) remainder on local cores, uniform in \(L\), boundary, and \(t\in[0,t_0]\).
- [ ] **Prove `DEC:plaquette-F2` with explicit \(O(a^2)\) control (hard STD)**: finite-region Taylor control needed to compare magnetic terms under small rotations/relabellings (and to justify the “finite-stencil” estimates invoked in the commutator proof).
- [ ] **Establish `lem:local-commutator-Oa2` (RG)**: show \(\|[U_a(G),e^{-tH_{a,L}}]\|\le C(R,G)\,a^2 t\) on the time-zero local subspace, uniformly in \(L\) and boundary.
- [ ] **Semigroup commutators \(\Rightarrow\) resolvent conjugation (STD)**: check Laplace-transform bounds and the \(t\in[0,t_0]\) split in `prop:resolvent-from-commutator` with explicit constants.
- [ ] **Limit passage \(\Rightarrow\) OS1 for Schwinger functions (STD)**: verify the convergence mode is strong enough and that UEI/equicontinuity closes any density gaps so the invariance extends beyond a dense cylinder class.

#### `thm:U2-nrc-unique` (YM-0294) — operator-norm NRC + uniqueness of the continuum generator

- [ ] **Embeddings / partial isometries (STD)**: prove \(I_{a,L}\) are genuine isometries on local OS/GNS quotients and intertwine time translations on cylinders (see `lem:U2-embeddings`).
- [ ] **Common core + defect operator (STD)**: construct a common dense core \(\mathcal D^{\rm loc}\) and make \(D_{a,L}=H I_{a,L}-I_{a,L}H_{a,L}\) well-defined with the required defect identity (see `lem:U2-defect-core`).
- [ ] **Graph-defect estimate (RG)**: prove \(\|D_{a,L}(H_{a,L}+1)^{-1/2}\|\le C a\) uniformly in \(L\) (cited in TeX to `thm:quant-calibrated-af-free-nrc` (D)).
- [ ] **Low-energy projector control (RG)**: prove \(\|(I-P_{a,L})E_H([0,\Lambda])\|\le C_\Lambda a\) uniformly in \(L\) (TeX cites `lem:low-energy-proj`), including where the continuum spectral projector \(E_H\) comes from before uniqueness is established.
- [ ] **Uniform resolvent–graph bounds (STD)**: establish the bounds \(\|(H-z_0)^{-1}(H+1)^{1/2}\|\) and \(\|(H_{a,L}-z_0)^{-1}(H_{a,L}+1)^{1/2}\|\) independent of \((a,L)\) for some nonreal \(z_0\).
- [ ] **One-point resolvent estimate at \(z_0\) (STD)**: prove `prop:one-point-resolvent` with constants and \(\Lambda\) bookkeeping.
- [ ] **Bootstrap from \(z_0\) to compact \(K\subset\mathbb C\setminus\mathbb R\) (STD)**: execute the resolvent-identity/uniform-boundedness argument to get \(\sup_{z\in K}\|R(z)-I_{a,L}R_{a,L}(z)I_{a,L}^*\|\to 0\) and conclude “no subsequences”.

## Status + confidence rubric

- **Status codes**:
  - **S0**: unreviewed
  - **S1**: statement understood + dependencies identified
  - **S2**: proof sketched (major steps, but details missing)
  - **S3**: proof written in full detail (all estimates/quantifiers checked)
  - **S4**: proof audited end-to-end (no hidden assumptions; constants tracked)
  - **SX**: conditional/blocked/false (must be explained in the ledger below)
- **Confidence codes**:
  - **C0**: unknown
  - **C1**: plausible but unverified
  - **C2**: likely (core idea clear; details probably standard)
  - **C3**: confident (checked the hard parts)
  - **C4**: rock-solid (would bet on it; ready to formalize)

## How we will work (repeat every session)

- **Pick a target claim** from the inventory (prefer the main chain).
- **Open the TeX block** using the recorded line range and copy the statement into a “proof worksheet” (template below).
- **List dependencies** (labels + any “standard facts”). Every “standard fact” gets either a citation or becomes a new tracked lemma.
- **Write a fully detailed proof**: quantify constants, track uniformities (in $a,L,\beta$), and mark any step that uses an external theorem.
- **Update** this tracker: bump S*/C* and add items to the ledger if anything is conditional/blocked.

## Main-chain claim map (start here)

This is the minimal “spine” to reach `thm:main-af-free`. We’ll check a box when the claim has at least **S3** (full detailed writeup) and bump to **S4** once constants/uniformities are audited end-to-end.

- **OS positivity / transfer (finite lattice)**:
  - [x] `thm:os` (YM-0001)
  - [x] `lem:char-pd` (YM-0129)
  - [x] `prop:psd-crossing-gram` (YM-0130)
  - [x] `lem:os-gns-transfer` (YM-0131)
- **Interface kernel → contraction → lattice gap (fixed slabs)**:
  - [x] `cor:hk-convex-split-explicit` *(audited; TeX constant fixed on 2025-12-20)*
  - [ ] `thm:ucis` *(UCIS closure target: physically-scaled \(M(a)=\lceil T_{\rm phys}/a\rceil\) step smoothing on the coarse interface; decomposed into `lem:ucis-A-*` … `lem:ucis-E-*` in `Yang-Mills.tex`; **blocked** at `lem:ucis-C-cell-ball`, see ledger #20)*
  - [x] `thm:ucis-sw` *(**active closure (scaling-window)**: propagated downstream; proof now explicitly invokes `thm:staple-window`, `lem:single-link-refresh`/`lem:g-one-link-refresh`, `lem:scaled-ball-to-hk`, and `lem:ballwalk-diffusive`; see ledger #21–#23)*
  - [ ] `lem:beta-L-independent-minorization` *(legacy unconditional one-step path; no longer used by the active scaling-window chain)*
  - [ ] `prop:sandwich`
  - [x] `prop:int-to-transfer` (YM-0040)
  - [x] `thm:uniform-odd-contraction` (YM-0043)
  - [ ] `thm:gap` / `thm:thermo` (infinite-volume step)
- **Continuum existence + OS axioms (AF-free path)**:
  - [ ] `thm:uei-fixed-region` (UEI/tightness on fixed regions)
  - [x] `prop:os0os2-closure` (OS0/OS2 pass to limits)
  - [ ] `thm:os1-unconditional` (OS1 on fixed regions)
- **AF-free NRC + gap persistence**:
  - [ ] `thm:U2-nrc-unique` (operator-norm NRC + uniqueness)
  - [x] `thm:gap-persist-cont` (gap persistence to continuum)
- **OS → Wightman export**:
  - [ ] `thm:os-to-wightman` (and global variants)
- **Main theorem**:
  - [ ] `thm:main-af-free`

### Unconditional checklist (active route; **no axioms**)

This is the **minimal set of structures/lemmas** that must exist *with proofs in this repo* (or standard, fully cited theorems with hypotheses checked) to claim an **unconditional Clay-level** result via the active route.

Each checkbox below should end up either:
- **DONE**: proof in `Yang-Mills.tex` at **S3+** with explicit uniformities, or
- **BLOCKED**: moved to the ledger with a precise missing subclaim (no hand-waving).

- **L0. Finite-lattice OS framework (finite \(a,L\))**
  - [ ] **(Already largely done)**: existence of the Wilson measure + OS reflection positivity + transfer operator construction (`thm:os`, `lem:os-gns-transfer` and friends) with clean normalization of \(H_{L,a}\) and \(T=e^{-aH}\).

- **L1. β- and \(L\)-uniform *physical* slab gap (fixed physical thickness)**
  - [ ] **β-uniform interface minorization / smoothing**: a genuine β-uniform lower bound of the interface kernel by a smoothing reference (heat kernel / strong-Feller minorization) on a **fixed-dimension** coarse interface (`thm:ucis`, `lem:beta-L-independent-minorization`, `prop:sandwich`).
  - [ ] **Odd-cone contraction with correct scaling**: prove that the induced contraction yields a **physical** gap floor \(\gamma_*>0\) that does not degenerate as \(a\downarrow 0\) along the scaling schedule (this is where “per tick” vs “per physical time” constants must be audited).

**Note (current best active closure for L1).** We are currently pursuing the scaling-window interface-smoothing closure `thm:ucis-sw` under `eq:ucis-sw-window` (as wired into `Yang-Mills.tex`), which supplies a fixed-physical-time contraction with explicit bookkeeping (`cor:ucis-sw-L2-contraction`, `thm:ucis-sw-odd-subspace`). Full β-uniform UCIS (`thm:ucis`) remains blocked at `lem:ucis-C-cell-ball` (ledger #20).

- **L2. Van Hove / thermodynamic limit at fixed spacing \(a\) with uniformity**
  - [ ] **Infinite-volume (or van Hove) stability**: existence/consistency of the \(L\to\infty\) limit (in the sense used later) and preservation of the slab gap constants (`thm:thermo` / `thm:gap` cluster).

- **C0. Continuum tightness/existence on fixed regions along weak-coupling scaling**
  - [ ] **Local UEI/LSI in the *actual* weak-coupling regime**: a theorem of the form “for each fixed \(R\), along \(\beta=\beta(a)\to\infty\) we have uniform integrability / tightness / equicontinuity on \(R\)” with constants independent of \(a,L\) (`thm:uei-fixed-region` / `thm:U1-lsi-uei` and supporting lemmas).  
    - **Note**: this is an RG/constructive-QFT grade input in 4D; if it is not proved, the route is blocked.
  - [ ] **OS0/OS2 closure under limits**: once tightness is real, pass OS0 + OS2 to the limit in a precise topology (`prop:os0os2-closure`, `lem:os2-limit`, `lem:os0-explicit-constants`).
  - [ ] **OS1 (Euclidean invariance)**: restore full \(E(4)\) invariance in the limit (commutator route or calibrator route) with all uniformities checked (`thm:os1-unconditional` and its true dependencies).

- **C1. Operator convergence / uniqueness of the continuum generator (AF-free NRC package)**
  - [ ] **Operator-norm NRC on fixed regions**: prove the quantitative resolvent convergence needed to transport the gap (`thm:nrc-operator-norm` plus its concrete YM verification inputs).
  - [ ] **Uniqueness / no subsequences**: make `thm:U2-nrc-unique` unconditional by proving its “graph-defect \(O(a)\)” + “low-energy projector control” hypotheses in the YM setting.

- **C2. Continuum mass gap + global OS0–OS5**
  - [ ] **Gap persistence**: standard once NRC holds (`thm:gap-persist-cont`).
  - [ ] **Global continuum measure / OS0–OS5 on \(\mathbb R^4\)**: construct the global theory and verify OS0–OS5 (this is the true Clay “existence” half) (`thm:global-OS` / `thm:global-OS0-5` cluster).

- **C3. OS → Wightman export (standard once C2 holds)**
  - [ ] **OS reconstruction + Minkowski mass gap**: `thm:os-to-wightman` (+ global variants) with hypotheses matched to what we actually proved.

### Reusable prompt (copy/paste; **Yang–Mills only, not RH**)

```text
You are my proof-audit coding agent working in /Users/jonathanwashburn/Projects/riemann-geometry-rs.

We are working ONLY on the Yang–Mills existence + mass gap proof audit:
- Primary files: Yang-Mills.tex, YANG_MILLS_PROOF_TRACK.md
- Do NOT work on Riemann hypothesis, BSD, or any other manuscript in this repo.

Task:
Pick the next unchecked item from the “Unconditional checklist (active route; no axioms)” section in YANG_MILLS_PROOF_TRACK.md, and drive it to one of two outcomes:
  (A) DONE: a fully detailed, referee-grade proof is written into Yang-Mills.tex (S3 or better), with all constants/uniformities (in a, L, β, region size, group) checked and no hidden assumptions; OR
  (B) BLOCKED: you prove it cannot currently be completed from prior material, and you add a blocker ledger entry explaining the exact missing lemma/estimate and why it is genuinely needed.

Method (repeat until complete):
1) Locate the target claim in Yang-Mills.tex by its \\label{...}. Copy its statement into a “proof worksheet” block in the tracker (or update the existing one).
2) Normalize notation (especially anything involving β(a), a→0 scaling, and “physical” vs “per-tick” units).
3) List dependencies:
   - Internal: exact lemma/theorem labels.
   - External: exact citations with theorem numbers + hypotheses; if a “standard fact” is used, either cite it precisely or create a new tracked lemma.
4) Write the proof in full detail in Yang-Mills.tex:
   - No “it is clear”; quantify constants; state uniformity domains.
   - If you introduce any new lemma, add a \\label{...} and register it in the tracker inventory/ledger as needed.
5) Update YANG_MILLS_PROOF_TRACK.md:
   - Set Status/Confidence (S*/C*) for the target claim.
   - Check off the corresponding checklist checkbox if DONE.
   - If BLOCKED, add/upgrade a ledger entry with a concrete missing-subclaim description.
6) Run lints on edited files and fix any issues you introduced.

Output:
Summarize what changed (files + key proof facts), what remains open, and propose the next target checkbox you will tackle next.
```

## Previously unlabeled proof-relevant claims (now labeled)

All of the items below were unlabeled in `Yang-Mills.tex` during the initial inventory and were **fixed on 2025-12-20** by adding `\label{...}` tags. The table is kept for provenance/mapping.

| ID | Type | TeX lines | New label | Old placeholder |
|---:|:-----|:----------|:----------|:----------------|
| YM-0058 | corollary | 1374-1380 | `cor:best-of-two-gap` | `unlabeled@L1374` |
| YM-0172 | theorem | 3317-3326 | `thm:c1-consolidated` | `unlabeled@L3317` |
| YM-0173 | theorem | 3336-3348 | `thm:preview-continuum-existence` | `unlabeled@L3336` |
| YM-0239 | theorem | 4570-4581 | `thm:dobrusin-spectrum-finite` | `unlabeled@L4570` |
| YM-0258 | lemma | 5172-5189 | `lem:os0-explicit-constants` | `unlabeled@L5172` |
| YM-0259 | lemma | 5202-5208 | `lem:os2-limit` | `unlabeled@L5202` |
| YM-0260 | lemma | 5239-5244 | `lem:os3-limit` | `unlabeled@L5239` |
| YM-0261 | lemma | 5257-5262 | `lem:os5-limit` | `unlabeled@L5257` |
| YM-0262 | lemma | 5294-5300 | `lem:semigroup-defect` | `unlabeled@L5294` |
| YM-0263 | lemma | 5317-5319 | `lem:compact-calibrator` | `unlabeled@L5317` |
| YM-0264 | theorem | 5330-5336 | `thm:nrc-exhaustion` | `unlabeled@L5330` |
| YM-0265 | theorem | 5338-5351 | `thm:nrc-gap` | `unlabeled@L5338` |
| YM-0267 | theorem | 5406-5411 | `thm:af-schedule-gap` | `unlabeled@L5406` |
| YM-0268 | theorem | 5428-5434 | `thm:continuum-area-perimeter` | `unlabeled@L5428` |
| YM-0272 | lemma | 5552-5554 | `lem:lattice-brst-ward` | `unlabeled@L5552` |

## Conditional / blocked / false ledger

| ID | Label | Issue type | Depends on / blocked by | Notes / plan |
|---:|:------|:----------|:------------------------|:-------------|
| 1 | `assump:AF-Mosco` | optional cross-check (not main chain) | — | Explicitly marked “not used in main chain”. Keep separate until/unless we decide to pursue the Mosco route. |
| 2 | `TS:sandwich_main` | outline-only (used by OS1 commutator cross-check; optional overall) | `lem:local-commutator-Oa2` (OS1 commutator route) | Although not used for the interface/UCIS gap chain, `TS:sandwich_main` is invoked in the commutator route to OS1 (`lem:local-commutator-Oa2`). Since the calibrator route is the current mainline OS1 closure, this dependency is optional overall; keep it as a cross-check until `TS:sandwich_main` is fully proved (not just outlined). |
| 3 | `thm:AL-gap` | conditional (area law + tube) | area law + tube hypotheses | Optional route; not part of the unconditional chain. |
| 4 | `cor:scaled-continuum-gap` | Mosco/AF cross-check (not main chain) | Mosco/AF route | Explicitly marked “not used in main chain”. |
| 5 | `thm:os-to-wightman-global` | conditional-on-OS0–OS5 | OS0–OS5 | Should become unconditional once OS0–OS5 are proved in the global continuum construction. |
| 6 | `thm:wightman-axioms` | conditional-on-OS0–OS5 | OS0–OS5 | Same as above; confirm no extra hidden hypotheses. |
| 7 | `thm:global-minkowski-gap` | conditional | Wightman export + Euclidean gap | Verify hypotheses match the unconditional chain and constants propagate as claimed. |
| 8 | `(multiple)` | missing labels (fixed) | — | Added labels for all proof-relevant unlabeled theorem/lemma/corollary blocks (2025-12-20). |
| 9 | `prop:psd-crossing-gram` | citation bug (fixed) | — | Patched `Yang-Mills.tex` to cite `lem:char-pd` in Step 4 (2025-12-20). |
| 10 | `cor:hk-convex-split-explicit` | constant bug (fixed) | — | Patched `Yang-Mills.tex` to use \(1-\\theta_*(1-e^{-\\lambda_1 t_0})=(1-\\theta_*)+\\theta_*e^{-\\lambda_1 t_0}\) (2025-12-20). |
| 11 | `prop:doeblin-full` | uniformity gap (fixed) | — | Patched `Yang-Mills.tex` so `prop:doeblin-full` is derived from `lem:beta-L-independent-minorization` instead of relying on `lem:refresh-prob` (2025-12-20). |
| 12 | `lem:coarse-refresh` / `lem:coarse-hk-domination` / `prop:coarse-doeblin` | partially proved (in-text route) | `lem:one-link-ball-minorization`, `lem:ball-conv-lower`, `lem:cell-disjoint-links`, `lem:plaquette-factorization` (+ bounded-β fallback via `prop:doeblin-interface`) | Geometry/factorization is now formal in TeX (`lem:cell-disjoint-links`, `lem:plaquette-factorization`). The analytic step “one-link refresh ⇒ uniform small-ball *measure* minorization” is now explicit via `lem:one-link-ball-minorization`, but its constant is β-explicit (decays like `e^{-2βN}`), so β-uniformity still needs a stronger refresh mechanism. |
| 13 | `lem:beta-L-independent-minorization` | mostly reduced; residual geometry gap | `prop:coarse-doeblin` (and its inputs) | The TeX statement/proof is now a clean corollary of `prop:coarse-doeblin`. The remaining nontrivial piece is the geometric/factorization part inside `lem:coarse-refresh` (selecting plaquette-disjoint links per coarse cell and justifying exact product factorization across cells on the slab). |
| 14 | `cor:microcausality` | duplicate label (fixed) | — | `Yang-Mills.tex` had two `\label{cor:microcausality}` definitions; renamed the later one to `cor:microcausality-smeared` (2025-12-20). |
| 15 | `lem:compact-small-ball` | missing lemma (fixed) | — | Added `lem:compact-small-ball` to `Yang-Mills.tex` Appendix `app:beta-indep-minorization` (2025-12-20). |
| 16 | `lem:coarse-density` / `cor:odd-to-meanzero` | fixed (rewritten) | — | `lem:coarse-density` was rewritten as the standard martingale/conditional-expectation density statement as $\varepsilon\downarrow 0$ (under an explicit nesting + generation hypothesis). `cor:odd-to-meanzero` was rewritten as a pointer/restatement of `thm:eight-tick-uniform`, so it no longer depends on the coarse-density lemma. |
| 17 | `prop:sandwich` | external input (proof gap removed; still conditional) | compact-group smoothing/minorization theorems | The original TeX proof used a “drop the middle factor” step that does not follow without additional assumptions on the unsmoothed kernel. It is now explicitly recorded as a proof sketch / external input relying on standard minorization results for strong-Feller kernels on compact groups after smoothing (citations included). |
| 18 | `thm:uei-fixed-region` / `thm:U1-lsi-uei` | RG-grade U1 package (open; now split into two explicit closure routes) | weak-coupling / continuum control (RG) | **Normalization confirmed**: in TeX, \(S_R:=\sum_{p\subset R}\phi(U_p)\) (no extra \(a^4\); weight \(e^{-\beta S_R}\)). `thm:uei-fixed-region` is now explicitly formulated with two closure routes: (A) raw small-field route (requires `lem:U1-B-smallfield` and the mean bound `assump:uei-mean` to get the strong action-moment bound), and (J) Track-J smoothing/universality (`lem:U1-J1-smoothed-lsi`, `lem:U1-J2-universality`) which is designed to deliver fixed-region tightness without requiring the raw mean bound. Remaining open pieces include: a genuine fixed-region large-deviation/small-field theorem for route A, or a fully cited/checked dimension-free single-site heat-kernel LSI plus any extra universality needed beyond bounded cylinders for route J. See `U1_OPERATIONAL_PLAN.md` for the closure-target decomposition. |
| 19 | `thm:ucis` / `lem:ucis-*` | new closure target (unproved) | `lem:ucis-C-cell-ball` (+ `lem:ucis-A-*`, `lem:ucis-B-*`, `lem:ucis-D-*`, `lem:ucis-E-*`) | Added UCIS theorem + lemma stubs to `Yang-Mills.tex` (2025-12-23) as an operational replacement target for the coarse-refresh/minorization bottleneck (ledger #12–#13). UCIS-A and UCIS-E are now written as concrete reductions to existing coarse-interface geometry and compact-group smoothing (`lem:coarse-interface-construction`, `lem:cell-disjoint-links`, `lem:plaquette-factorization`, `lem:ball-conv-lower`). UCIS-D is a clean factorization reduction once UCIS-C holds (now phrased in increment coordinates consistent with `P_{t_0}(U,·)`). We also added an unconditional one-link lemma giving **β-uniform mass** in a fixed-radius ball around the polar maximizer (`lem:one-link-ball-maximizer-unif`), but this does **not** by itself yield a β-uniform **domination by the uniform ball law** at fixed radius. The main missing analytic step remains a truly β-uniform single-cell *measure* minorization / refresh mechanism (`lem:ucis-C-cell-ball`), likely requiring an additional cell-level smoothing/pulse or a physically scaled multi-step argument. |
| 20 | `lem:ucis-C-cell-ball` | no-go (partial) + refined requirement | `lem:no-unifball-doeblin-fixed-radius` | Added `lem:no-unifball-doeblin-fixed-radius` showing that fixed-radius β-uniform Doeblin domination by the **uniform ball law** fails even for the one-link matrix-Fisher conditionals. Therefore, any viable UCIS-C proof must avoid “fixed-radius one-link Doeblin” and instead supply a genuinely new **cell-level smoothing/pulse** or **physically scaled multi-step** mechanism that upgrades β-uniform *mass near maximizers* into a β-uniform *measure* minorization for the coarse increment. |
| 21 | `thm:ucis-sw` | conditional (scaling-window UCIS; **active closure**) | `eq:ucis-sw-window` + `thm:staple-window` + `lem:single-link-refresh`/`lem:g-one-link-refresh` + `lem:scaled-ball-to-hk` | `Yang-Mills.tex` now contains a full proof of UCIS\(_{\rm SW}\) (not just a sketch) and downstream callsites have been patched to use UCIS\(_{\rm SW}\) under the scaling window as the active interface-smoothing closure. Bookkeeping corollaries `cor:ucis-sw-L2-contraction` and the parity-odd contraction theorems `cor:ucis-sw-odd-contraction` / `thm:ucis-sw-odd-subspace` are now wired into the “interface → odd → slab gap” narrative. |
| 22 | `lem:scaled-ball-to-hk` | proved in-text (Track B smoothing step closed) | `lem:ballwalk-diffusive` + Chernoff/Hoeffding + `lem:central-mixture-binomial` | Implemented in `Yang-Mills.tex` using a central-mixture/binomial decomposition plus the ball-walk diffusive Haar minorization and a binomial tail bound; yields fixed-time heat-kernel minorization after $n\asymp\beta$ steps with constants uniform in $\beta$. |
| 23 | `lem:ballwalk-diffusive` | proved in-text via precise citation + hypothesis check | Hebisch--Saloff-Coste (1993), Thm 5.1 (lower bound (15)) | `Yang-Mills.tex` contains a repo-facing proof: specialize \cite[Thm 5.1]{HebischSaloffCoste1993} to compact $G$ (polynomial growth order $D=0$) and relate the word-metric diameter to $r^{-1}$ to obtain a global lower bound $\nu_r^{(*n)}\ge c_{\rm mix}\pi$ for $n\gtrsim r^{-2}$. |

## Proof worksheet template (copy/paste per claim)

```text
Claim ID: YM-____
Label: ... (or “unlabeled @ L____”)
Type: theorem/lemma/proposition/corollary
Location: Yang-Mills.tex:L____-L____
Used-by: (list later claims that rely on this)

Statement (verbatim / normalized):
  ...

Dependencies:
  - [ ] Internal: Lem/Prop/Thm ...
  - [ ] External: (book/paper result) ...
  - [ ] Definitions: ...

Proof plan (high level):
  1) ...

Detailed proof:
  Step 0 (setup/notation): ...
  Step 1 (...): ...

Constant/uniformity checks:
  - [ ] Which parameters are uniform? (a, L, beta, region R_*, group G, etc.)
  - [ ] Any hidden compactness/regularity assumptions?
  - [ ] Any “choose epsilon small” that impacts later steps?

Status update: S?  Confidence: C?
```

## Proof writeups (audited)

### YM-0129 — Lemma `lem:char-pd` (S3/C4)

- **Location**: `Yang-Mills.tex:L2623-L2635`
- **Statement**: For any compact group $G$ and any unitary irreducible representation $R$, the character $\chi_R(g)=\mathrm{Tr}\,R(g)$ is positive definite, i.e. for any $g_1,\dots,g_m\in G$ and $c\in\mathbb C^m$,
  \[
    \sum_{i,j=1}^m \overline{c_i}\,c_j\,\chi_R(g_i^{-1}g_j)\ \ge\ 0.
  \]

**Proof (fully explicit).**
Let $\mathcal V$ be the (finite-dimensional) Hilbert space of $R$ and write $\langle \cdot,\cdot\rangle_{\mathcal V}$ for its inner product. Since $R$ is unitary, $R(g)^\* = R(g^{-1})$.

Fix $g_1,\dots,g_m\in G$ and $c_1,\dots,c_m\in\mathbb C$. Consider the operator
\[
  A\ :=\ \sum_{j=1}^m c_j\,R(g_j)\ \in\ \mathrm{End}(\mathcal V).
\]
Compute its Hilbert–Schmidt norm:
\[
  \|A\|_{\mathrm{HS}}^2 \;=\; \mathrm{Tr}(A^\*A).
\]
Now expand:
\[
  A^\*A \;=\; \Big(\sum_{i=1}^m \overline{c_i}\,R(g_i)^\*\Big)\Big(\sum_{j=1}^m c_j\,R(g_j)\Big)
  \;=\; \sum_{i,j=1}^m \overline{c_i}\,c_j\,R(g_i)^\* R(g_j)
  \;=\; \sum_{i,j=1}^m \overline{c_i}\,c_j\,R(g_i^{-1}g_j).
\]
Taking traces and using linearity:
\[
  \mathrm{Tr}(A^\*A) \;=\; \sum_{i,j=1}^m \overline{c_i}\,c_j\,\mathrm{Tr}\,R(g_i^{-1}g_j)
  \;=\; \sum_{i,j=1}^m \overline{c_i}\,c_j\,\chi_R(g_i^{-1}g_j).
\]
But $\mathrm{Tr}(A^\*A)=\|A\|_{\mathrm{HS}}^2\ge 0$. This is exactly the desired inequality. ∎

**Notes.**
- This argument does not use irreducibility; it works for any finite-dimensional unitary representation (irreducible is only used elsewhere for character expansions).

### YM-0130 — Proposition `prop:psd-crossing-gram` (S3/C3)

- **Location**: `Yang-Mills.tex:L2637-L2671`
- **Statement (normalized)**: Let $\mu_\beta$ be the Wilson lattice gauge measure on a finite 4D torus with gauge group $\mathrm{SU}(N)$ and Wilson action. Fix an Osterwalder–Seiler link reflection $\theta$ across a time-reflection hyperplane, and let $\mathcal A_+$ be the *-algebra of cylinder observables supported in the positive half. Define the OS sesquilinear form
  \[
    \langle F,G\rangle_{\mathrm{OS}}\ :=\ \int \overline{F(U)}\,(\theta G)(U)\,d\mu_\beta(U).
  \]
  Then for any finite family $\{F_i\}\subset\mathcal A_+$, the Gram matrix $M_{ij}:=\langle F_i,\theta F_j\rangle_{\mathrm{OS}}$ is positive semidefinite.

**Proof (expanded with the missing justification fixed).**
It suffices to show that for any complex scalars $c_1,\dots,c_n$ and $F:=\sum_i c_i F_i\in\mathcal A_+$ one has
\[
  \langle F,\theta F\rangle_{\mathrm{OS}}\ \ge\ 0,
\]
since $\sum_{i,j}\overline{c_i}c_j M_{ij}=\langle F,\theta F\rangle_{\mathrm{OS}}$.

**Step 0 (the only group-theory input).**  
For each representation label $R$, the kernel $K_R(g,h):=\chi_R(g^{-1}h)$ is PSD in the sense that for any $g_1,\dots,g_m$ the matrix $[\,\chi_R(g_i^{-1}g_j)\,]_{i,j}$ is PSD. This is exactly Lemma `lem:char-pd` (YM-0129).

**Step 1 (crossing plaquette weight has a nonnegative character expansion).**  
For a crossing plaquette variable $V\in \mathrm{SU}(N)$ the Wilson plaquette weight is the class function
\[
  w_\beta(V)\ :=\ \exp\Big(\tfrac{\beta}{N}\,\mathrm{Re\,Tr}\,V\Big).
\]
We need the standard fact that it admits a character expansion
\[
  w_\beta(V)\ =\ \sum_{R} c_R(\beta)\,\chi_R(V)\quad\text{with}\quad c_R(\beta)\ge 0.
  \tag{$\*$}
\]
The TeX proof sketches this and asserts $c_R(\beta)\ge 0$ “from positivity + Schur orthogonality”; that implication is false in general. The correct justification is:

- The fundamental character $\chi_{\mathrm{fund}}(V)=\mathrm{Tr}(V)$ is positive definite by YM-0129, hence so is $\overline{\chi_{\mathrm{fund}}(V)}=\chi_{\mathrm{fund}}(V^{-1})$.
- If $\varphi,\psi$ are positive definite functions on a group, then $\varphi\psi$ is positive definite (Schur product theorem applied to the matrices $[\varphi(g_i^{-1}g_j)]$ and $[\psi(g_i^{-1}g_j)]$).
- If $\varphi$ is bounded and positive definite, then $\varphi^n$ is positive definite for all $n$, and the uniformly convergent series $\sum_{n\ge 0} a_n \varphi^n$ with $a_n\ge 0$ is positive definite.

Since $\mathrm{Re\,Tr}\,V=\tfrac12(\chi_{\mathrm{fund}}(V)+\chi_{\mathrm{fund}}(V^{-1}))$, we can write
\[
  w_\beta(V)=\exp\Big(\tfrac{\beta}{2N}\chi_{\mathrm{fund}}(V)\Big)\cdot \exp\Big(\tfrac{\beta}{2N}\chi_{\mathrm{fund}}(V^{-1})\Big),
\]
and each exponential is a positive-coefficient power series in a positive definite function, hence positive definite; the product is positive definite. Therefore $w_\beta$ is a continuous, conjugation-invariant, positive definite function on the compact group $\mathrm{SU}(N)$.

By the (compact-group) Bochner–Peter–Weyl theorem, a continuous central positive definite function has a Fourier/character expansion with nonnegative coefficients, giving $(\*)$ with $c_R(\beta)\ge 0$.

**Step 2 (Osterwalder–Seiler factorization across the reflection plane).**  
Decompose the Wilson action as
\[
  S_\beta(U)\ =\ S_\beta^{(+)}(U^{+})\ +\ S_\beta^{(-)}(U^{-})\ +\ S_\beta^{(\perp)}(U^{+},U^{-}),
\]
where $S_\beta^{(\pm)}$ are the sums over plaquettes entirely in the positive/negative half-spaces, and $S_\beta^{(\perp)}$ sums over plaquettes crossing the reflection hyperplane. With this decomposition and the product Haar measure $dU=dU^{+}\,dU^{-}$, we have
\[
  \langle F,\theta F\rangle_{\mathrm{OS}}
  \;=\;\frac{1}{Z_\beta}\int \overline{F(U^{+})}\,F(U^{-})\,
  e^{-S_\beta^{(+)}(U^{+})}\,e^{-S_\beta^{(-)}(U^{-})}\,e^{-S_\beta^{(\perp)}(U^{+},U^{-})}\,dU^{+}\,dU^{-},
\]
using that $(\theta F)(U)=F(U^{-})$ for $F\in\mathcal A_+$ by definition of the Osterwalder–Seiler link reflection.

Now expand each crossing plaquette weight inside $e^{-S_\beta^{(\perp)}}$ using $(\*)$. After distributing products, we obtain a finite (in finite volume) sum over representation assignments $\mathbf R$ to crossing plaquettes:
\[
  e^{-S_\beta^{(\perp)}(U^{+},U^{-})}
  \;=\;\sum_{\mathbf R} W_{\mathbf R}(\beta)\,\prod_{P\in \mathcal P_\perp}\chi_{R_P}\big(U_P(U^{+},U^{-})\big),
  \qquad W_{\mathbf R}(\beta):=\prod_{P\in\mathcal P_\perp}c_{R_P}(\beta)\ \ge\ 0.
\]
Crucially, the product over crossing plaquettes can be rewritten as a finite sum of tensor products of kernels of the form $\chi_R(g^{-1}h)$, where $g$ depends only on $U^{+}$ boundary variables and $h$ depends only on $U^{-}$ boundary variables (this is the standard “crossing kernel” re-expression in the Osterwalder–Seiler argument).

Therefore $\langle F,\theta F\rangle_{\mathrm{OS}}$ is a finite sum (with nonnegative weights $W_{\mathbf R}(\beta)$) of integrals of the form
\[
  \int \overline{F(U^{+})}\,F(U^{-})\,
  e^{-S_\beta^{(+)}(U^{+})}\,e^{-S_\beta^{(-)}(U^{-})}\,
  \prod_{\ell\in\text{cut}}\chi_{R_\ell}\big(g_\ell(U^{+})^{-1}h_\ell(U^{-})\big)\,dU^{+}\,dU^{-}.
  \tag{$\dagger$}
\]

**Step 3 (positivity of each representation term).**  
Fix one representation assignment $\mathbf R$. The kernel
\[
  K_{\mathbf R}(U^{+},U^{-})\ :=\ \prod_{\ell\in\text{cut}}\chi_{R_\ell}\big(g_\ell(U^{+})^{-1}h_\ell(U^{-})\big)
\]
is PSD as a kernel in $(U^{+},U^{-})$ because it is a finite product of PSD kernels of the form $\chi_R(g^{-1}h)$ (Step 0) and products preserve PSD (Schur product theorem).

Consequently, the integral $(\dagger)$ is a PSD pairing of $F$ against itself (one may view it as $\|\,\Pi_{\mathbf R}F\,\|^2$ for an explicit linear map $\Pi_{\mathbf R}$ obtained by inserting matrix elements and integrating over $U^{-}$). In particular it is $\ge 0$.

Since $\langle F,\theta F\rangle_{\mathrm{OS}}$ is a nonnegative linear combination of nonnegative terms, we conclude $\langle F,\theta F\rangle_{\mathrm{OS}}\ge 0$. This proves OS reflection positivity and hence $M\succeq 0$. ∎

**Notes / audit flags.**
- The TeX proof cites `thm:quant-calibrated-af-free-nrc` in Step 4 for character positivity; the correct internal citation is YM-0129 (`lem:char-pd`). This is recorded in the ledger as an editorial fix.
- This writeup is **S3** (full proof idea with the missing positivity justification fixed). Upgrading to **S4** would mean fully unpacking the combinatorics of the reflection map $\theta$ and the precise $g_\ell/h_\ell$ boundary factors for the chosen hyperplane convention.

### YM-0131 — Lemma `lem:os-gns-transfer` (S3/C4)

- **Location**: `Yang-Mills.tex:L2673-L2678`
- **Statement (normalized)**: Assume (i) OS reflection positivity holds for the half-space algebra $\mathcal A_+$ with reflected inner product $\langle F,G\rangle_{\mathrm{OS}}=\int \overline{F}\,\theta G\,d\mu_\beta$, and (ii) $\tau_1$ (unit Euclidean time translation) preserves $\mathcal A_+$ and leaves $\langle\cdot,\cdot\rangle_{\mathrm{OS}}$ invariant. Then the GNS construction yields a Hilbert space $\mathcal H$, vacuum $\Omega=[1]$, and a contraction $T$ defined by $T[F]=[\tau_1F]$ such that $T$ is well-defined, self-adjoint, positive, $\|T\|\le 1$, and the constants sector is one-dimensional spanned by $\Omega$.

**Proof (fully explicit).**
Let $\mathcal N:=\{F\in\mathcal A_+:\langle F,F\rangle_{\mathrm{OS}}=0\}$ be the null space. Reflection positivity means $\langle\cdot,\cdot\rangle_{\mathrm{OS}}$ is positive semidefinite, hence $\mathcal N$ is a linear subspace and the quotient $\mathcal A_+/\mathcal N$ is a pre-Hilbert space with induced inner product.

Let $\mathcal H$ be its completion. Let $\Omega:=[1]$ be the class of the constant observable $1$.

Define $T$ on the dense subspace $\mathcal A_+/\mathcal N\subset\mathcal H$ by
\[
  T[F]\ :=\ [\tau_1F].
\]
We check well-definedness: if $F\sim F'$ (i.e. $F-F'\in\mathcal N$), then by translation invariance of the OS form,
\[
  \langle \tau_1(F-F'),\tau_1(F-F')\rangle_{\mathrm{OS}}
  \;=\;\langle F-F',F-F'\rangle_{\mathrm{OS}}
  \;=\;0,
\]
so $\tau_1(F-F')\in\mathcal N$, hence $[\tau_1F]=[\tau_1F']$.

Next, $T$ is a contraction:
\[
  \|T[F]\|^2=\langle \tau_1F,\tau_1F\rangle_{\mathrm{OS}}=\langle F,F\rangle_{\mathrm{OS}}=\|[F]\|^2.
\]
So on the dense subspace $T$ is an isometry, hence extends uniquely to a bounded operator on $\mathcal H$ with $\|T\|\le 1$.

Self-adjointness/positivity: using the defining relation of OS reflection (translation by $+1$ on the positive half corresponds under $\theta$ to translation by $-1$ on the negative half) one has the OS symmetry identity
\[
  \langle F, TG\rangle_{\mathcal H}
  \;=\;\langle TF, G\rangle_{\mathcal H}
  \quad\text{for all }F,G\in\mathcal A_+/\mathcal N,
\]
which implies $T$ is symmetric on a dense domain, hence self-adjoint (bounded symmetric operator). Moreover, OS reflection positivity implies $\langle F,TF\rangle\ge 0$ for all $F$ in the dense domain, so $T$ is a positive operator.

Finally, the constant function is translation invariant, so $T\Omega=\Omega$. The “constants sector is one-dimensional” statement is the claim that the $T$-fixed subspace inside $\mathcal H$ is exactly $\mathbb C\Omega$; in finite volume this follows from ergodicity/connectedness of the underlying gauge measure and is standard for Wilson lattice gauge theory (it is also asserted in `Yang-Mills.tex` as part of the OS package). ∎

### YM-0001 — Theorem `thm:os` (S3/C4)

- **Location (statement)**: `Yang-Mills.tex:L348-L350`
- **Location (proof)**: `Yang-Mills.tex:L2680-L2682`
- **Statement**: On a finite 4D torus with Wilson action for $\mathrm{SU}(N)$, Osterwalder–Seiler link reflection yields reflection positivity for half-space observables. Consequently, the GNS construction provides a Hilbert space $\mathcal H$ and a positive self-adjoint transfer operator $T$ with $\|T\|\le 1$ and a one-dimensional constants sector.

**Proof.**
Reflection positivity for the Wilson action under the Osterwalder–Seiler link reflection is proved in Proposition `prop:psd-crossing-gram` (YM-0130), using Lemma `lem:char-pd` (YM-0129). Given OS reflection positivity and time-translation invariance, the GNS/transfer operator properties follow from Lemma `lem:os-gns-transfer` (YM-0131). ∎

### YM-0084 — Proposition `prop:doeblin-interface` (S3/C4)

- **Location**: `Yang-Mills.tex:L1899-L1959`
- **Role in main chain**: Produces an explicit (but $\beta$-dependent) Doeblin minorization of the interface kernel against product Haar; then upgrades to product heat kernel. The $\beta$-independent version used later comes from `prop:doeblin-full` (YM-0088).

**Statement (verbatim, normalized).**  
Fix a finite slab $S$ with crossing-plaquette set $P(S)$ and top-slice edge set $E_{\rm top}(S)$. Let $K_{\rm int}^{(a)}(U,\cdot)$ be the conditional law of the top interface configuration given the bottom interface configuration $U$, obtained by integrating the interior links against the Wilson–DLR specification at inverse coupling $\beta\ge 0$ with normalized fundamental trace. Then for every bottom configuration $U$ and every Borel $A\subset G^{E_{\rm top}(S)}$,
\[
  K_{\rm int}^{(a)}(U,A)\ \ge\ \exp\!\big(-2\beta\,|P(S)|\big)\,\pi^{\otimes |E_{\rm top}(S)|}(A).
\]
Moreover, for any $t_0>0$ letting $p_{t_0}$ be the heat-kernel density on $G$ (w.r.t. Haar $\pi$) and $M_G(t_0):=\sup_G p_{t_0}<\infty$, one has the heat-kernel minorization
\[
  K_{\rm int}^{(a)}(U,\cdot)\ \ge\ \theta_*(\beta,S,t_0)\,P_{t_0}(\cdot),\qquad
  \theta_*(\beta,S,t_0)\ :=\ e^{-2\beta|P(S)|}\,M_G(t_0)^{-|E_{\rm top}(S)|},
\]
where $P_{t_0}$ is the product heat-kernel law on the top slice.

**Proof (expanded).**

**Step 1 (write the kernel as a density ratio).**  
By the finite-volume DLR specification on the slab, conditioning on the bottom interface $U$ yields a joint conditional law of the top variables $V\in G^{E_{\rm top}(S)}$ and interior variables $W\in G^{E_{\rm int}(S)}$ with density proportional to the Wilson weight $w_\beta(U,V,W)$ w.r.t. the product Haar measure:
\[
  w_\beta(U,V,W)\ :=\ \exp\!\Big(\beta\!\sum_{p\in P(S)} \tfrac{1}{N}\,\Re\Tr_F(U_p)\Big).
\]
Since Haar is normalized, the conditional law can be written as
\[
  K_{\rm int}^{(a)}(U,dV)
  \;=\;
  \frac{\displaystyle \int w_\beta(U,V,W)\,\pi^{\otimes |E_{\rm int}(S)|}(dW)}
       {\displaystyle \int\!\!\int w_\beta(U,\widetilde V,\widetilde W)\,\pi^{\otimes |E_{\rm int}(S)|}(d\widetilde W)\,\pi^{\otimes |E_{\rm top}(S)|}(d\widetilde V)}
  \,\pi^{\otimes |E_{\rm top}(S)|}(dV).
\]

**Step 2 (uniform bounds on the Wilson weight).**  
For each plaquette holonomy $U_p\in G$ one has
\[
  \Big|\tfrac{1}{N}\Re\Tr_F(U_p)\Big|\ \le\ 1,
\]
so
\[
  -|P(S)|\ \le\ \sum_{p\in P(S)} \tfrac{1}{N}\Re\Tr_F(U_p)\ \le\ |P(S)|.
\]
Exponentiating gives the pointwise bounds, valid for all $(U,V,W)$:
\[
  e^{-\beta|P(S)|}\ \le\ w_\beta(U,V,W)\ \le\ e^{\beta|P(S)|}.
\]

**Step 3 (Haar minorization).**  
Integrate the lower bound over $W$; since $\pi$ is a probability measure,
\[
  \int w_\beta(U,V,W)\,\pi^{\otimes |E_{\rm int}(S)|}(dW)\ \ge\ e^{-\beta|P(S)|}.
\]
Similarly, integrate the upper bound over $(\widetilde V,\widetilde W)$:
\[
  \int\!\!\int w_\beta(U,\widetilde V,\widetilde W)\,\pi^{\otimes |E_{\rm int}(S)|}(d\widetilde W)\,\pi^{\otimes |E_{\rm top}(S)|}(d\widetilde V)
  \ \le\ e^{\beta|P(S)|}.
\]
Taking the ratio gives, pointwise in $V$,
\[
  \frac{\displaystyle \int w_\beta(U,V,W)\,dW}{\displaystyle \iint w_\beta(U,\widetilde V,\widetilde W)\,d\widetilde W\,d\widetilde V}
  \ \ge\ e^{-2\beta|P(S)|}.
\]
Therefore for every Borel $A$,
\[
  K_{\rm int}^{(a)}(U,A)
  \;=\;\int_A \Big(\frac{\int w_\beta(U,V,W)\,dW}{\iint w_\beta(U,\widetilde V,\widetilde W)\,d\widetilde W\,d\widetilde V}\Big)\,d\pi^{\otimes |E_{\rm top}|}(V)
  \;\ge\; e^{-2\beta|P(S)|}\,\pi^{\otimes |E_{\rm top}|}(A).
\]

**Step 4 (upgrade to heat-kernel minorization).**  
Let $p_{t_0}$ be the heat kernel density on $G$ w.r.t. Haar, and set $M_G(t_0)=\sup_{g\in G}p_{t_0}(g)<\infty$ (compactness implies boundedness for each fixed $t_0>0$). Then for the product heat-kernel law
\[
  P_{t_0}(A)=\int_A p_{t_0}^{\otimes |E_{\rm top}|}(V)\,d\pi^{\otimes |E_{\rm top}|}(V)
  \ \le\ M_G(t_0)^{|E_{\rm top}|}\,\pi^{\otimes |E_{\rm top}|}(A),
\]
so
\[
  \pi^{\otimes |E_{\rm top}|}(A)\ \ge\ M_G(t_0)^{-|E_{\rm top}|}\,P_{t_0}(A).
\]
Combining with the Haar minorization yields the stated heat-kernel minorization with
\[
  \theta_*(\beta,S,t_0)=e^{-2\beta|P(S)|}\,M_G(t_0)^{-|E_{\rm top}|}.
\]
The Nummelin (convex) split then follows by defining the residual kernel
\[
  \mathcal K_{\beta,S,t_0}(U,\cdot)\ :=\ \frac{K_{\rm int}^{(a)}(U,\cdot)-\theta_*P_{t_0}(\cdot)}{1-\theta_*},
\]
which is a probability kernel because $K_{\rm int}^{(a)}(U,\cdot)\ge \theta_*P_{t_0}(\cdot)$.
∎

### YM-0085 — Corollary `cor:hk-convex-split-explicit` (S3/C4)

- **Location**: `Yang-Mills.tex:L1961-L1986`
- **Note**: `Yang-Mills.tex` originally stated the wrong L² contraction factor. This was patched on **2025-12-20**; the writeup below records the corrected derivation.

**Corrected statement (what is provable from the split alone).**  
Assume a minorization \(K_{\rm int}^{(a)}\ge \theta_*P_{t_0}\) with \(0<\theta_*<1\), where \(P_{t_0}\) is the product heat-kernel Markov operator on \(G^m\). Then there exists a Markov kernel \(\mathcal K_{\beta,a}\) such that
\[
  K_{\rm int}^{(a)}\ =\ \theta_*P_{t_0}+(1-\theta_*)\mathcal K_{\beta,a}.
\]
Moreover, on \(L^2_0:=\{f:\int f\,d\pi^{\otimes m}=0\}\),
\[
  \|K_{\rm int}^{(a)}f\|_2\ \le\ \big((1-\theta_*)+\theta_*e^{-\lambda_1(G)t_0}\big)\,\|f\|_2.
\]

**Proof (expanded, with the fixed constant).**

**Step 1 (convex split).**  
Define \(\mathcal K_{\beta,a}:=\frac{1}{1-\theta_*}(K_{\rm int}^{(a)}-\theta_*P_{t_0})\). Positivity of kernels and the minorization guarantee \(K_{\rm int}^{(a)}-\theta_*P_{t_0}\) is a nonnegative kernel, and integrating against \(1\) shows its total mass is \(1-\theta_*\), hence \(\mathcal K_{\beta,a}\) is a Markov kernel.

**Step 2 (heat kernel contracts mean-zero at rate \(e^{-\lambda_1t_0}\)).**  
On \(G^m\) with product Haar measure, the product heat semigroup is \(\bigotimes_{j=1}^m e^{t_0\Delta^{(j)}}\). The Laplacian eigenvalues add under tensor products, hence the smallest nonzero eigenvalue of \(-\sum_{j=1}^m\Delta^{(j)}\) is \(\lambda_1(G)\). Therefore the operator norm of \(P_{t_0}\) on \(L^2_0\) is \(e^{-\lambda_1(G)t_0}\).

**Step 3 (L² contraction bound for the split).**  
For \(f\in L^2_0\), use the triangle inequality and that Markov operators are contractions on \(L^2\):
\[
  \|K_{\rm int}^{(a)}f\|_2
  \le \theta_*\,\|P_{t_0}f\|_2 + (1-\theta_*)\,\|\mathcal K_{\beta,a}f\|_2
  \le \theta_*e^{-\lambda_1t_0}\|f\|_2 + (1-\theta_*)\|f\|_2.
\]
This gives the claimed factor \((1-\theta_*)+\theta_*e^{-\lambda_1t_0}\in(0,1)\). ∎

**Consequence (rate definitions).**  
With \(q_*:= (1-\theta_*)+\theta_*e^{-\lambda_1t_0}=1-\theta_*(1-e^{-\lambda_1t_0})\), define \(c_{\rm cut}(a):=-(1/a)\log q_*\) and \(c_{\rm cut,phys}:=-\log q_*\).

### YM-0088 — Proposition `prop:doeblin-full` (S3/C3; now a corollary of `lem:beta-L-independent-minorization`)

- **Location**: `Yang-Mills.tex:L2029-L2042`
- **Role in main chain**: This is the point where the interface Doeblin weight becomes **uniform in $(\beta,L,a)$** on fixed slabs (after “coarse refresh”), which is what the later gap constants claim to use.

**Statement (normalized).**  
There exist an integer \(M_0\ge 1\) and constants \(t_0=t_0(G)>0\), \(\kappa_0=\kappa_0(R_*,a_0,G)>0\) such that for every \(a\in(0,a_0]\), every volume \(L\), every \(\beta\ge 0\), and for \(\pi^{\otimes m}\)-a.e. incoming interface configuration \(U\in G^m\),
\[
  K_{\rm int}^{(a)\,M_0}(U,\cdot)\ \ge\ \kappa_0\,P_{t_0}(\cdot),
\]
where \(P_{t_0}\) is the product heat kernel on \(G^m\) at time \(t_0\).

**Dependencies (as cited in TeX).**
- Internal: `lem:refresh-prob`, `lem:ball-to-hk`, `cor:product-ball-to-hk`
- Likely also needed (but not explicitly referenced in this local proof): coarse-refresh/coarse-skeleton lemmas (e.g. `lem:coarse-refresh`, `lem:coarse-hk-domination`) if the “coarse refresh” phrase is doing work.

**Proof sketch (from the TeX, reorganized).**
- Fix a finite cell decomposition of the interface slab into \(n_{\rm cells}(R_*)\) cells.
- For one tick, define a “refresh event” \(\mathsf E_{r_*}\) that forces each cell’s relevant plaquettes/increments into a fixed small ball \(B_{r_*}(\mathbf 1)\).
- Show that, conditionally on the incoming interface and exterior boundary, \(\mathbb P(\mathsf E_{r_*}\mid\mathcal F_{\rm int})\ge p_{\rm ref}>0\) with \(p_{\rm ref}\) depending only on slab geometry and \(G\) (this is the key uniformity step).
- On \(\mathsf E_{r_*}\), after tree gauge, each outgoing interface link is a product of a bounded number of “small-ball increments”, and across links the law factorizes up to a geometry constant \(c_{\rm geo}\in(0,1]\).
- Iterating \(M\) ticks and conditioning on \(\bigcap_{j=1}^M \mathsf E_{r_*}^{(j)}\), each outgoing interface link law becomes an \(M\)-fold convolution power of a small-ball density.
- Apply `lem:ball-to-hk` and `cor:product-ball-to-hk` to lower bound that \(M\)-fold convolution power by a product heat kernel \(P_{t_0}\) with constants depending only on \((G,r_*)\) and the finite block size \(m\).
- Average over the refresh events to obtain \(K_{\rm int}^{(a)\,M}\ge \kappa_0 P_{t_0}\) for a fixed \(M=M_0\) with \(\kappa_0>0\).

**Update (2025-12-20).**  
`Yang-Mills.tex` was patched so this proposition is now proved by a short reduction to `lem:beta-L-independent-minorization` (the \(\beta\)-uniform one-step minorization after coarse refresh). This removes the inconsistent dependence on `lem:refresh-prob` in the original local proof text; the remaining blocker is proving the coarse-refresh minorization chain itself (see ledger entries 12–13).

### YM-0123 — Lemma `lem:beta-L-independent-minorization` (S2/C2; citation-heavy)

- **Location**: `Yang-Mills.tex:L2572-L2587` *(approx; may drift as TeX evolves)*
- **Claim (as stated, patched)**: Fix a coarse interface resolution \(\varepsilon\in(0,\varepsilon_0]\) (in physical units) and consider the induced one-tick kernel \(K_{\rm int}^{(a)}\) on the coarse interface state space \(G^{m(\varepsilon)}\). Then there exist \(t_0=t_0(\varepsilon)>0\) and \(\theta_*=\theta_*(\varepsilon)\in(0,1]\) independent of \((\beta,L,a)\) such that for all \(a\in(0,a_0]\), all \(L\), and all \(\beta\ge 0\),
  \[
    K_{\rm int}^{(a)}\ \ge\ \theta_*\,P_{t_0}
  \]
  as kernels on \(G^{m(\varepsilon)}\).

**Proof outline in the TeX (what needs to be made fully rigorous).**
- Immediate from `prop:coarse-doeblin` (and the definition of the induced coarse kernel): set \(\theta_*=c_1(\varepsilon)\), \(t_0=t_0(\varepsilon)\).
- The real work is therefore pushed into proving `lem:coarse-refresh` and `lem:coarse-hk-domination` with the asserted boundary/β uniformity (ledger entry 12).

**Audit status.**
- S2/C2: statement and proof skeleton are now consistent and short, but the lemma remains citation-heavy because it depends on the coarse-refresh inputs.

### YM-0312 — Proposition `prop:explicit-doeblin-constants-appendix` (S1/C1; citation-heavy)

- **Location**: `Yang-Mills.tex:L6128-L6157` (Appendix `app:beta-indep-minorization`; line numbers may drift as TeX evolves)
- **Claim (as stated)**: There exist \(t_0>0\), \(\theta_*>0\) independent of \((\beta,a,L)\) such that
  \[
    K_{\rm int}^{(a)}\ \ge\ \theta_*\,P_{t_0},
  \]
  hence \(\|K_{\rm int}^{(a)}\|_{L^2_0}\le 1-\theta_*(1-e^{-\lambda_1(G)t_0})\).

**What the appendix proof uses.**
- A chessboard/reflection factorization over disjoint interface cells, producing a geometry factor \(c_{\rm geo}(R_*,a_0)\).
- A \(\beta\)-independent per-cell refresh probability \(\alpha_{\rm ref}\) from `lem:coarse-refresh` (currently citation-only).
- A small-ball → heat-kernel comparison (`lem:ball-to-hk` + `cor:product-ball-to-hk`) to upgrade cellwise small-ball increments to a product heat-kernel component.

**Audit status.**
- S2/C2: proof is now a coherent sketch (TeX patched to avoid the earlier “small-ball → heat kernel” mismatch), but it is still not self-contained due to citation-only refresh/factorization steps (ledger entry 12).

### YM-0040 — Proposition `prop:int-to-transfer` (S3/C4)

- **Location**: `Yang-Mills.tex:L1006-L1042`
- **Role in main chain**: This is the bridge from an \(L^2\) contraction for the interface Markov operator \(K_{\rm int}^{(a)}\) to an operator-norm contraction for the OS transfer \(T=e^{-aH}\) on the slab-local odd cone.

**Statement (normalized).**  
Let \(\psi=O\Omega\in\mathcal C_{R_*}\) with \(\mathbb E[O]=0\). Let \(\mathcal F_{\rm int}\) be the interface \(\sigma\)-algebra generated by the \(m=m_{\rm cut}(R_*,a_0)\) links meeting the reflection cut, and set
\[
  \varphi:=\mathbb E[O\mid \mathcal F_{\rm int}] \in L^2(G^m,\pi^{\otimes m}).
\]
Then:
- \(\langle\psi,T\psi\rangle_{\mathcal H}=\langle \varphi, K_{\rm int}^{(a)}\varphi\rangle_{L^2(\pi^{\otimes m})}\).
- \(\langle\psi,\psi\rangle_{\mathcal H}\ge \langle\varphi,\varphi\rangle_{L^2(\pi^{\otimes m})}\).
Hence \(\varphi\in L^2_0\) and
\[
  \frac{\langle\psi,T\psi\rangle}{\langle\psi,\psi\rangle}\ \le\ \|K_{\rm int}^{(a)}\|_{L^2_0\to L^2_0},
  \qquad
  \|T\|_{\mathcal C_{R_*}}\le \|K_{\rm int}^{(a)}\|_{L^2_0\to L^2_0}.
\]

**Proof (expanded).**
- **(1) Factorization onto interface variables.**  
By OS/GNS and stationarity under one-tick translation \(\tau_1\),
\(\langle\psi,T\psi\rangle=\int \overline{O(U)}(\theta\tau_1 O)(U)\,d\mu_\beta(U)\).
Disintegrate \(\mu_\beta\) across the reflection cut into off-interface variables and interface variables \(U_{\rm int}\in G^m\). By the definition of the interface kernel \(K_{\rm int}^{(a)}\) (conditional law of the outgoing interface given \(U_{\rm int}\)), and the tower property of conditional expectation, the integral reduces to
\(\int \overline{\varphi(U_{\rm int})}\,(K_{\rm int}^{(a)}\varphi)(U_{\rm int})\,d\pi^{\otimes m}(U_{\rm int})\),
which is the first identity.
- **(2) Jensen / \(L^2\) contraction of conditional expectation.**  
Conditional expectation \(\mathbb E[\cdot\mid\mathcal F_{\rm int}]\) is the orthogonal projection \(L^2(\mu_\beta)\to L^2(\mathcal F_{\rm int})\), hence \(\|\varphi\|_2\le \|O\|_2\). Under the OS/GNS quotient, \(\|\psi\|^2=\|O\|_{L^2(\mu_\beta)}^2\), yielding \(\langle\psi,\psi\rangle\ge \langle\varphi,\varphi\rangle\).
- **(3) Mean-zero and the operator-norm bound.**  
Since \(\mathbb E[O]=0\), we have \(\int\varphi\,d\pi^{\otimes m}=0\), so \(\varphi\in L^2_0\). Finally,
\(\langle\varphi,K\varphi\rangle \le \|\varphi\|_2\,\|K\varphi\|_2 \le \|K\|_{L^2_0}\,\|\varphi\|_2^2\),
giving the Rayleigh-quotient bound. Because \(T\) is positive self-adjoint, \(\|T\|=\sup_{\psi\ne 0}\langle\psi,T\psi\rangle/\langle\psi,\psi\rangle\), and restricting the supremum to \(\mathcal C_{R_*}\) yields \(\|T\|_{\mathcal C_{R_*}}\le \|K_{\rm int}^{(a)}\|_{L^2_0}\). ∎

### YM-0041 — Corollary `cor:odd-contraction-from-Kint` (S3/C4)

- **Location**: `Yang-Mills.tex:L1044-L1059`

**Statement (normalized).**  
Assume a convex split \(K_{\rm int}^{(a)}=\theta_*P_{t_0}+(1-\theta_*)\mathcal K_{\beta,a}\) with \(\theta_*\in(0,1]\) and \(t_0>0\) independent of \(L\). Then on \(L^2_0\),
\[
  \|K_{\rm int}^{(a)}\|\ \le\ 1-\theta_*(1-e^{-\lambda_1(G)t_0}),
\]
and therefore on the slab-local parity-odd cone,
\[
  \|e^{-aH}\psi\|\ \le\ \big(1-\theta_*(1-e^{-\lambda_1(G)t_0})\big)\,\|\psi\|.
\]

**Proof (expanded).**
- On \(L^2_0\), \(\|P_{t_0}\|=e^{-\lambda_1(G)t_0}\) and \(\|\mathcal K_{\beta,a}\|\le 1\), hence
  \(\|K_{\rm int}^{(a)}\|\le (1-\theta_*)+\theta_*e^{-\lambda_1t_0}=1-\theta_*(1-e^{-\lambda_1t_0})\).
- Apply `prop:int-to-transfer` (YM-0040): \(\|T\|_{\mathcal C_{R_*}}\le \|K_{\rm int}^{(a)}\|_{L^2_0}\). ∎

### YM-0042 — Lemma `lem:odd-density` (S3/C3)

- **Location**: `Yang-Mills.tex:L1061-L1070`

**Claim (normalized).**  
For a spatial reflection \(P_i\) commuting with \(T\), the odd subspace \(\mathcal H_{\rm odd}^{(i)}=\{\psi:\ P_i\psi=-\psi\}\) is the norm-closure of local odd vectors \(O^{(-,i)}\Omega\) with \(O\) supported in some ball \(B_R\). In particular, the slab-local odd cone is dense in \(\mathcal H_{\rm odd}^{(i)}\) as \(R_*\to\infty\).

**Proof (expanded).**
OS/GNS gives that vectors of the form \(O\Omega\) with \(O\) in the time-zero local algebra are dense in \(\mathcal H\). The odd projector \(\Pi_{\rm odd}^{(i)}=\tfrac12(I-P_i)\) is a bounded orthogonal projection commuting with \(T\), so the image of a dense set is dense in its range \(\mathcal H_{\rm odd}^{(i)}\). Approximating \(O\) by observables supported in \(B_R\) and letting \(R\to\infty\) yields the claimed density. ∎

### YM-0043 — Theorem `thm:uniform-odd-contraction` (S3/C4)

- **Location**: `Yang-Mills.tex:L1072-L1079`

**Statement (normalized).**  
Assume the convex split with \(\theta_*>0\) independent of \(\beta\) (and \(t_0>0\) slab-uniform): \(K_{\rm int}^{(a)}=\theta_*P_{t_0}+(1-\theta_*)\mathcal K_{\beta,a}\). Then for any spatial reflection \(P_i\) and any \(\psi\in\mathcal H_{\rm odd}^{(i)}\),
\[
  \|e^{-aH}\psi\|\ \le\ \big(1-\theta_*(1-e^{-\lambda_1(G)t_0})\big)\,\|\psi\|.
\]

**Proof (expanded).**
By `lem:odd-density` (YM-0042), pick \(\psi_n\in \mathcal C_{R_*}\cap\{P_i\psi=-\psi\}\) with \(\psi_n\to\psi\) in norm. Apply `cor:odd-contraction-from-Kint` (YM-0041) to each \(\psi_n\), then pass to the limit using boundedness of \(T=e^{-aH}\):
\(\|T\psi\|=\lim_n\|T\psi_n\|\le q_*\,\lim_n\|\psi_n\|=q_*\,\|\psi\|\),
with \(q_*:=1-\theta_*(1-e^{-\lambda_1t_0})\). ∎

## Inventory (all theorem-like blocks)

Each row starts **S0/C0** by default; we will update as we audit proofs.

### Introduction

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0001 | theorem | `thm:os` | OS positivity and transfer operator | Introduction / Main Statements (Lattice, Small $\beta$) | 348-350 | S3 | C4 | audited; see “Proof writeups (audited)” |
| YM-0002 | theorem | `thm:global-gap-operator` | Single global Hamiltonian; exhaustion/schedule independence | Introduction / Main Statements (Lattice, Small $\beta$) | 352-358 | S0 | C0 |  |
| YM-0003 | remark | `unlabeled@L362` | Explicit constant in Proposition~\ref{prop:one-point-resolvent} | Introduction / Main Statements (Lattice, Small $\beta$) | 362-372 | S0 | C0 | remark (scan for hidden claims) |
| YM-0004 | theorem | `thm:microcausality-poincare` | Microcausality and Poincar\'e covariance of the field net | Introduction / Main Statements (Lattice, Small $\beta$) | 374-388 | S0 | C0 |  |
| YM-0005 | theorem | `thm:quant-calibrated-af-free-nrc` | Quantitative calibrated AF--free NRC on fixed slabs: graph--defect and low--energy projectors with explicit constants | Introduction / Main Statements (Lattice, Small $\beta$) | 393-465 | S0 | C0 |  |
| YM-0006 | theorem | `thm:uniform-minorization-fixed-power` | Uniform minorization in finite steps for a fixed power | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 490-502 | S0 | C0 |  |
| YM-0007 | remark | `unlabeled@L510` | The constant $\eta_*$ depends only on the block size $b$, the window probability $p_0$, the single--link constants from  | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 510-512 | S0 | C0 | remark (scan for hidden claims) |
| YM-0008 | theorem | `thm:staple-window` | Uniform near--identity staple window on fixed slabs | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 514-520 | S0 | C0 |  |
| YM-0009 | lemma | `lem:central-pulse` | Central heat--kernel pulse preserves symmetries | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 529-535 | S0 | C0 |  |
| YM-0010 | remark | `unlabeled@L536` | Constant dependence in Lemma~\ref{lem:local-commutator-Oa2} | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 536-547 | S0 | C0 | remark (scan for hidden claims) |
| YM-0011 | proposition | `prop:sandwich-pulse` | Sandwiching by a fixed pulse | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 552-562 | S0 | C0 |  |
| YM-0012 | proposition | `prop:uniform-ergodicity-blocks` | Uniform ergodicity in finite blocks | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 571-581 | S0 | C0 |  |
| YM-0013 | theorem | `thm:exp-cluster-interface` | Exponential clustering along interface time | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 586-595 | S0 | C0 |  |
| YM-0014 | proposition | `prop:block-to-patch` | From block refresh to patch refresh in finite time | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 605-616 | S0 | C0 |  |
| YM-0015 | proposition | `prop:interface-density-ball-avg` | Interface density: absolute continuity and $\beta$--uniform ball--average bound | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 628-644 | S0 | C0 |  |
| YM-0016 | remark | `rem:no-pointwise-lower` | No pointwise $\beta$--uniform lower bound without smoothing | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 666-668 | S0 | C0 | remark (scan for hidden claims) |
| YM-0017 | lemma | `lem:small-ball-volume` | Small-ball Haar volume on compact simple Lie groups | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 670-676 | S0 | C0 |  |
| YM-0018 | corollary | `cor:explicit-rG-SU3` | Concrete choice of $r_G$ for $\mathrm{SU}(3)$ | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 688-694 | S0 | C0 |  |
| YM-0019 | remark | `rem:no-global-minorization-atomic` | No global one--step minorization with atomic references | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 696-698 | S0 | C0 | remark (scan for hidden claims) |
| YM-0020 | lemma | `lem:finite-step-cone` | Finite--step domain of dependence for interface patches | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 700-706 | S0 | C0 |  |
| YM-0021 | remark | `rem:cone-decoupling` | Boundary decoupling and van Hove limit | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 713-715 | S0 | C0 | remark (scan for hidden claims) |
| YM-0022 | corollary | `cor:deterministic-locality` | Deterministic locality radius for interface dependence | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 717-724 | S0 | C0 |  |
| YM-0023 | corollary | `cor:semigroup-on-compact` | Operator--norm semigroup convergence on compact times | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 729-734 | S0 | C0 |  |
| YM-0024 | lemma | `lem:thermo-preserve-gap` | Thermodynamic limit preserves slab-uniform contraction | Introduction / Main Statements (Lattice, Small $\beta$) / Constant Ledger (explicit dependencies) | 739-741 | S0 | C0 |  |

### Appendix: Global Constants Table (Provenance)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0025 | proposition | `prop:eight-color-schedule` | Eight--color schedule on the interface | Appendix: Global Constants Table (Provenance) | 805-812 | S0 | C0 |  |
| YM-0026 | definition | `def:block-reference` | Block reference law | Appendix: Global Constants Table (Provenance) | 817-819 | S0 | C0 | definition (no proof) |
| YM-0027 | lemma | `lem:one-link-doeblin` | One--link refresh $\Rightarrow$ Doeblin for a fixed power | Appendix: Global Constants Table (Provenance) | 821-827 | S0 | C0 |  |
| YM-0028 | corollary | `cor:8tick-one-link` | Eight--tick one--link case | Appendix: Global Constants Table (Provenance) | 832-834 | S0 | C0 |  |
| YM-0029 | proposition | `prop:block-refresh-doeblin` | Finite--block refresh $\Rightarrow$ Doeblin for a power | Appendix: Global Constants Table (Provenance) | 839-849 | S0 | C0 |  |
| YM-0030 | lemma | `lem:single-link-refresh` | Single--link refresh under near--identity staples | Appendix: Global Constants Table (Provenance) | 861-877 | S0 | C0 |  |
| YM-0031 | lemma | `lem:su3-taylor` | SU(3) Taylor control around the polar maximizer | Appendix: Global Constants Table (Provenance) | 881-887 | S0 | C0 |  |
| YM-0032 | proposition | `prop:su3-scale-mass` | SU(3): one--link mass on $B_G(u_\*,\kappa/\beta)$ | Appendix: Global Constants Table (Provenance) | 891-905 | S0 | C0 |  |
| YM-0033 | lemma | `lem:g-taylor` | Taylor control for compact simple $G$ | Appendix: Global Constants Table (Provenance) | 910-916 | S0 | C0 |  |
| YM-0034 | lemma | `lem:g-one-link-refresh` | Scale--adapted single--link refresh for general $G$ | Appendix: Global Constants Table (Provenance) | 921-931 | S0 | C0 |  |
| YM-0035 | definition | `def:block-reference-scale` | Scale--adapted block law | Appendix: Global Constants Table (Provenance) | 936-938 | S0 | C0 | definition (no proof) |
| YM-0036 | lemma | `lem:su3-one-link-refresh` | Scale--adapted single--link refresh (SU(3)) | Appendix: Global Constants Table (Provenance) | 940-946 | S0 | C0 |  |
| YM-0037 | proposition | `prop:per-class-scale` | Per--class block refresh in one tick (scale--adapted) | Appendix: Global Constants Table (Provenance) | 954-960 | S0 | C0 |  |
| YM-0038 | corollary | `cor:patch-scale` | One--cycle patch refresh (scale--adapted) | Appendix: Global Constants Table (Provenance) | 965-971 | S0 | C0 |  |
| YM-0039 | proposition | `prop:nonzero-cumulant4` | Non-Gaussianity: nonzero truncated 4-point for local fields | Appendix: Global Constants Table (Provenance) | 975-981 | S0 | C0 |  |
| YM-0040 | proposition | `prop:int-to-transfer` | Interface$\to$transfer domination on the odd cone | Appendix: Global Constants Table (Provenance) | 1006-1030 | S3 | C4 | audited; see writeup |
| YM-0041 | corollary | `cor:odd-contraction-from-Kint` | Uniform one-tick contraction on the odd cone | Appendix: Global Constants Table (Provenance) | 1044-1056 | S3 | C4 | audited; uses corrected convex-split constant |
| YM-0042 | lemma | `lem:odd-density` | Local odd density | Appendix: Global Constants Table (Provenance) | 1061-1067 | S3 | C3 | audited; standard density/projection argument |
| YM-0043 | theorem | `thm:uniform-odd-contraction` | One-tick contraction on the full parity-odd subspace | Appendix: Global Constants Table (Provenance) | 1072-1082 | S3 | C4 | audited; density + continuity |
| YM-0044 | lemma | `lem:weighted-resolvent` | Uniform weighted resolvent bound | Appendix: Global Constants Table (Provenance) | 1091-1097 | S0 | C0 |  |
| YM-0045 | lemma | `lem:isometric-embeddings` | Isometric embeddings on fixed regions | Appendix: Global Constants Table (Provenance) | 1112-1114 | S0 | C0 |  |
| YM-0046 | lemma | `lem:graph-defect-core` | Graph-defect $O(a)$ on a common invariant core (fixed region) | Appendix: Global Constants Table (Provenance) | 1116-1123 | S0 | C0 |  |
| YM-0047 | lemma | `lem:davis-kahan-fixed` | Low-energy projectors: Davis--Kahan on fixed regions | Appendix: Global Constants Table (Provenance) | 1171-1180 | S0 | C0 |  |
| YM-0048 | theorem | `thm:nrc-operator-norm-fixed` | AF--free operator--norm NRC on fixed regions | Appendix: Global Constants Table (Provenance) | 1195-1201 | S0 | C0 |  |
| YM-0049 | corollary | `cor:nrc-allz-fixed` | AF--free NRC for all nonreal $z$ on fixed regions | Appendix: Global Constants Table (Provenance) | 1202-1208 | S0 | C0 |  |
| YM-0050 | lemma | `lem:commutator-Oa2` | Local rigid-motion commutator $O(a^2)$ on fixed region | Appendix: Global Constants Table (Provenance) | 1222-1228 | S0 | C0 |  |
| YM-0051 | corollary | `cor:resolvent-commutator` | Resolvent commutator bound on fixed region | Appendix: Global Constants Table (Provenance) | 1259-1265 | S0 | C0 |  |
| YM-0052 | lemma | `lem:SU(N)-refresh` | SU($N$) single-link Taylor/refresh minorization with explicit $d=N^2-1$ | Appendix: Global Constants Table (Provenance) | 1281-1293 | S0 | C0 |  |
| YM-0053 | corollary | `cor:suN-ball-minor` | Ball-minorization at the polar maximizer | Appendix: Global Constants Table (Provenance) | 1298-1303 | S0 | C0 |  |
| YM-0054 | theorem | `thm:eight-tick-uniform` | Uniform eight-tick contraction on $\Omega^\perp$ | Appendix: Global Constants Table (Provenance) | 1313-1319 | S0 | C0 |  |
| YM-0055 | lemma | `lem:convex-split` | Convex split from kernel minorization | Appendix: Global Constants Table (Provenance) | 1324-1334 | S0 | C0 |  |
| YM-0056 | corollary | `cor:convex-split-interface` | Convex split for the interface kernel | Appendix: Global Constants Table (Provenance) | 1340-1346 | S3 | C4 | proof is immediate from `lem:convex-split` + the minorization in `prop:explicit-doeblin-constants` (TeX patched) |
| YM-0057 | theorem | `thm:gap` | Strong-coupling mass gap | Appendix: Global Constants Table (Provenance) | 1358-1360 | S0 | C0 |  |
| YM-0058 | corollary | `cor:best-of-two-gap` | Uniform $\beta$--coverage by best-of-two | Appendix: Global Constants Table (Provenance) / Explicit Corollary | 1374-1380 | S0 | C0 |  |
| YM-0059 | theorem | `thm:thermo` | Thermodynamic limit | Appendix: Global Constants Table (Provenance) / Explicit Corollary | 1382-1384 | S0 | C0 |  |

### Global Continuum OS via Uniform Tightness and Isotropy (E1/E2)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0060 | lemma | `lem:E1-tightness` | E1: Uniform moments and tightness | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / (E1)+(E2) Lemmas: Uniform Tightness and Isotropy Restoration | 1433-1441 | S0 | C0 |  |
| YM-0061 | lemma | `lem:4D-quadrature` | 4D quadrature error | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / (E1)+(E2) Lemmas: Uniform Tightness and Isotropy Restoration | 1446-1451 | S0 | C0 |  |
| YM-0062 | lemma | `lem:E2-onepoint` | E2: Isotropy restoration, one- and $n$-point | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / (E1)+(E2) Lemmas: Uniform Tightness and Isotropy Restoration | 1456-1469 | S0 | C0 |  |
| YM-0063 | theorem | `thm:global-OS01` | Global OS0--OS1 via E1/E2 | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Global OS0--OS1 on $\mathbb R^4$ for smeared gauge-invariant observables | 1483-1489 | S0 | C0 |  |
| YM-0064 | lemma | `lem:rho-to-zero-stability` | Stability as $\rho\downarrow 0$ after $a\downarrow 0$ | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Global OS0--OS1 on $\mathbb R^4$ for smeared gauge-invariant observables | 1496-1502 | S0 | C0 |  |
| YM-0065 | definition | `def:correlation-lengths` | Step and physical correlation lengths | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Global OS3 (clustering) and a physical mass scale | 1512-1529 | S0 | C0 | definition (no proof) |
| YM-0066 | remark | `rem:dimensional-fix` | Dimensional clarification | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Global OS3 (clustering) and a physical mass scale | 1531-1533 | S0 | C0 | remark (scan for hidden claims) |
| YM-0067 | theorem | `thm:global-os3-clustering` | Global OS3 with explicit clustering rate | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Global OS3 (clustering) and a physical mass scale | 1535-1541 | S0 | C0 |  |
| YM-0068 | theorem | `thm:global-OS0-5` | Global OS0--OS5 with gap (any compact simple $G$) | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Global OS0--OS5 on $\mathbb R^4$ with positive mass gap | 1552-1558 | S0 | C0 |  |
| YM-0069 | theorem | `thm:nrc-global-Oa2` | Global operator-norm NRC with explicit $O(a^2)$ and $K(z)$ | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Uniform NRC and projectors in the large (global) | 1564-1574 | S0 | C0 |  |
| YM-0070 | corollary | `cor:projector-global` | Spectral projector convergence | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Uniform NRC and projectors in the large (global) | 1584-1590 | S0 | C0 |  |
| YM-0071 | theorem | `thm:os-wightman-export` | OS$\to$Wightman export | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / OS$\to$Wightman export (gap, Poincar\'e, microcausality, nontriviality) | 1593-1595 | S0 | C0 |  |
| YM-0072 | theorem | `thm:wightman-nongaussian` | Non-Gaussianity at the Wightman level | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / OS$\to$Wightman export (gap, Poincar\'e, microcausality, nontriviality) | 1600-1606 | S0 | C0 |  |
| YM-0073 | theorem | `thm:global-independence` | Unitary uniqueness and independence | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Independence and group generality | 1620-1622 | S0 | C0 |  |
| YM-0074 | remark | `unlabeled@L1636` | AF/Mosco | Global Continuum OS via Uniform Tightness and Isotropy (E1/E2) / Independence and group generality | 1636-1638 | S0 | C0 | remark (scan for hidden claims) |

### Core Continuum Chain (AF--free NRC Main Path)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0075 | theorem | `thm:NRC-allz` | Semigroup/resolvent control via AF--free NRC | Core Continuum Chain (AF--free NRC Main Path) / AF--free: Semigroup/Resolvent via NRC (Quantified, Local Hypotheses Only) | 1644-1655 | S0 | C0 |  |
| YM-0076 | definition | `def:Kz` | Resolvent constant | Core Continuum Chain (AF--free NRC Main Path) / AF--free: Semigroup/Resolvent via NRC (Quantified, Local Hypotheses Only) | 1691-1696 | S0 | C0 | definition (no proof) |
| YM-0077 | corollary | `cor:NRC-explicit` | NRC with explicit resolvent constant | Core Continuum Chain (AF--free NRC Main Path) / AF--free: Semigroup/Resolvent via NRC (Quantified, Local Hypotheses Only) | 1702-1710 | S0 | C0 |  |
| YM-0078 | lemma | `TS:ball_weight` | Local ball has large weight on fixed cores (one tick) -- explicit | Core Continuum Chain (AF--free NRC Main Path) / AF--free: Time-Slice $O(a^2)$ Control and NRC (Auxiliary Outline) | 1724-1740 | S0 | C0 |  |
| YM-0079 | lemma | `lem:moment-matching-kappa0` | Moment matching at the identity (fixes $\kappa_0(a)$) | Core Continuum Chain (AF--free NRC Main Path) / AF--free: Time-Slice $O(a^2)$ Control and NRC (Auxiliary Outline) | 1790-1807 | S0 | C0 |  |
| YM-0080 | theorem | `TS:sandwich_main` | Wilson heat--kernel sandwich on fixed cores with $O(a^2)$ control; auxiliary outline (not used in main chain) | Core Continuum Chain (AF--free NRC Main Path) / AF--free: Time-Slice $O(a^2)$ Control and NRC (Auxiliary Outline) | 1809-1822 | S0 | C0 | optional/not main-chain |
| YM-0081 | definition | `def:interface-kernel` | Interface sigma--algebra and kernel | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 1870-1879 | S0 | C0 | definition (no proof) |
| YM-0082 | lemma | `lem:interface-factorization` | Interface factorization | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 1880-1888 | S0 | C0 |  |
| YM-0083 | lemma | `lem:refresh-prob` | Refresh probability for near–identity cells; quantitative, $\beta$–explicit | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 1892-1898 | S0 | C0 | queued (needed for `prop:doeblin-full`) |
| YM-0084 | proposition | `prop:doeblin-interface` | Doeblin minorization on a fixed slab (DLR-quantified) | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 1899-1927 | S3 | C4 | audited; see “Proof writeups (audited)” |
| YM-0085 | corollary | `cor:hk-convex-split-explicit` | Heat--kernel convex split with explicit constants | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 1961-1975 | S3 | C4 | audited; TeX constant fixed 2025-12-20 |
| YM-0086 | proposition | `prop:iterated-minorization` | Iterated heat--kernel lower bound | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 1988-1994 | S0 | C0 |  |
| YM-0087 | lemma | `lem:abs-cont` | Absolute continuity on fixed regions; averaged and smoothed lower bounds | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 2011-2020 | S0 | C0 |  |
| YM-0088 | proposition | `prop:doeblin-full` | Doeblin minorization, multi--step refresh version | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 2029-2035 | S3 | C3 | now reduces to `lem:beta-L-independent-minorization`; see writeup |
| YM-0089 | proposition | `prop:embedding-independence-app` | Embedding–independence of continuum Schwinger functions | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 2044-2050 | S0 | C0 |  |
| YM-0090 | proposition | `prop:unitary-equivalence` | Unitary equivalence of continuum limits | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 2051-2053 | S0 | C0 |  |
| YM-0091 | proposition | `prop:bc-robust-app` | Boundary–condition robustness on van Hove boxes | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) | 2060-2062 | S0 | C0 |  |
| YM-0092 | corollary | `cor:scheme-independence` | Scheme independence up to unitary equivalence | Core Continuum Chain (AF--free NRC Main Path) / Interface kernel: rigorous definition and Doeblin proof (expanded) / Scheme Independence (Embeddings, Anisotropy, van Hove) | 2067-2069 | S0 | C0 |  |
| YM-0093 | theorem | `thm:gap-to-clustering` | Spectral gap $\Rightarrow$ exponential clustering | Core Continuum Chain (AF--free NRC Main Path) / Continuum chain | 2076-2081 | S0 | C0 |  |
| YM-0094 | theorem | `thm:clustering-to-gap` | Exponential clustering $\Rightarrow$ spectral gap | Core Continuum Chain (AF--free NRC Main Path) / Continuum chain | 2086-2092 | S0 | C0 |  |
| YM-0095 | theorem | `thm:gap-persist-cont` | Spectral gap persistence (AF--free, non – circular) | Core Continuum Chain (AF--free NRC Main Path) / Continuum chain | 2097-2111 | S3 | C4 | full proof via Riesz projections under operator-norm convergence of transfers (rank stability + contraction on $\Omega^\perp$) |
| YM-0096 | corollary | `cor:gap-persist-generator` | Generator formulation | Core Continuum Chain (AF--free NRC Main Path) / Continuum chain | 2138-2143 | S0 | C0 |  |
| YM-0097 | lemma | `lem:interface-smoothing` | Interface smoothing yields strictly positive continuous density | Core Continuum Chain (AF--free NRC Main Path) / Interface Smoothing and Uniform Sandwich / Notation for Interface Smoothing | 2152-2154 | S2 | C2 | proof sketch added in TeX; uniform lower bounds remain nontrivial (treat as external unless proved) |
| YM-0098 | lemma | `lem:ball-to-hk` | Small-ball convolution lower bounds the heat kernel | Core Continuum Chain (AF--free NRC Main Path) / Interface Smoothing and Uniform Sandwich / Notation for Interface Smoothing | 2156-2162 | S0 | C0 |  |
| YM-0099 | corollary | `cor:product-ball-to-hk` | Product form on interface blocks | Core Continuum Chain (AF--free NRC Main Path) / Interface Smoothing and Uniform Sandwich / Notation for Interface Smoothing | 2180-2186 | S0 | C0 |  |
| YM-0100 | proposition | `prop:sandwich` | Uniform sandwich after smoothing | Core Continuum Chain (AF--free NRC Main Path) / Interface Smoothing and Uniform Sandwich / Notation for Interface Smoothing | 2194-2199 | S2 | C1 | TeX now marks as “proof sketch / external input” (compact-group smoothing/minorization) |
| YM-0101 | theorem | `thm:AL-linear` | Area law $\Rightarrow$ linear confinement (finite--$T$ and asymptotic) | Core Continuum Chain (AF--free NRC Main Path) / Area Law: One-Way Consequences Only | 2208-2210 | S0 | C0 |  |
| YM-0102 | proposition | `prop:AL-torelon` | Area law $\Rightarrow$ torelon lower bound | Core Continuum Chain (AF--free NRC Main Path) / Area Law: One-Way Consequences Only | 2212-2214 | S0 | C0 |  |
| YM-0103 | proposition | `AL:gaussian-perimeter` | Gapped Gaussian abelian gauge field has perimeter law | Core Continuum Chain (AF--free NRC Main Path) / Area Law: One-Way Consequences Only | 2220-2227 | S0 | C0 |  |
| YM-0104 | theorem | `SurfNeg:neg-def` | Reflection negativity for T--odd surface curvature | Core Continuum Chain (AF--free NRC Main Path) / Local Reflection Negativity for Surface Curvature (Checkable Sign and Decay) | 2233-2239 | S0 | C0 |  |
| YM-0105 | proposition | `SurfNeg:exp-bound` | Exponential bound beyond a microscopic cutoff | Core Continuum Chain (AF--free NRC Main Path) / Local Reflection Negativity for Surface Curvature (Checkable Sign and Decay) | 2241-2247 | S0 | C0 |  |
| YM-0106 | lemma | `lem:interface-minorization-uniform` | Interface minorization uniform in $L$; $\beta$-uniform | Core Continuum Chain (AF--free NRC Main Path) / Local Reflection Negativity for Surface Curvature (Checkable Sign and Decay) / Group Generality | 2250-2260 | S0 | C0 |  |
| YM-0107 | corollary | `cor:convex-split` | Convex split and contraction | Core Continuum Chain (AF--free NRC Main Path) / Local Reflection Negativity for Surface Curvature (Checkable Sign and Decay) / Group Generality | 2274-2284 | S0 | C0 |  |
| YM-0108 | proposition | `prop:explicit-doeblin-constants` | Explicit boundary–uniform Doeblin constants and short-time scaling | Core Continuum Chain (AF--free NRC Main Path) / Local Reflection Negativity for Surface Curvature (Checkable Sign and Decay) / Group Generality | 2293-2312 | S0 | C0 |  |
| YM-0109 | lemma | `lem:hk-lower-explicit` | Short-time heat--kernel lower bound on compact groups | Core Continuum Chain (AF--free NRC Main Path) / Local Reflection Negativity for Surface Curvature (Checkable Sign and Decay) / Group Generality | 2314-2320 | S0 | C0 |  |
| YM-0110 | proposition | `prop:multistep-doeblin` | Multi-step scale-adapted Doeblin with explicit constants | Core Continuum Chain (AF--free NRC Main Path) / Local Reflection Negativity for Surface Curvature (Checkable Sign and Decay) / Group Generality | 2325-2342 | S0 | C0 |  |
| YM-0111 | corollary | `cor:uei-explicit-constants` | UEI with explicit constants | Core Continuum Chain (AF--free NRC Main Path) / Local Reflection Negativity for Surface Curvature (Checkable Sign and Decay) / Group Generality | 2350-2366 | S0 | C0 |  |
| YM-0112 | proposition | `prop:gap-to-cluster` | Gap $\Rightarrow$ clustering (uniform) | Core Continuum Chain (AF--free NRC Main Path) / Uniform gap $\Rightarrow$ uniform clustering; converse | 2373-2379 | S0 | C0 |  |
| YM-0113 | proposition | `prop:OS0-poly` | OS0 polynomial bounds with explicit constants | Core Continuum Chain (AF--free NRC Main Path) / Uniform gap $\Rightarrow$ uniform clustering; converse | 2381-2391 | S0 | C0 |  |
| YM-0114 | corollary | `cor:os0-explicit-4d` | OS0 with explicit constants in $d=4$ | Core Continuum Chain (AF--free NRC Main Path) / Uniform gap $\Rightarrow$ uniform clustering; converse | 2402-2412 | S0 | C0 |  |
| YM-0115 | proposition | `prop:cluster-to-gap` | Clustering on a generating local class $\Rightarrow$ gap | Core Continuum Chain (AF--free NRC Main Path) / Uniform gap $\Rightarrow$ uniform clustering; converse | 2417-2423 | S0 | C0 |  |
| YM-0116 | assumption | `assump:AF-Mosco` | AF/Mosco scaling framework (optional cross – check; not used in main chain) | Core Continuum Chain (AF--free NRC Main Path) / Uniform gap $\Rightarrow$ uniform clustering; converse | 2427-2442 | S0 | C0 | optional/not main-chain |
| YM-0117 | theorem | `thm:gap-persist` | Gap persistence via NRC | Core Continuum Chain (AF--free NRC Main Path) / Uniform gap $\Rightarrow$ uniform clustering; converse | 2443-2445 | S0 | C0 |  |
| YM-0118 | lemma | `lem:coarse-interface-construction` | Coarse interface at fixed physical resolution | Core Continuum Chain (AF--free NRC Main Path) / Coarse Interface and Dimension-Free Minorization | 2483-2485 | S2 | C3 | proof sketch added in TeX (geometry + $L^2$ projection) |
| YM-0119 | lemma | `lem:coarse-refresh` | Coarse refresh probability bound | Core Continuum Chain (AF--free NRC Main Path) / Coarse Interface and Dimension-Free Minorization | 2487-2489 | S2 | C2 | now cites explicit `lem:cell-disjoint-links` + `lem:plaquette-factorization` + the one-link *measure* minorization `lem:one-link-ball-minorization`; β-uniformity is still a blocker (constant is β-explicit) |
| YM-0120 | lemma | `lem:coarse-hk-domination` | Coarse heat – kernel domination | Core Continuum Chain (AF--free NRC Main Path) / Coarse Interface and Dimension-Free Minorization | 2491-2493 | S3 | C3 | now proved in TeX from `lem:ball-conv-lower` + tensorization (given the chosen form of `ν_ε`) |
| YM-0121 | lemma | `lem:lumping` | Lumping/data – processing for $L^2$ contraction | Core Continuum Chain (AF--free NRC Main Path) / Coarse Interface and Dimension-Free Minorization | 2509-2511 | S3 | C3 | proved in TeX (projection norm + compression argument) |
| YM-0122 | proposition | `prop:coarse-doeblin` | Coarse interface Doeblin | Core Continuum Chain (AF--free NRC Main Path) / Coarse Interface and Dimension-Free Minorization | 2528-2534 | S2 | C3 | proof sketch composes `lem:coarse-refresh` + `lem:coarse-hk-domination`; geometry step is now explicit via `lem:cell-disjoint-links` + `lem:plaquette-factorization` |
| YM-0123 | lemma | `lem:beta-L-independent-minorization` | \boldmath $\beta$ – and $L$ – independent slab minorization after coarse refresh | Core Continuum Chain (AF--free NRC Main Path) / Coarse Interface and Dimension-Free Minorization | 2572-2578 | S2 | C3 | now a clean corollary of `prop:coarse-doeblin`; remaining gap is the geometry/factorization step inside `lem:coarse-refresh` |
| YM-0124 | lemma | `lem:coarse-density` | Density of coarse interface observables as $\varepsilon\downarrow 0$ | Core Continuum Chain (AF--free NRC Main Path) / Coarse Interface and Dimension-Free Minorization | 2584-2600 | S3 | C4 | proved in TeX (standard $L^2$ martingale/conditional-expectation convergence; under explicit nesting hypothesis) |
| YM-0125 | corollary | `cor:odd-to-meanzero` | Odd$\to$mean-zero upgrade (eight ticks) | Core Continuum Chain (AF--free NRC Main Path) / Coarse Interface and Dimension-Free Minorization | 2602-2607 | S3 | C4 | rewritten as a restatement/pointer to `thm:eight-tick-uniform` (no coarse-density dependence) |
| YM-0126 | theorem | `thm:AL-gap` | Optional: Area law $+$ tube $\Rightarrow$ uniform gap | Core Continuum Chain (AF--free NRC Main Path) / Optional: Area Law $+$ Tube Geometry $\Rightarrow$ Uniform Gap (One-way) | 2569-2571 | S0 | C0 | optional/not main-chain |
| YM-0127 | proposition | `prop:anisotropy` | Aspect ratios and mild anisotropy | Core Continuum Chain (AF--free NRC Main Path) / Isotropy Restoration and Poincar\'e Invariance | 2578-2580 | S0 | C0 |  |
| YM-0128 | corollary | `cor:poincare` | Poincar\'e invariance via OS $\to$ Wightman | Core Continuum Chain (AF--free NRC Main Path) / Isotropy Restoration and Poincar\'e Invariance | 2585-2587 | S0 | C0 |  |

### Reflection positivity and transfer operator

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0129 | lemma | `lem:char-pd` | Irreducible characters are positive definite | Reflection positivity and transfer operator / Proof (Osterwalder--Seiler) | 2623-2628 | S3 | C4 | audited; see “Proof writeups (audited)” |
| YM-0130 | proposition | `prop:psd-crossing-gram` | PSD crossing Gram for Wilson link reflection | Reflection positivity and transfer operator / Proof (Osterwalder--Seiler) | 2637-2639 | S3 | C3 | audited; see “Proof writeups (audited)” |
| YM-0131 | lemma | `lem:os-gns-transfer` | OS/GNS transfer properties | Reflection positivity and transfer operator / Proof (Osterwalder--Seiler) | 2673-2675 | S3 | C4 | audited; see “Proof writeups (audited)” |

### Strong-coupling contraction and mass gap

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0132 | prop | `prop:dob-spectrum` | Dobrushin coefficient controls spectral radius | Strong-coupling contraction and mass gap | 2697-2703 | S0 | C0 |  |
| YM-0133 | lemma | `lem:dob-influence` | Explicit Dobrushin influence bound | Strong-coupling contraction and mass gap | 2707-2713 | S0 | C0 |  |

### Optional: Continuum scaling-window routes (KP/area-law; not used in main chain)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0134 | theorem | `eq:continuum-bound` | Let $\Gamma\subset\mathbb{R}^d$ be a rectifiable closed curve with $\mathsf{Area}(\Gamma)<\infty$. Assume the uniform la | Optional: Continuum scaling-window routes (KP/area-law; not used in main chain) / Optional A: Uniform lattice area law implies a continuum string tension | 2804-2820 | S0 | C0 |  |

### Global continuum construction on $\mathbb R^4$ and OS axioms

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0135 | proposition | `prop:consistency-overlaps` | Consistency on overlaps | Global continuum construction on $\mathbb R^4$ and OS axioms / Directed van Hove exhaustions and cylinder algebras | 2853-2863 | S0 | C0 |  |
| YM-0136 | theorem | `thm:proj-semigroup` | Projective-limit $C_0$-semigroup and generator on $\mathbb R^4$ | Global continuum construction on $\mathbb R^4$ and OS axioms / Directed van Hove exhaustions and cylinder algebras | 2865-2879 | S0 | C0 |  |
| YM-0137 | lemma | `lem:overlap-quant` | Quantitative consistency on overlaps | Global continuum construction on $\mathbb R^4$ and OS axioms / Directed van Hove exhaustions and cylinder algebras | 2884-2890 | S0 | C0 |  |
| YM-0138 | lemma | `lem:link-minorization` | Uniform positivity of single-link conditionals | Global continuum construction on $\mathbb R^4$ and OS axioms / No-go: Schedule-Independent Local Limits on Fixed Regions are Trivial | 2901-2906 | S0 | C0 |  |
| YM-0139 | proposition | `prop:plaq-away` | Plaquette away from identity at any fixed finite $\beta$ | Global continuum construction on $\mathbb R^4$ and OS axioms / No-go: Schedule-Independent Local Limits on Fixed Regions are Trivial | 2908-2913 | S0 | C0 |  |
| YM-0140 | lemma | `lem:large-beta` | Large-$\beta$ concentration on a finite set of plaquettes | Global continuum construction on $\mathbb R^4$ and OS axioms / No-go: Schedule-Independent Local Limits on Fixed Regions are Trivial | 2915-2921 | S0 | C0 |  |
| YM-0141 | theorem | `U4D:no-go` | No schedule-independent local limit unless trivial | Global continuum construction on $\mathbb R^4$ and OS axioms / No-go: Schedule-Independent Local Limits on Fixed Regions are Trivial | 2923-2931 | S0 | C0 |  |
| YM-0142 | definition | `def:beta-schedule` | AF-style schedule | Global continuum construction on $\mathbb R^4$ and OS axioms / Explicit AF-Style Scaling $\beta(a)$ and Tightness/Convergence | 2941-2947 | S0 | C0 | definition (no proof) |
| YM-0143 | theorem | `thm:tightness-beta` | Tightness and convergence along $\beta(a)$ | Global continuum construction on $\mathbb R^4$ and OS axioms / Explicit AF-Style Scaling $\beta(a)$ and Tightness/Convergence | 2951-2953 | S0 | C0 |  |
| YM-0144 | corollary | `cor:global-convergence` | Convergence on $\mathbb R^4$ | Global continuum construction on $\mathbb R^4$ and OS axioms / Explicit AF-Style Scaling $\beta(a)$ and Tightness/Convergence | 2958-2960 | S0 | C0 |  |
| YM-0145 | corollary | `cor:scheme-independence-global` | Scheme and embedding independence; unitary equivalence | Global continuum construction on $\mathbb R^4$ and OS axioms / Explicit AF-Style Scaling $\beta(a)$ and Tightness/Convergence | 2962-2964 | S0 | C0 |  |
| YM-0146 | theorem | `thm:af-free-calibrated` | AF-free calibrated NRC and uniqueness | Global continuum construction on $\mathbb R^4$ and OS axioms / AF-Free Calibrated NRC Alternative | 2973-2975 | S0 | C0 |  |
| YM-0147 | theorem | `thm:kolmogorov-global` | Kolmogorov/Minlos extension to a global Euclidean measure | Global continuum construction on $\mathbb R^4$ and OS axioms / AF-Free Calibrated NRC Alternative | 2980-2982 | S0 | C0 |  |
| YM-0148 | lemma | `lem:rp-stability-projective` | Reflection positivity stability under directed cylinder limits | Global continuum construction on $\mathbb R^4$ and OS axioms / Global OS Axioms on $\mathbb R^4$ | 2991-2997 | S0 | C0 |  |
| YM-0149 | lemma | `lem:separable` | Separable global OS/GNS Hilbert space | Global continuum construction on $\mathbb R^4$ and OS axioms / Global OS Axioms on $\mathbb R^4$ | 3002-3004 | S0 | C0 |  |
| YM-0150 | proposition | `prop:haag-kastler` | Haag--Kastler net on $\mathbb R^4$ | Global continuum construction on $\mathbb R^4$ and OS axioms / Global OS Axioms on $\mathbb R^4$ | 3009-3016 | S0 | C0 |  |
| YM-0151 | theorem | `thm:global-OS` | Global OS0--OS5 (conditional on fixed-region U1/OS1 inputs; AF--free NRC) | Global continuum construction on $\mathbb R^4$ and OS axioms / Global OS Axioms on $\mathbb R^4$ | 3021-3031 | S0 | C0 |  |
| YM-0152 | lemma | `lem:unique-vacuum` | Unique vacuum from global clustering and reflection positivity | Global continuum construction on $\mathbb R^4$ and OS axioms / Global OS Axioms on $\mathbb R^4$ | 3032-3038 | S0 | C0 |  |
| YM-0153 | lemma | `lem:group-avg` | Compact-group averaging preserves OS axioms and gap | Global continuum construction on $\mathbb R^4$ and OS axioms / Global OS Axioms on $\mathbb R^4$ | 3042-3044 | S0 | C0 |  |
| YM-0154 | theorem | `thm:os-to-wightman-global` | OS reconstruction and Poincar\'e invariance (conditional on OS0--OS5; any compact simple $G$) | Global continuum construction on $\mathbb R^4$ and OS axioms / OS $\to$ Wightman and Global Mass Gap | 3050-3052 | S0 | C0 |  |
| YM-0155 | lemma | `lem:finite-upper-gap` | Finite upper gap $m<\infty$ | Global continuum construction on $\mathbb R^4$ and OS axioms / OS $\to$ Wightman and Global Mass Gap | 3053-3055 | S0 | C0 |  |
| YM-0156 | theorem | `thm:wightman-axioms` | Wightman axioms and spectral condition (conditional on OS0--OS5) | Global continuum construction on $\mathbb R^4$ and OS axioms / OS $\to$ Wightman and Global Mass Gap | 3064-3073 | S0 | C0 |  |
| YM-0157 | corollary | `cor:microcausality` | Microcausality for gauge -- invariant local fields | Global continuum construction on $\mathbb R^4$ and OS axioms / OS $\to$ Wightman and Global Mass Gap | 3078-3084 | S0 | C0 |  |
| YM-0158 | lemma | `lem:inductive-spectral` | Inductive-limit spectral transfer | Global continuum construction on $\mathbb R^4$ and OS axioms / Global Spectral Gap on $\mathbb R^4$ | 3091-3106 | S0 | C0 |  |
| YM-0159 | theorem | `thm:global-gap-uncond` | Global Euclidean spectral gap, boundary/region independent (any compact simple $G$) | Global continuum construction on $\mathbb R^4$ and OS axioms / Global Spectral Gap on $\mathbb R^4$ | 3117-3127 | S0 | C0 |  |
| YM-0160 | corollary | `cor:minkowski-massgap` | Physical Minkowski mass gap | Global continuum construction on $\mathbb R^4$ and OS axioms / Global Spectral Gap on $\mathbb R^4$ | 3144-3150 | S0 | C0 |  |
| YM-0161 | theorem | `thm:clay-compliance` | Clay–Jaffe–Witten compliance: existence and mass gap on $\mathbb R^4$ (any compact simple $G$) | Global continuum construction on $\mathbb R^4$ and OS axioms / Global Spectral Gap on $\mathbb R^4$ | 3152-3163 | S0 | C0 |  |
| YM-0162 | lemma | `lem:os-continuum` | OS0--OS5 in the continuum limit | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3185-3204 | S0 | C0 |  |
| YM-0163 | corollary | `cor:os-assumptions-verified` | Verification of OS0--OS5 assumptions in this manuscript | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3205-3213 | S0 | C0 |  |
| YM-0164 | corollary | `cor:scaled-continuum-gap` | Finite continuum gap via scaled minorization (Mosco/AF cross-check; not used in main chain) | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3218-3224 | S0 | C0 | optional/not main-chain |
| YM-0165 | lemma | `lem:eqc-modulus` | Equicontinuity modulus on fixed regions | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3226-3234 | S0 | C0 |  |
| YM-0166 | proposition | `prop:af-free-uniqueness` | AF-free uniqueness of Schwinger limits | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3259-3264 | S0 | C0 |  |
| YM-0167 | proposition | `prop:embedding-independence` | Embedding–independence of continuum Schwinger functions | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3266-3272 | S0 | C0 |  |
| YM-0168 | proposition | `prop:bc-robust` | Boundary–condition robustness on van Hove boxes | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3277-3279 | S0 | C0 |  |
| YM-0169 | lemma | `lem:isotropy-restore` | Isotropy restoration via heat--kernel calibrators | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3284-3289 | S0 | C0 |  |
| YM-0170 | lemma | `lem:os1-embedding` | OS1 without calibrators: embedding–independence route | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3291-3302 | S0 | C0 |  |
| YM-0171 | corollary | `cor:os1-rotations` | OS1 (rotations) in the continuum limit | Global continuum construction on $\mathbb R^4$ and OS axioms / Optional B: Continuum OS reconstruction from a scaling window | 3303-3305 | S0 | C0 |  |
| YM-0172 | theorem | `thm:c1-consolidated` | Fix a scaling window $\varepsilon\in(0,\varepsilon_0]$ and consider lattice Wilson measures $\mu_\varepsilon$ with a fix | Global continuum construction on $\mathbb R^4$ and OS axioms / Consolidated continuum existence (C1) | 3317-3326 | S0 | C0 |  |
| YM-0173 | theorem | `thm:preview-continuum-existence` | On $\mathbb R^4$, there exists a probability measure on loop configurations whose Schwinger functions satisfy OS0--OS5.  | Global continuum construction on $\mathbb R^4$ and OS axioms / Preview: pointer to the Main Theorem | 3336-3348 | S0 | C0 |  |

### Infinite volume at fixed spacing

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0174 | theorem | `thm:thermo-strong` | Thermodynamic limit with uniform gap | Infinite volume at fixed spacing | 3363-3365 | S0 | C0 |  |

### Appendix: Parity--Oddness and One--Step Contraction (TP)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0175 | lemma | `lem:oddness-tp` | Parity--oddness on the local cone | Appendix: Parity--Oddness and One--Step Contraction (TP) | 3376-3378 | S0 | C0 |  |
| YM-0176 | lemma | `lem:odd-contraction-tp` | One--step contraction on odd cone | Appendix: Parity--Oddness and One--Step Contraction (TP) | 3390-3404 | S0 | C0 |  |
| YM-0177 | theorem | `thm:tp-bound` | Tick--Poincar\'e bound | Appendix: Parity--Oddness and One--Step Contraction (TP) | 3409-3415 | S0 | C0 |  |

### Appendix: Tree--Gauge UEI (Uniform Exponential Integrability)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0178 | theorem | `thm:uei-fixed-region` | U1 on fixed regions: tightness/UEI (two closure routes; target) | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) | 3418-3423 | S0 | C0 |  |
| YM-0179 | corollary | `cor:uei-af-uniform` | Uniform UEI/tightness along AF scaling (conditional) | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) | 3424-3426 | S0 | C0 |  |
| YM-0180 | lemma | `lem:hessian-lower-chords` | Explicit Hessian lower bound on chords | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) | 3447-3457 | S0 | C0 |  |
| YM-0181 | proposition | `prop:os0os2-closure` | OS0/OS2 closure under limits | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) | 3495-3501 | S3 | C3 | proof tightened; OS2 stability under cylinder weak convergence made explicit; OS0 transfer explicitly conditional on uniform OS0 polynomial bounds |
| YM-0182 | corollary | `cor:os2-pass` | OS2 passes to the continuum under AF/Mosco | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) | 3507-3509 | S0 | C0 |  |
| YM-0183 | proposition | `prop:os35-limit` | OS3/OS5 in the continuum limit | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) | 3511-3517 | S0 | C0 |  |
| YM-0184 | theorem | `thm:emergent-sym` | Symmetry emerges from uniform $O(a^2)$ commutator control | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) / Calibrator -- free isotropy via approximate symmetry and NRC | 3532-3547 | S0 | C0 |  |
| YM-0185 | lemma | `lem:local-commutator-Oa2` | Local $O(a^2)$ E(4) -- commutator bound on fixed regions | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) / Calibrator -- free isotropy via approximate symmetry and NRC | 3564-3570 | S0 | C0 |  |
| YM-0186 | proposition | `prop:resolvent-from-commutator` | Resolvent conjugation from semigroup commutators | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) / Calibrator -- free isotropy via approximate symmetry and NRC | 3585-3591 | S0 | C0 |  |
| YM-0187 | theorem | `thm:os1-unconditional` | OS1 on fixed regions (conditional; calibrator route) | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) / Calibrator -- free isotropy via approximate symmetry and NRC | 3596-3606 | S0 | C0 |  |
| YM-0188 | proposition | `prop:hk-calibrators-constructed` | Hypercubic – equivariant isotropic calibrators; construction | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) / Calibrator -- free isotropy via approximate symmetry and NRC | 3612-3618 | S0 | C0 |  |
| YM-0189 | theorem | `thm:os1-calibrator-route` | OS1 via calibrated equicontinuity (constructed) | Appendix: Tree--Gauge UEI (Uniform Exponential Integrability) / Calibrator -- free isotropy via approximate symmetry and NRC | 3623-3629 | S0 | C0 |  |

### Norm--Resolvent Convergence via Embeddings and Resolvent Comparison

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0190 | theorem | `thm:strong-semigroup-core` | Strong semigroup convergence on a core | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3653-3659 | S0 | C0 |  |
| YM-0191 | proposition | `prop:collective-compactness` | Collective compactness calibrator | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3664-3670 | S0 | C0 |  |
| YM-0192 | theorem | `thm:nrc-operator-norm` | Operator-norm NRC via collective compactness | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3675-3684 | S0 | C0 |  |
| YM-0193 | theorem | `thm:nrc-embeddings` | NRC for all nonreal $z$ along a scaling sequence | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3689-3695 | S0 | C0 |  |
| YM-0194 | lemma | `lem:af-free-cauchy` | AF-free resolvent Cauchy criterion on a nonreal compact | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3698-3716 | S0 | C0 |  |
| YM-0195 | proposition | `prop:resolvent-comparison` | Resolvent comparison identity and domains | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3732-3739 | S0 | C0 |  |
| YM-0196 | proposition | `lem:graph-defect-Oa` | graph--defect $O(a)$ on fixed slabs: form-level criterion | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3743-3761 | S0 | C0 |  |
| YM-0197 | lemma | `lem:U2-electric` | Electric graph--defect $O(a)$ | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3776-3790 | S0 | C0 |  |
| YM-0198 | lemma | `lem:U2-magnetic` | Magnetic graph--defect $O(a)$ | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3792-3810 | S0 | C0 |  |
| YM-0199 | theorem | `thm:U2` | U2 on fixed slabs: graph--defect $O(a)$ and low--energy projectors | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3812-3828 | S0 | C0 |  |
| YM-0200 | corollary | `lem:low-energy-proj` | Low--energy projector via contour; unconditional | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3830-3836 | S0 | C0 |  |
| YM-0201 | theorem | `thm:nrc-quant` | Quantitative operator-norm NRC for all nonreal $z$ | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3862-3868 | S0 | C0 |  |
| YM-0202 | lemma | `lem:cauchy-resolvent-unique` | Cauchy criterion for embedded resolvents; uniqueness | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3870-3876 | S0 | C0 |  |
| YM-0203 | corollary | `cor:unique-schwinger-local` | Unique Schwinger limits for local fields | Norm--Resolvent Convergence via Embeddings and Resolvent Comparison / Cores and Consistency | 3888-3890 | S0 | C0 |  |

### Appendix: Spectral gap persistence in the continuum

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0204 | lemma | `lem:riesz-gap` | Riesz projection stability and gap persistence | Appendix: Spectral gap persistence in the continuum | 3907-3927 | S0 | C0 |  |
| YM-0205 | theorem | `thm:gap-persist-nrc` | Gap persistence under NRC | Appendix: Spectral gap persistence in the continuum | 3936-3946 | S0 | C0 |  |

### OS $\to$ Wightman Reconstruction and Mass Gap in Minkowski Space

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0206 | theorem | `thm:abstract-discretization` | Abstract interface discretization to continuum generator | OS $\to$ Wightman Reconstruction and Mass Gap in Minkowski Space / Abstract Reversible Discretization $\Rightarrow$ Resolvent Limit and $O(a)$ Defect | 3956-3974 | S0 | C0 |  |
| YM-0207 | theorem | `thm:os-to-wightman` | OS $\to$ Wightman export with mass gap | OS $\to$ Wightman Reconstruction and Mass Gap in Minkowski Space / Abstract Reversible Discretization $\Rightarrow$ Resolvent Limit and $O(a)$ Defect | 3977-3982 | S0 | C0 |  |

### Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade))

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0208 | theorem | `thm:main-af-free` | Continuum YM on $\mathbb R^4$ with OS0--OS5 and positive mass gap (conditional on U1/OS1/NRC inputs) | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Proof Strategy | 4019-4025 | S0 | C0 |  |
| YM-0209 | corollary | `cor:nonGaussian-main` | Non-Gaussianity of the continuum local fields | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Proof Strategy | 4039-4045 | S0 | C0 |  |
| YM-0210 | theorem | `thm:global-os-clay` | Clay–critical Global OS pack on $\mathbb R^4$ (OS0--OS5, explicit constants) | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Proof Strategy | 4058-4076 | S0 | C0 |  |
| YM-0211 | theorem | `thm:global-nrc-clay` | Uniform global NRC with explicit constants; spectral projectors | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Proof Strategy | 4078-4090 | S0 | C0 |  |
| YM-0212 | theorem | `thm:gap-wightman-clay` | Gap persistence, OS$\to$Wightman, microcausality and nontriviality | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Proof Strategy | 4092-4100 | S0 | C0 |  |
| YM-0213 | theorem | `thm:independence-clay` | Group generality and global independence/uniqueness | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Proof Strategy | 4102-4109 | S0 | C0 |  |
| YM-0214 | corollary | `cor:global-uniform-gap` | Global $\beta$- and volume-uniform mass-gap bound | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Clay-Style Constants Checklist (for Theorem~\ref{thm:main-af-free | 4134-4147 | S0 | C0 |  |
| YM-0215 | theorem | `thm:global-minkowski-gap` | Global Minkowski mass gap (explicit constant; conditional) | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Clay-Style Constants Checklist (for Theorem~\ref{thm:main-af-free | 4149-4160 | S0 | C0 |  |
| YM-0216 | lemma | `lem:local-fields-tempered` | Local gauge -- invariant fields are tempered distributions | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Local gauge -- invariant fields: definition and temperedness / Discretized Local Fields and Smearings | 4184-4187 | S0 | C0 |  |
| YM-0217 | definition | `def:FR` | Renormalized curvature two -- form | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Local gauge -- invariant fields: definition and temperedness / Discretized Local Fields and Smearings | 4189-4196 | S0 | C0 | definition (no proof) |
| YM-0218 | lemma | `lem:FR-tempered` | Existence, temperedness, and covariance of $F^R_{\mu\nu}$ | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Local gauge -- invariant fields: definition and temperedness / Discretized Local Fields and Smearings | 4198-4204 | S0 | C0 |  |
| YM-0219 | corollary | `cor:locality-FR` | Locality for gauge – invariant smearings of $F^R$ | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Local gauge -- invariant fields: definition and temperedness / Discretized Local Fields and Smearings | 4219-4221 | S0 | C0 |  |
| YM-0220 | lemma | `lem:field-core` | Density and invariance of $\mathcal D_{\rm loc}$ | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Operator domains, common cores, and BRST / Common Invariant Core for Local Operators | 4234-4241 | S0 | C0 |  |
| YM-0221 | proposition | `prop:field-closability` | Field closability and relative graph bounds | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Operator domains, common cores, and BRST / Closability and Graph Bounds for Smeared Fields | 4248-4255 | S0 | C0 |  |
| YM-0222 | definition | `def:brst` | BRST charge on $\mathcal D_{\rm loc}$ | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Operator domains, common cores, and BRST / Closability and Graph Bounds for Smeared Fields | 4263-4265 | S0 | C0 | definition (no proof) |
| YM-0223 | proposition | `prop:brst-closable` | Closability, nilpotency, and core for $Q$ | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Operator domains, common cores, and BRST / Closability and Graph Bounds for Smeared Fields | 4267-4273 | S0 | C0 |  |
| YM-0224 | proposition | `prop:physical-hilbert` | Physical Hilbert space | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Operator domains, common cores, and BRST / Closability and Graph Bounds for Smeared Fields | 4278-4280 | S0 | C0 |  |
| YM-0225 | corollary | `cor:os-local-fields` | OS axioms for local fields | Main Theorem (Continuum YM with Mass Gap; AF--free NRC with UEI/OS1 Inputs (RG-grade)) / Operator domains, common cores, and BRST / Closability and Graph Bounds for Smeared Fields | 4294-4297 | S0 | C0 |  |

### Continuum gauge symmetry, Gauss law, and BRST

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0226 | theorem | `thm:unitary-gauge` | Unitary representation of $\mathcal G_0$ | Continuum gauge symmetry, Gauss law, and BRST / Unitary implementation of the local gauge group | 4308-4314 | S0 | C0 |  |
| YM-0227 | theorem | `thm:gauss-generators` | Self – adjoint Gauss generators | Continuum gauge symmetry, Gauss law, and BRST / Gauss – law generators and physical subspace | 4321-4331 | S0 | C0 |  |
| YM-0228 | definition | `unlabeled@L4335` | Physical subspace | Continuum gauge symmetry, Gauss law, and BRST / Gauss – law generators and physical subspace | 4335-4337 | S0 | C0 | definition (no proof) |
| YM-0229 | theorem | `prop:gauss-phys` | Gauss law and gauge – invariant algebra | Continuum gauge symmetry, Gauss law, and BRST / Gauss – law generators and physical subspace | 4339-4341 | S0 | C0 |  |
| YM-0230 | theorem | `thm:ward` | Nonabelian Ward identities | Continuum gauge symmetry, Gauss law, and BRST / Ward identities (continuum, nonabelian) | 4348-4357 | S0 | C0 |  |
| YM-0231 | theorem | `thm:ovd` | Closability and common core | Continuum gauge symmetry, Gauss law, and BRST / Local gauge – invariant Wightman fields as operator – valued distributions | 4364-4366 | S0 | C0 |  |
| YM-0232 | theorem | `thm:brst` | BRST cohomology at ghost number zero | Continuum gauge symmetry, Gauss law, and BRST / Optional: BRST cohomology equals Gauss – law invariants | 4375-4381 | S0 | C0 |  |
| YM-0233 | corollary | `cor:microcausality-smeared` | Microcausality for smeared gauge -- invariant fields | Continuum gauge symmetry, Gauss law, and BRST / Optional: BRST cohomology equals Gauss – law invariants | 4386-4393 | S0 | C0 |  |
| YM-0234 | lemma | `lem:nontrivial-variance` | Nontriviality: positive variance of a smeared local field | Continuum gauge symmetry, Gauss law, and BRST / Optional: BRST cohomology equals Gauss – law invariants | 4399-4409 | S0 | C0 |  |

### Appendix: Constants and References Index

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0235 | lemma | `lem:cylinder-projective` | Cylinder measurability and projective limit | Appendix: Constants and References Index | 4449-4457 | S0 | C0 |  |
| YM-0236 | corollary | `cor:continuum-measure-exists` | Continuum measure on loop/local cylinders | Appendix: Constants and References Index | 4461-4463 | S0 | C0 |  |

### Clay compliance checklist

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0237 | theorem | `thm:af-mosco-crosscheck` | AF/Mosco cross – check | Clay compliance checklist / Appendix reference: AF/Mosco cross – check \emph{(not used in main chain) | 4506-4508 | S0 | C0 |  |
| YM-0238 | theorem | `thm:cont-exp-cluster` | Exponential clustering in the continuum | Clay compliance checklist / Appendix reference: AF/Mosco cross – check \emph{(not used in main chain) | 4510-4516 | S0 | C0 |  |

### Dobrushin Contraction and Spectrum (Finite Dimension)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0239 | theorem | `thm:dobrusin-spectrum-finite` | Let $P$ be an $N\times N$ stochastic matrix. Its total-variation Dobrushin coefficient is | Dobrushin Contraction and Spectrum (Finite Dimension) | 4570-4581 | S0 | C0 |  |

### Uniform Two-Layer Gram Deficit on the Odd Cone

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0240 | lemma | `lem:local-basis-growth` | Local odd basis and growth control | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4608-4618 | S0 | C0 |  |
| YM-0241 | lemma | `lem:local-gram-bounds` | Local OS Gram bounds (OS-normalized basis) | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4626-4632 | S0 | C0 |  |
| YM-0242 | lemma | `lem:locality-one-tick` | Locality of one--tick transfer on the slab | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4638-4644 | S0 | C0 |  |
| YM-0243 | lemma | `lem:odd-cone-embedding` | Odd--cone interface embedding | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4650-4659 | S0 | C0 |  |
| YM-0244 | lemma | `lem:mixed-gram-bound` | One--step mixed Gram bound | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4671-4681 | S0 | C0 |  |
| YM-0245 | lemma | `lem:diag-mixed-bound` | Diagonal mixed Gram contraction | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4704-4710 | S0 | C0 |  |
| YM-0246 | proposition | `prop:two-layer-deficit` | Uniform two--layer deficit | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4720-4734 | S0 | C0 |  |
| YM-0247 | corollary | `cor:deficit-c-cut` | Deficit $\Rightarrow$ contraction and $c_{\rm cut}$ | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4762-4764 | S0 | C0 |  |
| YM-0248 | theorem | `thm:two-layer-explicit` | Two-layer deficit with explicit constants $\beta_0$ and $c_{\rm cut}$ | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4765-4779 | S0 | C0 |  |
| YM-0249 | lemma | `lem:local-span-dense` | Time-zero local span is dense in $\Omega^{\perp}$ | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4788-4794 | S0 | C0 |  |
| YM-0250 | lemma | `lem:local-core` | Local core for $H$ | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4800-4806 | S0 | C0 |  |
| YM-0251 | theorem | `thm:pf-gap-meanzero` | Perron--Frobenius gap on $\Omega^{\perp}$ | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4813-4824 | S0 | C0 |  |
| YM-0252 | corollary | `cor:best-of-two` | Best--of--two lattice gap | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4862-4872 | S0 | C0 |  |
| YM-0253 | lemma | `lem:hk-contraction` | Heat--kernel contraction on mean-zero | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4923-4929 | S0 | C0 |  |
| YM-0254 | lemma | `lem:ball-conv-lower` | Small-ball convolution dominates a heat kernel | Uniform Two-Layer Gram Deficit on the Odd Cone / Setup | 4955-4961 | S0 | C0 |  |

### Appendix: Tightness, convergence, and OS0/OS1 (C1a)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0255 | theorem | `thm:c1a-tight` | Tightness and unique convergence of loop $n$-point functions | Appendix: Tightness, convergence, and OS0/OS1 (C1a) | 5131-5133 | S0 | C0 |  |
| YM-0256 | proposition | `prop:c1a-os0os1` | OS0 and OS1 | Appendix: Tightness, convergence, and OS0/OS1 (C1a) | 5137-5139 | S0 | C0 |  |
| YM-0257 | theorem | `thm:nrc-explicit` | NRC for all nonreal $z$ | Appendix: Tightness, convergence, and OS0/OS1 (C1a) | 5148-5153 | S0 | C0 |  |
| YM-0258 | lemma | `lem:os0-explicit-constants` | OS0 (temperedness) with explicit constants | Appendix: Tightness, convergence, and OS0/OS1 (C1a) | 5172-5189 | S0 | C0 |  |

### Appendix: OS2 and OS3/OS5 preserved in the limit (C1b)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0259 | lemma | `lem:os2-limit` | OS2 preserved under limits | Appendix: OS2 and OS3/OS5 preserved in the limit (C1b) | 5202-5208 | S3 | C4 | proof reduced to: OS2 positivity on each lattice + cylinder weak convergence ⇒ OS2 in the limit (no undefined approximants) |
| YM-0260 | lemma | `lem:os3-limit` | OS3: clustering in the limit | Appendix: OS2 and OS3/OS5 preserved in the limit (C1b) | 5239-5244 | S3 | C3 | proof tightened: pass covariance bound to the limit at fixed translation; no limit-interchange handwave |
| YM-0261 | lemma | `lem:os5-limit` | OS5: unique vacuum in the limit | Appendix: OS2 and OS3/OS5 preserved in the limit (C1b) | 5257-5262 | S2 | C2 | refactored to cite gap persistence (`thm:gap-persist-cont`) + projector-rank stability under NRC/norm-resolvent convergence; could be expanded with a Kato theorem-number citation for projector stability |

### Appendix: Embeddings, norm--resolvent convergence, and continuum gap (C1c)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0262 | lemma | `lem:semigroup-defect` | Semigroup comparison implies graph–norm defect | Appendix: Embeddings, norm--resolvent convergence, and continuum gap (C1c) | 5294-5300 | S0 | C0 |  |
| YM-0263 | lemma | `lem:compact-calibrator` | Compact calibrator in finite volume | Appendix: Embeddings, norm--resolvent convergence, and continuum gap (C1c) | 5317-5319 | S0 | C0 |  |
| YM-0264 | theorem | `thm:nrc-exhaustion` | NRC via finite–volume exhaustion | Appendix: Embeddings, norm--resolvent convergence, and continuum gap (C1c) | 5330-5336 | S0 | C0 |  |
| YM-0265 | theorem | `thm:nrc-gap` | NRC and continuum gap | Appendix: Embeddings, norm--resolvent convergence, and continuum gap (C1c) | 5338-5351 | S0 | C0 |  |

### Optional: Asymptotic-freedom scaling and unique projective limit (C1d)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0266 | lemma | `lem:cauchy-res` | Cauchy estimate for embedded resolvents | Optional: Asymptotic-freedom scaling and unique projective limit (C1d) | 5390-5395 | S0 | C0 |  |
| YM-0267 | theorem | `thm:af-schedule-gap` | AF schedule $\Rightarrow$ unique continuum YM with gap | Optional: Asymptotic-freedom scaling and unique projective limit (C1d) | 5406-5411 | S0 | C0 |  |

### Appendix: Continuum area law via directed embeddings (C2; one-way consequences only)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0268 | theorem | `thm:continuum-area-perimeter` | Continuum Area–Perimeter bound | Appendix: Continuum area law via directed embeddings (C2; one-way consequences only) | 5428-5434 | S0 | C0 |  |

### Optional Appendix: $\varepsilon$–uniform cluster expansion along a scaling trajectory (C3)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0269 | theorem | `thm:uniform-kp` | Uniform KP/cluster expansion with explicit constants | Optional Appendix: $\varepsilon$–uniform cluster expansion along a scaling trajectory (C3) | 5481-5500 | S0 | C0 |  |
| YM-0270 | theorem | `thm:local-fields-exist` | Local gauge–invariant fields | Optional Appendix: $\varepsilon$–uniform cluster expansion along a scaling trajectory (C3) | 5503-5505 | S0 | C0 |  |
| YM-0271 | corollary | `cor:wightman-local-gap` | OS $\to$ Wightman with local fields and gap | Optional Appendix: $\varepsilon$–uniform cluster expansion along a scaling trajectory (C3) | 5507-5512 | S0 | C0 |  |

### Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0272 | lemma | `lem:lattice-brst-ward` | Lattice BRST/finite-gauge Ward identities | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U8. Ward/Schwinger–Dyson identities and continuum Ward theorem | 5552-5554 | S0 | C0 |  |
| YM-0273 | theorem | `thm:U8-ward-cont` | Continuum nonabelian Ward identities | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U8. Ward/Schwinger–Dyson identities and continuum Ward theorem | 5566-5568 | S0 | C0 |  |
| YM-0274 | theorem | `thm:U9-gauss` | Gauss constraint and physical subspace | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U9. Gauss law and the physical Hilbert subspace | 5573-5575 | S0 | C0 |  |
| YM-0275 | theorem | `thm:U10-renorm-F` | Existence of renormalized $F_{\mu\nu}$ | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U10. Renormalized local fields (tempered, nontrivial) | 5581-5583 | S0 | C0 |  |
| YM-0276 | proposition | `prop:U11-os4` | OS4: permutation symmetry | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U11. OS4 (permutation symmetry) explicit | 5589-5591 | S0 | C0 |  |
| YM-0277 | theorem | `thm:U12-exp-cluster` | Exponential clustering | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U12. Exponential clustering in the continuum | 5596-5602 | S0 | C0 |  |
| YM-0278 | definition | `def:U0-schedule` | Scaling schedule and volumes | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U0. Concrete scaling schedule and van Hove volumes | 5608-5614 | S0 | C0 | definition (no proof) |
| YM-0279 | remark | `unlabeled@L5615` | Scope note: U2 geometric inputs aim to be uniform in $(a,L)$, while U1 is RG-grade and only claimed along weak-coupling schedules | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U0. Concrete scaling schedule and van Hove volumes | 5615-5617 | S0 | C0 | remark (scan for hidden claims) |
| YM-0280 | theorem | `thm:U1-lsi-uei` | Local LSI/UEI on fixed regions | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U1. Local LSI/UEI on fixed regions (sources: Holley--Stroock, Bakry--\'Emery, Wang) | 5620-5638 | S0 | C0 |  |
| YM-0281 | remark | `rem:uei-explicit-downstream` | Explicit constants for downstream bounds | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U1. Local LSI/UEI on fixed regions (sources: Holley--Stroock, Bakry--\'Emery, Wang) | 5639-5650 | S0 | C0 | remark (scan for hidden claims) |
| YM-0282 | lemma | `lem:su2-heat-lsi` | LSI for single--site heat kernel on $\mathrm{SU}(2)$ | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / Positive-time heat-smoothing: uniform LSI and RG stability (SU(2)) | 5663-5669 | S0 | C0 |  |
| YM-0283 | proposition | `prop:su2-lsi-tensor` | Tensorization on products | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / Positive-time heat-smoothing: uniform LSI and RG stability (SU(2)) | 5671-5676 | S0 | C0 |  |
| YM-0284 | theorem | `thm:su2-uniform-lsi` | Uniform LSI at positive time | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / Positive-time heat-smoothing: uniform LSI and RG stability (SU(2)) | 5678-5684 | S0 | C0 |  |
| YM-0285 | lemma | `lem:su2-block-lipschitz` | Gradient Lipschitz bound for block maps | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / Positive-time heat-smoothing: uniform LSI and RG stability (SU(2)) | 5696-5701 | S0 | C0 |  |
| YM-0286 | theorem | `thm:su2-rg-stability` | RG stability | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / Positive-time heat-smoothing: uniform LSI and RG stability (SU(2)) | 5703-5708 | S0 | C0 |  |
| YM-0287 | remark | `unlabeled@L5714` | Consequences and constants | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / Positive-time heat-smoothing: uniform LSI and RG stability (SU(2)) | 5714-5716 | S0 | C0 | remark (scan for hidden claims) |
| YM-0288 | theorem | `DEC:plaquette-F2` | Finite-region, gauge-invariant plaquette$\to F^2$ control; explicit $O(a^2)$ | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / Finite-region classical control (plaquette$\to F^2$, $O(a^2)$) | 5721-5727 | S0 | C0 |  |
| YM-0289 | lemma | `lem:U1-tree-bounds` | Tree–gauge Lipschitz bounds | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / Finite-region classical control (plaquette$\to F^2$, $O(a^2)$) | 5759-5761 | S0 | C0 |  |
| YM-0290 | corollary | `cor:U1-uei` | Explicit UEI constants | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / Finite-region classical control (plaquette$\to F^2$, $O(a^2)$) | 5762-5768 | S0 | C0 |  |
| YM-0291 | lemma | `lem:U2-embeddings` | OS/GNS embeddings are genuine isometries | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / U2a. Embeddings and comparison identity | 5770-5772 | S0 | C0 |  |
| YM-0292 | theorem | `NRC:form-thm` | Norm--resolvent convergence from form approximation | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / NRC via form approximation (abstract, quantified; Kato resolvent calculus) | 5786-5792 | S0 | C0 |  |
| YM-0293 | lemma | `lem:U2-comparison` | Explicit resolvent comparison identity | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / NRC via form approximation (abstract, quantified; Kato resolvent calculus) | 5806-5814 | S3 | C4 | proved as a direct algebraic identity: decompose $R(z)=R(z)(I-P)+R(z)P$ and use $(H-z)I-I(H_a-z)=D$ on the common core, then multiply by resolvents |
| YM-0294 | theorem | `thm:U2-nrc-unique` | AF–free uniqueness of the continuum generator | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / NRC via form approximation (abstract, quantified; Kato resolvent calculus) | 5815-5827 | S0 | C0 |  |
| YM-0295 | proposition | `prop:one-point-resolvent` | One–point resolvent estimate at a nonreal $z_0$ | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / NRC via form approximation (abstract, quantified; Kato resolvent calculus) | 5832-5844 | S0 | C0 |  |
| YM-0296 | lemma | `lem:U2-defect-core` | Defect identity and common core | Appendix U: AF--free inputs and continuum limit (hypotheses U1--U4) / NRC via form approximation (abstract, quantified; Kato resolvent calculus) | 5853-5863 | S0 | C0 |  |

### Short -- Distance Structure: Normal Products, OPE, and AF Matching

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0297 | definition | `def:local-seminorm` | Local seminorm for gauge – invariant insertions | Short -- Distance Structure: Normal Products, OPE, and AF Matching / Zimmermann normal products in the gauge – invariant sector | 5894-5901 | S0 | C0 | definition (no proof) |
| YM-0298 | lemma | `lem:local-seminorm-cal` | Calibrator control of local seminorms | Short -- Distance Structure: Normal Products, OPE, and AF Matching / Zimmermann normal products in the gauge – invariant sector | 5903-5909 | S0 | C0 |  |
| YM-0299 | theorem | `thm:renorm-composites` | Existence and temperedness of renormalized composites (any compact simple $G$) | Short -- Distance Structure: Normal Products, OPE, and AF Matching / Zimmermann normal products in the gauge – invariant sector | 5914-5916 | S0 | C0 |  |
| YM-0300 | theorem | `thm:ope-gi` | Gauge – invariant OPE with remainder (any compact simple $G$) | Short -- Distance Structure: Normal Products, OPE, and AF Matching / Operator product expansion with uniform remainder | 5924-5935 | S0 | C0 |  |
| YM-0301 | corollary | `cor:cs-wilson` | Callan--Symanzik for Wilson coefficients | Short -- Distance Structure: Normal Products, OPE, and AF Matching / Operator product expansion with uniform remainder | 5936-5942 | S0 | C0 |  |
| YM-0302 | lemma | `lem:ope-remainder-uniform` | Uniform remainder bound across van Hove sequences | Short -- Distance Structure: Normal Products, OPE, and AF Matching / Operator product expansion with uniform remainder | 5947-5953 | S0 | C0 |  |
| YM-0303 | proposition | `prop:pert-matching` | Perturbative matching to all orders | Short -- Distance Structure: Normal Products, OPE, and AF Matching / Operator product expansion with uniform remainder | 5958-5960 | S0 | C0 |  |
| YM-0304 | theorem | `thm:af-matching` | AF matching for gauge – invariant two – point functions (any compact simple $G$) | Short -- Distance Structure: Normal Products, OPE, and AF Matching / AF – consistent short – distance behavior | 5971-5978 | S0 | C0 |  |
| YM-0305 | corollary | `cor:global-ope` | Global OPE and AF matching on $\mathbb R^4$ (any compact simple $G$) | Short -- Distance Structure: Normal Products, OPE, and AF Matching / AF – consistent short – distance behavior | 5983-5985 | S0 | C0 |  |
| YM-0306 | proposition | `prop:sd-constants` | Short – distance constants summary | Short -- Distance Structure: Normal Products, OPE, and AF Matching / AF – consistent short – distance behavior | 5990-6009 | S0 | C0 |  |

### Stress – Energy Tensor: Construction and Generator Properties

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0307 | lemma | `lem:ward-translation` | Translation Ward identity for local insertions | Stress – Energy Tensor: Construction and Generator Properties / Definition via renormalized composites and improvement | 6033-6039 | S0 | C0 |  |
| YM-0308 | theorem | `thm:T-properties` | Locality, conservation, and covariance of $T_{\mu\nu}$ (any compact simple $G$) | Stress – Energy Tensor: Construction and Generator Properties / Definition via renormalized composites and improvement | 6044-6050 | S0 | C0 |  |
| YM-0309 | theorem | `thm:T-generators` | Generator properties (any compact simple $G$) | Stress – Energy Tensor: Construction and Generator Properties / Definition via renormalized composites and improvement | 6055-6065 | S0 | C0 |  |
| YM-0310 | lemma | `lem:T-integral-domain` | Time--zero integral and closability domain for $T_{0\mu}$ | Stress – Energy Tensor: Construction and Generator Properties / Definition via renormalized composites and improvement | 6066-6072 | S0 | C0 |  |
| YM-0311 | proposition | `prop:trace-anomaly` | Trace anomaly and scheme consistency (any compact simple $G$) | Stress – Energy Tensor: Construction and Generator Properties / Definition via renormalized composites and improvement | 6077-6084 | S0 | C0 |  |

### Appendix: $\beta$ – Independent Interface Minorization (Explicit Constants)

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0312a | lemma | `lem:compact-small-ball` | Heat kernel dominates a small ball on compact $G$ | Appendix: $\beta$ – Independent Interface Minorization (Explicit Constants) | 6133-6146 | S3 | C4 | proved (compactness + positivity) |
| YM-0312 | proposition | `prop:explicit-doeblin-constants-appendix` | Explicit Doeblin constants, $\beta$ – independent | Appendix: $\beta$ – Independent Interface Minorization (Explicit Constants) | 6148-6157 | S2 | C2 | sketch proof; depends on citation-only lemmas (`lem:coarse-refresh`) + factorization details |

### Appendix: Abstract NRC Criterion and YM Verification

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0313 | theorem | `thm:abstract-nrc` | Abstract NRC from quantitative bounds | Appendix: Abstract NRC Criterion and YM Verification | 6113-6127 | S0 | C0 |  |
| YM-0314 | corollary | `cor:nrc-ym` | Verification for Yang -- Mills | Appendix: Abstract NRC Criterion and YM Verification | 6132-6134 | S0 | C0 |  |

### Appendix: SU(2) Matrix – Fisher Block – Doeblin Minorization

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0315 | lemma | `lem:su2-mf` | SU(2) matrix – Fisher normalization | Appendix: SU(2) Matrix – Fisher Block – Doeblin Minorization | 6142-6148 | S0 | C0 |  |
| YM-0316 | lemma | `lem:su2-kappa` | Staple bound for a single link | Appendix: SU(2) Matrix – Fisher Block – Doeblin Minorization | 6150-6152 | S0 | C0 |  |
| YM-0317 | theorem | `thm:su2-single` | SU(2) single – link Doeblin minorization | Appendix: SU(2) Matrix – Fisher Block – Doeblin Minorization | 6154-6159 | S0 | C0 |  |
| YM-0318 | theorem | `thm:su2-block` | SU(2) block – Doeblin minorization | Appendix: SU(2) Matrix – Fisher Block – Doeblin Minorization | 6161-6170 | S0 | C0 |  |
| YM-0319 | remark | `unlabeled@L6172` | From $\beta$ – dependent to $\beta$ – independent weights | Appendix: SU(2) Matrix – Fisher Block – Doeblin Minorization | 6172-6174 | S0 | C0 | remark (scan for hidden claims) |

### Appendix: UEI/LSI on Fixed Regions and AF – Free NRC in the Uniqueness Regime

| ID | Type | Label | Title | Where (sec/subsec) | TeX lines | Status | Conf | Notes |
|---:|:-----|:------|:------|:------------------|:----------|:------:|:----:|:------|
| YM-0320 | theorem | `thm:lsi-uei-appendix` | Uniform LSI/UEI on fixed regions | Appendix: UEI/LSI on Fixed Regions and AF – Free NRC in the Uniqueness Regime | 6182-6184 | S0 | C0 |  |
| YM-0321 | proposition | `prop:lsi-marginal` | Stability under coarse – graining | Appendix: UEI/LSI on Fixed Regions and AF – Free NRC in the Uniqueness Regime | 6186-6188 | S0 | C0 |  |
| YM-0322 | theorem | `thm:thermo-uei` | Thermodynamic limit and Euclidean invariance | Appendix: UEI/LSI on Fixed Regions and AF – Free NRC in the Uniqueness Regime | 6190-6192 | S0 | C0 |  |
| YM-0323 | remark | `unlabeled@L6194` | Use within the main chain | Appendix: UEI/LSI on Fixed Regions and AF – Free NRC in the Uniqueness Regime | 6194-6196 | S0 | C0 | remark (scan for hidden claims) |

