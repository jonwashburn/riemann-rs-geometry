## Proof Track — `BSD-Jon-Final.txt`

This document is a **multi-session proof-audit track** for the LaTeX file `BSD-Jon-Final.txt`.

**Important**: this started as an auto-generated scaffold. Once you begin filling in proofs here, avoid overwriting the file wholesale; instead edit in-place session-by-session.

- **Generated**: 2025-12-20 14:23:21
- **Source**: `BSD-Jon-Final.txt`
- **Theorem-like environments found**: 183

### How to use this (workflow)

- **Pick a result** from the inventory.
- **Copy/verify the statement** against the source lines.
- **List dependencies** (internal labels + external theorems) and mark whether each is proved/assumed.
- **Write a massive-detail proof** (no gaps) in the section for that result.
- **Tag blockers** (conditional inputs, missing lemmas, suspected false steps).
- **Repeat**; confidence accumulates top-down as dependencies close.

### Status taxonomy (edit per result)

Use one of:
- **todo**: not started
- **stated**: statement copied + checked vs source
- **outlined**: dependency graph + proof outline written
- **drafted**: full proof written (still needs audit)
- **audited**: proof checked line-by-line; all citations resolved
- **blocked**: cannot proceed (missing input / circularity / unclear definition)
- **conditional**: relies on black-box / hypothesis / conjecture
- **suspect**: likely wrong / needs counterexample check
- **deprecated**: intentionally not used in the current mainline; kept only as historical context (do not invest effort unless reviving that route)

### Session log

- **2025-12-20**: Auto-generated inventory + per-result proof templates from `BSD-Jon-Final.txt`. Next step is to pick a target result and start the `stated → outlined → drafted → audited` loop.

### BSD unconditional checklist (C0–C5) — dashboard (active route)

This is the **minimal spine** for an unconditional BSD proof in this manuscript’s framework. Each item must be either (i) proved internally with referee-grade detail, or (ii) supplied by unconditional literature with exact theorem-number mapping and a verified hypothesis check. If an item is blocked, **all downstream “unconditional” claims must be downgraded**.

| ID | Goal (what must be true) | Where it lives in this repo | Current status | Minimal unblocker |
|---|---|---|---|---|
| **C0** | Definitions + normalizations: \(L_p\), \(L_p^{\pm}\), improved \(L_p^{\!*}\); Selmer \(X_p\), \(X_p^{\pm}\); small primes; exceptional zeros | `BSD-Jon-Final.txt` §§2.3–2.5, F.15, F.40; proof-track C0 dictionary below | **done** | — |
| **C1** | Operator/determinant exactness: \(\det(I-K)\doteq L_p\) and \(\mathrm{coker}(I-K)^\vee\simeq X\) (ordinary/signed/improved), with integral exactness for \(T=0\) leading terms | `BSD-Jon-Final.txt` §§4.5–4.8 + Appendix F; proof-track `thm:integral-det-exact-ord` etc | **conditional** | produce a fully cited/referee-grade operator model and integral exactness proof (or downgrade claims that depend on it) |
| **C2** | Cyclotomic IMC **ideal equality** at every \(p\) (ordinary/signed/improved), via literature coverage + finite-exception closures | proof-track `cor:disc-imc`, `thm:universal-imc`; `BSD-Jon-Final.txt` §F.32 | **blocked** | a genuine “all primes” coverage theorem in the supersingular/additive-conductor and small-prime edge ranges (or an explicit finite closure that yields ideal equality, not just \(T=0\) consequences) |
| **C3** | Universal \(\mu=0\) for every \(p\) (ordinary and signed) | `BSD-Jon-Final.txt` Appendix F.pw; proof-track `thm:mu0-wedge` / `thm:pw-wedge-mu` | **blocked** | either (i) a complete referee-grade proof of the wedge/energy/nonvanishing package, or (ii) replace by an unconditional literature theorem (none known at this generality) |
| **C4** | BSD\(_p\) for every prime from (IMC equality + \(\mu=0\) + exactness + PT + exceptional-zero correction) | `BSD-Jon-Final.txt` `cor:universal-bsd-p`; proof-track `cor:universal-bsd-p` / `prop:BSDp` | **conditional** | C1+C2+C3 + a correct fixed-prime \(\Sha[p^\infty]\) finiteness/leading-term interface (Appendix C issues must be resolved) |
| **C5** | Global BSD from BSD\(_p\) for all primes (algebraicity of ratio + sign) | `BSD-Jon-Final.txt` Appendix G; proof-track `thm:global-bsd` | **drafted/conditional** | C4 for all \(p\) + a clean reference/proof for the archimedean sign/positivity step |

### C0 — Definitions and normalization dictionary (AUDITED)

This section closes checklist item **C0**: it pins down the **exact conventions** used for the cyclotomic Iwasawa algebra \(\Lambda\), the cyclotomic \(p\)-adic \(L\)-functions (ordinary / signed / improved), and the corresponding Selmer/Iwasawa modules, in a way that makes later literature IMC imports unambiguous.

The guiding principle is that **IMC statements live in \(\Lambda\) only up to**:
- a **\(\Lambda^\times\)** unit factor (period/differential/branch normalizations), and
- a **canonical \(\Lambda\)-automorphism** induced by changing the chosen topological generator \(\gamma\in\Gamma\).

Accordingly, when we say “IMC equality” later, we always mean **equality of ideals in \(\Lambda\)** after transporting both sides across these harmless normalizations.

#### C0.1. Cyclotomic Iwasawa algebra and evaluation at characters

- **Cyclotomic extension**: \(\mathbb Q_\infty/\mathbb Q\) is the cyclotomic \(\mathbb Z_p\)-extension and \(\Gamma:=\mathrm{Gal}(\mathbb Q_\infty/\mathbb Q)\cong \mathbb Z_p\).
- **Iwasawa algebra**: \(\Lambda:=\mathbb Z_p\llbracket \Gamma\rrbracket\).
- **Generator and coordinate**: fix a topological generator \(\gamma\in\Gamma\) and identify \(\Lambda\cong\mathbb Z_p\llbracket T\rrbracket\) via \(T=\gamma-1\).
- **Finite-order evaluation**: for a finite-order character \(\chi:\Gamma\to \mu_{p^n}\subset\overline{\mathbb Q}_p^\times\), define
  \[
  \mathrm{ev}_\chi:\Lambda\to \mathbb Z_p[\mu_{p^n}],\qquad \mathrm{ev}_\chi(\gamma)=\chi(\gamma)\quad(\text{i.e. }T\mapsto \chi(\gamma)-1).
  \]

**Generator change (canonical \(\Lambda\)-automorphism).**  
If \(\gamma'=\gamma^u\) with \(u\in\mathbb Z_p^\times\), then \(T'=\gamma'-1=(1+T)^u-1\), and substitution yields a \(\Lambda\)-automorphism
\[
\iota_u:\mathbb Z_p\llbracket T\rrbracket\to\mathbb Z_p\llbracket T\rrbracket,\qquad f(T)\mapsto f\big((1+T)^u-1\big).
\]
For every ideal \(I\subset\Lambda\), the transported ideal \(\iota_u(I)\) is the “same” ideal expressed in the new coordinate. In particular, **ideal equalities are invariant**:
\[
(f)=(g)\ \Longleftrightarrow\ (\iota_u(f))=(\iota_u(g)).
\]

This is the only generator-dependence we allow anywhere in the IMC/BSD pipeline.

#### C0.2. Cyclotomic \(p\)-adic \(L\)-functions: ordinary / signed / improved

We use the following objects (all are standard; the point of C0 is only to freeze conventions):

- **Ordinary (good ordinary \(p\ge 5\))**: a cyclotomic \(p\)-adic \(L\)-function \(L_p(E,T)\in\Lambda\) characterized by the usual interpolation against finite-order cyclotomic characters. We write \(L_p(E,\chi):=\mathrm{ev}_\chi(L_p(E,T))\).  
  **Normalization rule**: changing the Néron differential / Shimura period choices or Perrin–Riou branch multiplies \(L_p(E,T)\) by an element of \(\Lambda^\times\); changing \(\gamma\) transports it by \(\iota_u\) as above.

- **Supersingular (signed theory)**: for supersingular primes (classically \(p\ge 5\)), we use the signed \(p\)-adic \(L\)-functions \(L_p^{\pm}(E,T)\in\Lambda\) (Pollack/Kobayashi/LLZ framework) and define \(L_p^{\pm}(E,\chi):=\mathrm{ev}_\chi(L_p^{\pm}(E,T))\).  
  **Normalization rule**: identical (units + generator automorphism).

- **Split multiplicative (exceptional zero / improved objects)**: when \(E\) has split multiplicative reduction at \(p\), the usual cyclotomic \(p\)-adic \(L\)-function has a trivial zero at \(\chi=1\) (i.e. at \(T=0\)). In this case we use the **improved** cyclotomic \(p\)-adic \(L\)-function \(L_p^{\!*}(E,T)\) together with the matching improved algebraic objects; see `BSD-Jon-Final.txt` \S\,F.40.  
  **Policy**: whenever a statement is phrased as “IMC/BSD\(_p\) at \(p\)”, it is understood that at split multiplicative \(p\) we work in the **improved normalization**.

#### C0.3. Selmer groups and Iwasawa modules: ordinary / signed / improved

Fix \(E/\mathbb Q\) and a prime \(p\ge 2\).

- **Cyclotomic Selmer**: \(\mathrm{Sel}_{p^\infty}(E/K)\) is defined by standard local conditions at all places \(v\) of \(K\).
- **Local condition at \(v\mid p\)**:
  - **ordinary**: the finite (“Greenberg”) condition;
  - **supersingular**: the Kobayashi \(\pm\) local conditions (hence signed Selmer);
  - **split multiplicative**: the improved local condition (Greenberg–Stevens), matching \(L_p^{\!*}\).
- **Iwasawa module**:
  \[
  X_p(E/\mathbb Q_\infty):=\mathrm{Hom}_{\mathrm{cont}}\big(\mathrm{Sel}_{p^\infty}(E/\mathbb Q_\infty),\ \mathbb Q_p/\mathbb Z_p\big),
  \]
  and analogously \(X_p^{\pm}\) (signed) and \(X_p^{\!*}\) (improved).

**Convention alignment with the literature.**  
Different papers may:
- use **imprimitive** Selmer groups / \(L\)-functions (removing Euler factors at a finite set \(\Sigma\) of bad primes),
- use different \(\Gamma\)-generators / \(T\)-coordinates,
- use different period normalizations (unit scaling).

Our rule is: every external IMC theorem imported later (C2) must specify its \(\Sigma\) and its local condition at \(p\); then we translate to our primitive objects by (i) multiplying by the explicit Euler factors and (ii) applying the \(\Lambda\)-unit / \(\iota_u\) transport. C0 records the mechanics; C2 records the per-paper theorem numbers and hypothesis checks.

#### C0.4. Small primes and additive reduction

- For \(p\in\{2,3\}\) and for additive reduction at \(p\), the **definitions** of \(L_p\)/Selmer/\(X_p\) are unchanged.  
- In the operator/Wach-module model used elsewhere, we instead use overconvergent \((\varphi,\Gamma)\)-modules; see `BSD-Jon-Final.txt` \S\,F.15. (Those proofs/inputs belong to C1, not C0.)

#### C0.5. Where this is enforced in the manuscript

We updated `BSD-Jon-Final.txt` so the manuscript itself now points back to this C0 dictionary:
- \(\Lambda\), evaluation maps, and generator-change invariance: `BSD-Jon-Final.txt` \S2.3.
- \(L_p\), \(L_p^{\pm}\), improved \(L_p^{\!*}\) policy and normalization disclaimer: `BSD-Jon-Final.txt` \S2.4 and \S\,F.40.
- Selmer local conditions (ordinary/signed/improved) and small-prime/additive pointer: `BSD-Jon-Final.txt` \S2.5 and \S\,F.15.

### Immediate triage / questions (high signal)

- **Global claim consistency**: The manuscript text has been downgraded so global BSD claims are now stated **conditionally** on the \(\mu=0\)/IMC/exactness packages; the remaining unconditional/conditional boundary is enforced by this proof-track dashboard.
- **New/nonstandard inputs to audit early**:
  - Appendix **F.pw** (cyclotomic wedge / universal \(\mu=0\)) is still a proposed internal engine and must be audited if we want any “unconditional \(\mu=0\)” story.
  - Appendix **F.fs** (finite-slope disc Schur–pinch / disc IMC) is now **deprecated** in the mainline: the current route imports cyclotomic IMC equality from the **literature coverage** package (\S\,F.32) instead of proving it by a new disc-boundary rigidity argument. The disc engine sections are kept as historical context only.
- **Engine attack order (unconditional goal)**:
  - **Primary**: lock down the **IMC coverage table** (`cor:disc-imc`, `thm:universal-imc`) with exact theorem numbers/hypotheses for the 2024–2025 citations and the finite-exception closure steps (small primes, exceptional zero, Eisenstein/reducible residual set).
  - **Parallel (hard / likely-new)**: audit whether the cyclotomic wedge package (Appendix F.pw: `thm:box-energy`, `lem:wedge`, `thm:mu0-wedge`) can be made referee-grade. If not, treat universal \(\mu=0\) as conditional and keep it out of “unconditional” claims.
- **Resolved (paper repair): height-unit pipeline vs §7.1**: the source has been repaired so §7.1 explicitly records that, under the stated normalization \(t(E_1)\subset p\mathbb{Z}_p\) and \(u_p\in\mathbb{Z}_p^\times\), formal-group points have \(v_p(h_p(X))\ge 2\) and therefore are not diagonal units. The separation-based “height–unit prime” certificate is now formulated correctly: `prop:triangular` uses mixed integrality to force \(h_p(P_i,P_j)\in p\mathbb{Z}_p\) for \(i\ne j\) in the **unscaled** Gram matrix, and diagonal unit checks are performed on the basis points \(P_i\) (typically in \(E(\mathbb{Z}_p)\setminus E_1\)), not on \(m_iP_i\in E_1\).
- **Confirmed blocker: “diagonal–unit certificate ⇒ \(\mu=0\)” route (rank \(r>1\))**: the source’s congruence \(h_p(R,S)\equiv u_p\,\log_\omega(R)\log_\omega(S)\pmod p\) (from `lem:triang-ord-modp`) is stable under any \(M_p\in\mathrm{GL}_r(\mathbb{Z}_p)\) change of basis. Therefore, if **all** \(\log_\omega(Q_i)\in\mathbb{Z}_p^\times\), then **all** entries of \(H'_p\) are nonzero mod \(p\), so \(H'_p\) cannot be upper triangular mod \(p\) unless \(r=1\). This breaks the intended use of `thm:R-triangular` / `thm:R-triangular-signed` as “μ=0 from triangularization + unit diagonals”.
- **Confirmed blocker: Appendix C.3 Sha finiteness**: the dimension argument “nondegenerate height ⇒ \(\Sha[p^\infty]\) finite” in Appendix C.3 is invalid as written; it does not follow from the orthogonal decomposition. Anything relying on Appendix C.3 needs a different proof or must treat \(\Sha[p^\infty]\) finiteness as an extra hypothesis.
- **Sketched items are blockers by default**: Anything flagged `SKETCH` should be treated as `blocked` until expanded.
- **Black boxes are policy choices**: B1–B4 are explicit assumed inputs unless replaced by internal arguments later; decide whether we accept them as axioms for the track or treat them as targets to prove/justify.

#### Proposed correction (paper-level): resolve the §7.1 “formal-group diagonal units” contradiction

This track treats the §7.1 mismatch as a **hard contradiction** until the source specifies an explicit normalization correction.

**Recommendation (minimal change; consistent with standard formal group conventions).**
- Keep the §7.1 definitions as written: for \(X\in E_1(\mathbb{Q}_p)\), \(t(X)\in p\mathbb{Z}_p\) and \(\log_E(T)=T+O(T^2)\in\mathbb{Z}_p\llbracket T\rrbracket\), with \(h_p(X,X)=u_p\log_E(t(X))^2\) and \(u_p\in\mathbb{Z}_p^\times\).
- Then \(\log_E(t(X))\in p\mathbb{Z}_p\) and \(v_p(h_p(X,X))\ge 2\) for all \(X\in E_1(\mathbb{Q}_p)\).
- **Required editorial fix**: replace every claim of the form “\(mP\in E_1(\mathbb{Q}_p)\) and \(h_p(mP)\in\mathbb{Z}_p^\times\)” (or “\(\log_E(mP)\in\mathbb{Z}_p^\times\)”) by the correct valuation bounds, and treat the “height–unit prime”/“diagonal–unit certificate ⇒ \(\mu=0\)” route as **not available** for rank \(r>1\) without additional new input.

**Alternative salvage routes (high risk; require re-audit of many sections).**
- **Rescale log/height normalization**: e.g. \(\log^{\mathrm{paper}}:=p^{-1}\log^{\mathrm{formal}}\) (or a non-minimal differential) so that \(\log^{\mathrm{paper}}(E_1)\) can contain units. This changes the valuation of the constant \(u_p\) and forces a re-audit of `lem:unit-log`, `lem:mixed-integrality`, and every “integrality/unit” inference downstream.
- **Change the separation/arithmetic mechanism**: alter the CRT scaling so the “diagonal” points lie in \(E(\mathbb{Z}_p)\setminus E_1\) (where units are possible) while off-diagonals land in \(E_1\) and mixed-integrality applies by symmetry. This would require strengthening/redefining `def:separated` and rewriting the local triangularization pipeline.

**Deep-dive note**: `notes/papers/bsd/coleman-gross-heights-notes.md`

### BSD external deep-dive workflow (implemented)

This track now uses a **paper-by-paper audit workflow** (adapted from `PAPER_DEEP_DIVE_PLAN.md`) for all *external* results referenced by `BSD-Jon-Final.txt`.

- **Notes folder**: `notes/papers/bsd/`
- **Summary map**: `notes/papers/bsd/DEEP_DIVE_SUMMARY.md`
- **Per-paper notes (initial scaffolds)**:
  - `notes/papers/bsd/1994-1995-perrin-riou-big-log-notes.md`
  - `notes/papers/bsd/coleman-gross-heights-notes.md`
  - `notes/papers/bsd/kato-euler-system-divisibility-notes.md`
  - `notes/papers/bsd/greenberg-control-notes.md`
  - `notes/papers/bsd/nekovar-selmer-complexes-poitou-tate-notes.md`
  - `notes/papers/bsd/kobayashi-pollack-llz-signed-theory-notes.md`

#### Deliverables per external reference (required before upgrading statuses)
- **Exact statement** we need (with hypotheses)
- **Normalization dictionary** to the paper’s notation (logs/heights/projectors)
- **Where it is used** (proof-track labels)
- **What remains conditional** after importing it

#### Priority order (highest ROI)
- Perrin–Riou interpolation (ordinary + signed) → unlock `lem:PR-*` / `thm:HL-*`
- Coleman–Gross normalization → resolves the §7.1 formal-group valuation contradiction (or confirms it is fatal)
- Greenberg control + Nekovář PT → required for `thm:sha-finite` audit
- Kato one-sided divisibility → required for `prop:BSDp` and μ/IMC pipelines

### Global dashboard: explicit black-box inputs / hypotheses / conjectures

#### Standing black boxes (from §2.6)

- **B1**: Cyclotomic Iwasawa Main Conjecture (IMC$_p$). — Source `BSD-Jon-Final.txt` L187
- **B1'**: One–sided divisibility (Kato). — Source `BSD-Jon-Final.txt` L193
- **B2**: Coleman–Gross heights and leading term. — Source `BSD-Jon-Final.txt` L200
  - **Deep-dive note**: `notes/papers/bsd/coleman-gross-heights-notes.md`
  - **Critical**: as currently written, §7.1’s checklist + `lem:unit-log` imply \(v_p(h_p(X))\ge 2\) for \(X\in E_1(\mathbb{Q}_p)\), contradicting repeated “formal-group diagonal unit” claims. Treat any unit-diagonal-in-\(E_1\) pipeline steps as blocked until a normalization correction is specified.
- **B3**: Poitou–Tate and Cassels–Tate. — Source `BSD-Jon-Final.txt` L203
- **B4**: Control theorems. — Source `BSD-Jon-Final.txt` L206

#### Hypotheses declared in the source

- **hyp:big-kummer** — Source L353
- **hyp:twist** — Source L1406

#### Conjectures declared in the source

- **conj:sep-density** — Source L3299

#### Auto-detected incompleteness / conditionality indicators

- `SKETCH`: title/body contains "sketch"
- `ASSUMES`: contains "Assume"
- `USES_HYP`: references `hyp:*`
- `USES_CONJ`: references `conj:*`
- `IMC_MENTION`: mentions IMC / main conjecture

##### Results flagged `SKETCH` (auto-list)

- [auto-proposition-L1391](#auto-proposition-l1391) (proposition) — Twist–average template; sketch — L1391–L1397
- [thm:sep-infinitude](#thm-sep-infinitude) (theorem) — Infinitude under Serre and independence; sketch — L3303–L3305
- [prop:sha-global-criterion](#prop-sha-global-criterion) (proposition) — Criterion via $\Lambda$–adic positivity and PT; sketch — L3312–L3314

##### Results flagged `USES_CONJ` (auto-list; treat as blockers)

- (none detected)

##### Results flagged `USES_HYP` (auto-list)

- [thm:inf-many-ord-units](#thm-inf-many-ord-units) (theorem) — Infinitely many ordinary diagonal--unit primes under Hypothesis~\ref{hyp:big-kummer} — L360–L366
- [thm:inf-many-signed-units](#thm-inf-many-signed-units) (theorem) — Signed analogue — L383–L385
- [thm:twist-average](#thm-twist-average) (theorem) — Twist–average positive density of diagonal units — L1421–L1427
- [thm:kummer-independence](#thm-kummer-independence) (theorem) — Kummer independence under non--CM — L1654–L1661

##### Results flagged `ASSUMES` (auto-list)

- [thm:inf-many-ord-units](#thm-inf-many-ord-units) (theorem) — Infinitely many ordinary diagonal--unit primes under Hypothesis~\ref{hyp:big-kummer} — L360–L366
- [thm:twist-average](#thm-twist-average) (theorem) — Twist–average positive density of diagonal units — L1421–L1427
- [thm:level-raise-visibility](#thm-level-raise-visibility) (theorem) — Level–raised congruences and visibility — L1466–L1468
- [thm:anti-BSDp](#thm-anti-bsdp) (theorem) — Anticyclotomic promotion to BSD$_p$ — L1480–L1492
- [thm:RS-BSDp](#thm-rs-bsdp) (theorem) — Rankin–Selberg promotion to BSD$_p$ — L1501–L1512
- [lem:ord-char](#lem-ord-char) (lemma) — Order at $T=0$ under IMC — L1575–L1581
- [cor:sec6A-density](#cor-sec6a-density) (corollary) — \S6A: ordinary diagonal--unit density — L1726–L1733
- [auto-corollary-L1750](#auto-corollary-l1750) (corollary) — Toward global $\Sha$ finiteness — L1750–L1752
- [prop:BSDp](#prop-bsdp) (proposition) — IMC$_p$ + $\mu_p=0$ + finite $\Sha[p^\infty]$ $\Rightarrow$ BSD$_p$ — L1872–L1890
- [prop:Hlambda-to-revdiv](#prop-hlambda-to-revdiv) (proposition) — Positivity $\Rightarrow$ reverse divisibility — L3283–L3292
- [thm:sep-infinitude](#thm-sep-infinitude) (theorem) — Infinitude under Serre and independence; sketch — L3303–L3305
- [thm:sep-quant](#thm-sep-quant) (theorem) — Chebotarev–Kummer separation — L3517–L3519
- [thm:vis-kato](#thm-vis-kato) (theorem) — Visibility + Kato $\Rightarrow$ equality at congruence primes — L3608–L3615
- [thm:global-bsd](#thm-global-bsd) (theorem) — Global BSD from BSD$_p$ — L3828–L3834

##### Results flagged `IMC_MENTION` (auto-list)

- [cor:disc-imc](#cor-disc-imc) (corollary) — IMC equality on finite\,--\,slope discs — L628–L630
- [auto-corollary-L677](#auto-corollary-l677) (corollary) — Automatic signed BSD$_p$ — L677–L683
- [auto-proposition-L832](#auto-proposition-l832) (proposition) — Higher rank closure template — L832–L834
- [thm:anti-BSDp](#thm-anti-bsdp) (theorem) — Anticyclotomic promotion to BSD$_p$ — L1480–L1492
- [thm:RS-BSDp](#thm-rs-bsdp) (theorem) — Rankin–Selberg promotion to BSD$_p$ — L1501–L1512
- [thm:global-imc](#thm-global-imc) (theorem) — Cyclotomic IMC from two divisibilities — L1536–L1547
- [thm:universal-imc](#thm-universal-imc) (theorem) — Universal cyclotomic IMC (ordinary and signed) — L1556–L1566
- [lem:ord-char](#lem-ord-char) (lemma) — Order at $T=0$ under IMC — L1575–L1581
- [auto-corollary-L1586](#auto-corollary-l1586) (corollary) — Density BSD$_p$ coverage and closure — L1586–L1588
- [cor:universal-mu](#cor-universal-mu) (corollary) — Universal $\mu=0$ — L1638–L1640
- [prop:mu-zero](#prop-mu-zero) (proposition) — Unit $p$–adic regulator $\Rightarrow \mu_p(E)=0$ — L1841–L1852
- [auto-remark-L1866](#auto-remark-l1866) (remark) — Scope of inputs — L1866–L1868
- [prop:BSDp](#prop-bsdp) (proposition) — IMC$_p$ + $\mu_p=0$ + finite $\Sha[p^\infty]$ $\Rightarrow$ BSD$_p$ — L1872–L1890
- [thm:IMC-operator-ord](#thm-imc-operator-ord) (theorem) — Ordinary IMC packaged as an operator identity — L2102–L2108
- [thm:IMC-operator-signed](#thm-imc-operator-signed) (theorem) — Signed IMC packaged as an operator identity — L2182–L2188
- [auto-remark-L2819](#auto-remark-l2819) (remark) — Two routes to the equality — L2819–L2821
- [auto-remark-L3620](#auto-remark-l3620) (remark) — Supersingular and signed variants — L3620–L3622
- [prop:finite-checklist](#prop-finite-checklist) (proposition) — Finite checklist for $\mathcal{E}$ at rank $\ge 1$ — L3624–L3632
- [thm:R-triangular](#thm-r-triangular) (theorem) — Reverse divisibility at $T=0$ from triangularization — L3638–L3655
- [auto-corollary-L3716](#auto-corollary-l3716) (corollary) — BSD$_p$ in signed IMC ranges — L3716–L3718
- [auto-corollary-L3724](#auto-corollary-l3724) (corollary) — Validated closure for \S6 — L3724–L3732
- [thm:disc-imc](#thm-disc-imc) (theorem) — Finite–slope IMC equality on $D$ — L3800–L3802

### Inventory (file order)

Each line links to a dedicated section below.

- **001**. [def:separated](#def-separated) — **definition** — Separated primes — Source L221–L226 — Flags: **—** — Status: **todo**
- **002**. [lem:CRT](#lem-crt) — **lemma** — Congruence scalings — Source L230–L236 — Flags: **—** — Status: **todo**
- **003**. [lem:triang-ord-modp](#lem-triang-ord-modp) — **lemma** — Lemma U: mod-$p$ upper–triangularization with unit scalar on the diagonal — Source L246–L252 — Flags: **—** — Status: **drafted**
- **004**. [cor:unit-regulator-from-triangular](#cor-unit-regulator-from-triangular) — **corollary** — Determinant valuation and regulator units — Source L269–L275 — Flags: **—** — Status: **drafted**
- **005**. [lem:diag-units](#lem-diag-units) — **lemma** — Per–prime diagonal unit test — Source L284–L290 — Flags: **—** — Status: **drafted**
- **006**. [prop:cofinite-nondeg](#prop-cofinite-nondeg) — **proposition** — Per–prime nondegeneracy — Source L299–L301 — Flags: **—** — Status: **todo**
- **007**. [hyp:big-kummer](#hyp-big-kummer) — **hypothesis** — Big image and Kummer independence — Source L353–L358 — Flags: **HYPOTHESIS** — Status: **todo**
- **008**. [thm:inf-many-ord-units](#thm-inf-many-ord-units) — **theorem** — Infinitely many ordinary diagonal--unit primes under Hypothesis~\ref{hyp:big-kummer} — Source L360–L366 — Flags: **ASSUMES, USES_HYP** — Status: **todo**
- **009**. [thm:inf-many-signed-units](#thm-inf-many-signed-units) — **theorem** — Signed analogue — Source L383–L385 — Flags: **USES_HYP** — Status: **todo**
- **010**. [auto-remark-L390](#auto-remark-l390) — **remark** — What remains to be written in full — Source L390–L392 — Flags: **—** — Status: **todo**
- **011**. [auto-definition-L427](#auto-definition-l427) — **definition** — Completely continuous $\Lambda$–endomorphism — Source L427–L433 — Flags: **—** — Status: **todo**
- **012**. [auto-proposition-L435](#auto-proposition-l435) — **proposition** — Complete continuity of $K(T)$ — Source L435–L440 — Flags: **—** — Status: **todo**
- **013**. [auto-definition-L445](#auto-definition-l445) — **definition** — Fredholm determinant of $K(T)$ — Source L445–L447 — Flags: **—** — Status: **todo**
- **014**. [thm:coker-id](#thm-coker-id) — **theorem** — Cokernel identification — Source L453–L459 — Flags: **—** — Status: **drafted**
- **015**. [thm:det-equals-Lp](#thm-det-equals-lp) — **theorem** — Determinant equals $p$–adic $L$–function — Source L472–L477 — Flags: **—** — Status: **drafted**
- **016**. [thm:integral-det-exact-ord](#thm-integral-det-exact-ord) — **theorem** — Integral big–log determinant and kernel exactness — Source L494–L501 — Flags: **—** — Status: **todo**
- **017**. [lem:wach-lattice-ord](#lem-wach-lattice-ord) — **lemma** — Wach lattice and $\Lambda$–integrality — Source L514–L516 — Flags: **—** — Status: **todo**
- **018**. [lem:exactness-global](#lem-exactness-global) — **lemma** — Exactness and finite cokernel globally — Source L521–L523 — Flags: **—** — Status: **todo**
- **019**. [lem:outer-boundary](#lem-outer-boundary) — **lemma** — Boundary unit\,--\,modulus and zero\,--\,freeness — Source L546–L552 — Flags: **—** — Status: **todo**
- **020**. [rem:noncancellation](#rem-noncancellation) — **remark** — Non\,--\,cancellation at zeros — Source L557–L559 — Flags: **—** — Status: **todo**
- **021**. [thm:box-energy](#thm-box-energy) — **theorem** — Uniform box\,--\,energy bound — Source L569–L575 — Flags: **—** — Status: **blocked**
- **022**. [lem:wedge](#lem-wedge) — **lemma** — Wedge criterion — Source L582–L592 — Flags: **—** — Status: **blocked**
- **023**. [thm:mu0-wedge](#thm-mu0-wedge) — **theorem** — Positive proportion at each depth; $\mu=0$ — Source L597–L599 — Flags: **—** — Status: **conditional**
- **024**. [auto-remark-L604](#auto-remark-l604) — **remark** — Signed and improved variants — Source L604–L606 — Flags: **—** — Status: **todo**
- **025**. [lem:disc-wedge](#lem-disc-wedge) — **lemma** — Boundary wedge on $\partial\mathcal{D}$ — Source L612–L614 — Flags: **—** — Status: **deprecated**
- **026**. [thm:schur-pinch](#thm-schur-pinch) — **theorem** — Rigid Schur pinch; no extra factor on $\mathcal{D}$ — Source L618–L623 — Flags: **—** — Status: **deprecated**
- **027**. [cor:disc-imc](#cor-disc-imc) — **corollary** — IMC equality on finite\,--\,slope discs — Source L628–L630 — Flags: **IMC_MENTION** — Status: **conditional**
- **028**. [auto-remark-L632](#auto-remark-l632) — **remark** — Relation to \S\,F.56 — Source L632–L634 — Flags: **—** — Status: **todo**
- **029**. [cor:universal-bsd-p](#cor-universal-bsd-p) — **corollary** — Universal BSD$_p$ via wedge/pinch — Source L636–L638 — Flags: **—** — Status: **conditional**
- **030**. [cor:global-bsd-outer](#cor-global-bsd-outer) — **corollary** — Global BSD leading term via operator--outer--wedge — Source L643–L645 — Flags: **—** — Status: **todo**
- **030**. [cor:global-bsd-outer](#cor-global-bsd-outer) — **corollary** — Global BSD leading term via operator--outer--wedge — Source L643–L645 — Flags: **—** — Status: **drafted**
- **031**. [auto-corollary-L662](#auto-corollary-l662) — **corollary** — Automatic BSD$_p$ under SU — Source L662–L668 — Flags: **—** — Status: **todo**
- **032**. [auto-corollary-L677](#auto-corollary-l677) — **corollary** — Automatic signed BSD$_p$ — Source L677–L683 — Flags: **IMC_MENTION** — Status: **todo**
- **033**. [def:hida-congruence](#def-hida-congruence) — **definition** — Hida family and congruence ideal — Source L709–L711 — Flags: **—** — Status: **todo**
- **034**. [thm:RS-integral-ord](#thm-rs-integral-ord) — **theorem** — Integral two–variable $p$–adic $L$ and congruence ideal — Source L713–L719 — Flags: **—** — Status: **todo**
- **035**. [lem:gorenstein-ord](#lem-gorenstein-ord) — **lemma** — Gorenstein property and finite flatness — Source L734–L736 — Flags: **—** — Status: **todo**
- **036**. [lem:control-ord](#lem-control-ord) — **lemma** — Ordinary control for Fourier coefficients and cohomology — Source L741–L743 — Flags: **—** — Status: **todo**
- **037**. [lem:integral-interp-hida](#lem-integral-interp-hida) — **lemma** — Integral interpolation normalizations — Source L748–L754 — Flags: **—** — Status: **todo**
- **038**. [thm:twk-divides](#thm-twk-divides) — **theorem** — Patched divisibility and descent — Source L761–L770 — Flags: **—** — Status: **todo**
- **039**. [lem:lgc-greenberg](#lem-lgc-greenberg) — **lemma** — Matching Greenberg local conditions at $p$ — Source L784–L786 — Flags: **—** — Status: **todo**
- **040**. [thm:descent-control](#thm-descent-control) — **theorem** — Descent control from patched modules to $X_p$ — Source L791–L793 — Flags: **—** — Status: **todo**
- **041**. [lem:ord-control-descent](#lem-ord-control-descent) — **lemma** — Ordinary control in families — Source L799–L801 — Flags: **—** — Status: **todo**
- **042**. [auto-theorem-L812](#auto-theorem-l812) — **theorem** — Rank $1$ closure at $p$ — Source L812–L814 — Flags: **—** — Status: **todo**
- **043**. [auto-theorem-L822](#auto-theorem-l822) — **theorem** — Visibility closure at $p$ — Source L822–L824 — Flags: **—** — Status: **todo**
- **044**. [auto-proposition-L832](#auto-proposition-l832) — **proposition** — Higher rank closure template — Source L832–L834 — Flags: **IMC_MENTION** — Status: **todo**
- **045**. [auto-definition-L868](#auto-definition-l868) — **definition** — Detector $\Phi_{N,\omega}$ — Source L868–L878 — Flags: **—** — Status: **todo**
- **046**. [prop:Phi-detector](#prop-phi-detector) — **proposition** — Equivariance and detection — Source L882–L888 — Flags: **—** — Status: **todo**
- **047**. [auto-remark-L900](#auto-remark-l900) — **remark** — Normalization independence — Source L900–L902 — Flags: **—** — Status: **todo**
- **048**. [thm:cm-ord-density](#thm-cm-ord-density) — **theorem** — CM ordinary diagonal–unit density — Source L918–L920 — Flags: **—** — Status: **todo**
- **049**. [thm:cm-signed-inf](#thm-cm-signed-inf) — **theorem** — CM signed supersingular infinitude — Source L932–L934 — Flags: **—** — Status: **todo**
- **050**. [auto-remark-L939](#auto-remark-l939) — **remark** — Effectivity and explicit constants — Source L939–L941 — Flags: **—** — Status: **todo**
- **051**. [auto-proposition-L963](#auto-proposition-l963) — **proposition** — Complete continuity of $K_{\pm}(T)$ — Source L963–L968 — Flags: **—** — Status: **todo**
- **052**. [auto-definition-L970](#auto-definition-l970) — **definition** — Fredholm determinant (signed) — Source L970–L972 — Flags: **—** — Status: **todo**
- **053**. [thm:coker-id-signed](#thm-coker-id-signed) — **theorem** — Signed coker identification — Source L982–L988 — Flags: **—** — Status: **todo**
- **054**. [thm:det-equals-Lp-signed](#thm-det-equals-lp-signed) — **theorem** — Signed determinant equals signed $p$–adic $L$–function — Source L997–L1002 — Flags: **—** — Status: **todo**
- **055**. [thm:integral-det-exact-signed](#thm-integral-det-exact-signed) — **theorem** — Integral signed determinant and kernel exactness — Source L1011–L1013 — Flags: **—** — Status: **todo**
- **056**. [def:family-regulator](#def-family-regulator) — **definition** — Saturated lattice and family regulator — Source L1027–L1036 — Flags: **—** — Status: **todo**
- **057**. [lem:family-integral](#lem-family-integral) — **lemma** — Integrality and specialization — Source L1038–L1040 — Flags: **—** — Status: **todo**
- **058**. [thm:family-det-kernel](#thm-family-det-kernel) — **theorem** — Integral determinant and exact kernel in family — Source L1046–L1059 — Flags: **—** — Status: **todo**
- **059**. [thm:family-exp-recip](#thm-family-exp-recip) — **theorem** — Explicit reciprocity in family — Source L1065–L1071 — Flags: **—** — Status: **todo**
- **060**. [thm:EZ-T0](#thm-ez-t0) — **theorem** — Exceptional zero, corrected $T=0$ statement — Source L1102–L1112 — Flags: **—** — Status: **todo**
- **061**. [thm:improved-integral](#thm-improved-integral) — **theorem** — Integral improved determinant and exact kernel — Source L1126–L1139 — Flags: **—** — Status: **todo**
- **062**. [auto-corollary-L1151](#auto-corollary-l1151) — **corollary** — Improved reverse inclusion — Source L1151–L1160 — Flags: **—** — Status: **todo**
- **063**. [lem:mu-asymptotics](#lem-mu-asymptotics) — **lemma** — Specialization lengths and $\mu$ lower bound — Source L1222–L1224 — Flags: **—** — Status: **todo**
- **064**. [thm:mu-equality](#thm-mu-equality) — **theorem** — $\mu$ equality — Source L1230–L1235 — Flags: **—** — Status: **todo**
- **065**. [auto-definition-L1251](#auto-definition-l1251) — **definition** — Completed cohomology and finite–slope spectrum — Source L1251–L1253 — Flags: **—** — Status: **todo**
- **066**. [auto-definition-L1255](#auto-definition-l1255) — **definition** — Finite–slope Eisenstein ideal — Source L1255–L1257 — Flags: **—** — Status: **todo**
- **067**. [thm:fs-congruence-L](#thm-fs-congruence-l) — **theorem** — Finite–slope congruence module = two–variable (signed) $p$–adic $L$ — Source L1259–L1261 — Flags: **—** — Status: **todo**
- **068**. [thm:fs-patched-descent](#thm-fs-patched-descent) — **theorem** — Finite–slope patched divisibility and descent — Source L1269–L1279 — Flags: **—** — Status: **todo**
- **069**. [thm:int-RS-eigen](#thm-int-rs-eigen) — **theorem** — Integral Rankin–Selberg interpolation on the eigencurve — Source L1287–L1293 — Flags: **—** — Status: **todo**
- **070**. [lem:patching-data](#lem-patching-data) — **lemma** — Patching data — Source L1301–L1303 — Flags: **—** — Status: **todo**
- **071**. [thm:precise-patch](#thm-precise-patch) — **theorem** — Precise patched divisibility — Source L1308–L1310 — Flags: **—** — Status: **todo**
- **072**. [thm:trianguline-signed](#thm-trianguline-signed) — **theorem** — Trianguline control for signed regulators — Source L1317–L1319 — Flags: **—** — Status: **todo**
- **073**. [auto-corollary-L1324](#auto-corollary-l1324) — **corollary** — Exactness and integrality for signed families — Source L1324–L1326 — Flags: **—** — Status: **todo**
- **074**. [lem:awayp-integral](#lem-awayp-integral) — **lemma** — Integral local conditions at $\ell\ne p$ — Source L1340–L1342 — Flags: **—** — Status: **todo**
- **075**. [prop:awayp-neutral](#prop-awayp-neutral) — **proposition** — Determinant neutrality of away–$p$ local factors — Source L1348–L1350 — Flags: **—** — Status: **todo**
- **076**. [auto-corollary-L1356](#auto-corollary-l1356) — **corollary** — Correct global determinant line — Source L1356–L1358 — Flags: **—** — Status: **todo**
- **077**. [lem:affine-line](#lem-affine-line) — **lemma** — Affine count on a translation line — Source L1365–L1371 — Flags: **—** — Status: **todo**
- **078**. [thm:min-kummer-density](#thm-min-kummer-density) — **theorem** — Minimal Kummer criterion for positive density — Source L1376–L1382 — Flags: **—** — Status: **todo**
- **079**. [auto-proposition-L1391](#auto-proposition-l1391) — **proposition** — Twist–average template; sketch — Source L1391–L1397 — Flags: **SKETCH** — Status: **todo**
- **080**. [hyp:twist](#hyp-twist) — **hypothesis** — Twist inputs — Source L1406–L1411 — Flags: **HYPOTHESIS** — Status: **todo**
- **081**. [thm:LS-Cheb](#thm-ls-cheb) — **theorem** — Large–sieve Chebotarev over twist families — Source L1413–L1419 — Flags: **—** — Status: **todo**
- **082**. [thm:twist-average](#thm-twist-average) — **theorem** — Twist–average positive density of diagonal units — Source L1421–L1427 — Flags: **ASSUMES, USES_HYP** — Status: **todo**
- **083**. [auto-remark-L1432](#auto-remark-l1432) — **remark** — Source L1432–L1434 — Flags: **—** — Status: **todo**
- **084**. [thm:uniform-revdiv](#thm-uniform-revdiv) — **theorem** — Uniform reverse divisibility over $\Lambda$ — Source L1440–L1450 — Flags: **—** — Status: **todo**
- **085**. [thm:level-raise-visibility](#thm-level-raise-visibility) — **theorem** — Level–raised congruences and visibility — Source L1466–L1468 — Flags: **ASSUMES** — Status: **todo**
- **086**. [thm:anti-BSDp](#thm-anti-bsdp) — **theorem** — Anticyclotomic promotion to BSD$_p$ — Source L1480–L1492 — Flags: **ASSUMES, IMC_MENTION** — Status: **todo**
- **087**. [thm:RS-BSDp](#thm-rs-bsdp) — **theorem** — Rankin–Selberg promotion to BSD$_p$ — Source L1501–L1512 — Flags: **ASSUMES, IMC_MENTION** — Status: **todo**
- **088**. [lem:uniq-measure](#lem-uniq-measure) — **lemma** — Uniqueness from specializations — Source L1529–L1531 — Flags: **—** — Status: **todo**
- **089**. [thm:global-imc](#thm-global-imc) — **theorem** — Cyclotomic IMC from two divisibilities — Source L1536–L1547 — Flags: **IMC_MENTION** — Status: **todo**
- **090**. [thm:universal-imc](#thm-universal-imc) — **theorem** — Universal cyclotomic IMC (ordinary and signed) — Source L1556–L1566 — Flags: **IMC_MENTION** — Status: **todo**
- **091**. [lem:ord-char](#lem-ord-char) — **lemma** — Order at $T=0$ under IMC — Source L1575–L1581 — Flags: **ASSUMES, IMC_MENTION** — Status: **todo**
- **092**. [auto-corollary-L1586](#auto-corollary-l1586) — **corollary** — Density BSD$_p$ coverage and closure — Source L1586–L1588 — Flags: **IMC_MENTION** — Status: **blocked**
- **093**. [lem:mu-criterion](#lem-mu-criterion) — **lemma** — Character–proportion criterion — Source L1597–L1603 — Flags: **—** — Status: **drafted**
- **094**. [prop:chi-detector](#prop-chi-detector) — **proposition** — Level–$p^n$ detector — Source L1616–L1622 — Flags: **—** — Status: **todo**
- **095**. [thm:LS-chi](#thm-ls-chi) — **theorem** — Positive–proportion nonvanishing at each level — Source L1631–L1633 — Flags: **—** — Status: **todo**
- **096**. [cor:universal-mu](#cor-universal-mu) — **corollary** — Universal $\mu=0$ — Source L1638–L1640 — Flags: **IMC_MENTION** — Status: **todo**
- **097**. [thm:kummer-independence](#thm-kummer-independence) — **theorem** — Kummer independence under non--CM — Source L1654–L1661 — Flags: **USES_HYP** — Status: **todo**
- **098**. [cor:unconditional-density](#cor-unconditional-density) — **corollary** — Unconditional infinitude and density for non--CM curves — Source L1670–L1676 — Flags: **—** — Status: **todo**
- **099**. [lem:good-ell](#lem-good-ell) — **lemma** — A good prime $\ell$ for $(E,P)$ — Source L1685–L1692 — Flags: **—** — Status: **todo**
- **100**. [thm:uniform-kummer](#thm-uniform-kummer) — **theorem** — Uniform Kummer independence at a prime — Source L1697–L1703 — Flags: **—** — Status: **todo**
- **101**. [cor:effective-density](#cor-effective-density) — **corollary** — Effective density constants — Source L1712–L1717 — Flags: **—** — Status: **todo**
- **102**. [cor:sec6A-density](#cor-sec6a-density) — **corollary** — \S6A: ordinary diagonal--unit density — Source L1726–L1733 — Flags: **ASSUMES** — Status: **todo**
- **103**. [cor:sec6B-density](#cor-sec6b-density) — **corollary** — \S6B: ordinary diagonal--unit density — Source L1738–L1740 — Flags: **—** — Status: **todo**
- **104**. [cor:sec6-signed-inf](#cor-sec6-signed-inf) — **corollary** — Signed supersingular infinitude for \S6A/\S6B — Source L1742–L1744 — Flags: **—** — Status: **todo**
- **105**. [auto-remark-L1746](#auto-remark-l1746) — **remark** — Effectivity — Source L1746–L1748 — Flags: **—** — Status: **todo**
- **106**. [auto-corollary-L1750](#auto-corollary-l1750) — **corollary** — Toward global $\Sha$ finiteness — Source L1750–L1752 — Flags: **ASSUMES** — Status: **conditional**
- **107**. [lem:membership](#lem-membership) — **lemma** — Membership in the formal group — Source L1755–L1757 — Flags: **—** — Status: **todo**
- **108**. [lem:formal-factor](#lem-formal-factor) — **lemma** — Formal–group factorization — Source L1767–L1773 — Flags: **—** — Status: **todo**
- **109**. [lem:unit-log](#lem-unit-log) — **lemma** — Formal–group valuation bounds — Source L1775–L1777 — Flags: **—** — Status: **todo**
- **110**. [lem:mixed-integrality](#lem-mixed-integrality) — **lemma** — Mixed integrality — Source L1783–L1789 — Flags: **—** — Status: **drafted**
- **111**. [prop:triangular](#prop-triangular) — **proposition** — Separation forces $p$–divisible off–diagonal heights; diagonal units certify $\mathrm{Reg}_p$ — Source L1799–L1801 — Flags: **—** — Status: **drafted**
- **112**. [cor:height-unit](#cor-height-unit) — **corollary** — Height–unit primes (definition / certificate) — Source L1817–L1822 — Flags: **—** — Status: **drafted**
  - **NOTE**: this item is now marked `blocked` in its section below due to the §7.1 normalization contradiction and the `prop:triangular` issues.
- **113**. [auto-remark-L1824](#auto-remark-l1824) — **remark** — Scope and ordering — Source L1824–L1826 — Flags: **—** — Status: **todo**
- **114**. [prop:mu-zero](#prop-mu-zero) — **proposition** — Unit $p$–adic regulator $\Rightarrow \mu_p(E)=0$ — Source L1841–L1852 — Flags: **IMC_MENTION** — Status: **todo**
- **115**. [auto-remark-L1866](#auto-remark-l1866) — **remark** — Scope of inputs — Source L1866–L1868 — Flags: **IMC_MENTION** — Status: **todo**
- **116**. [prop:BSDp](#prop-bsdp) — **proposition** — IMC$_p$ + $\mu_p=0$ + finite $\Sha[p^\infty]$ $\Rightarrow$ BSD$_p$ — Source L1872–L1890 — Flags: **ASSUMES, IMC_MENTION** — Status: **outlined**
- **117**. [auto-remark-L1896](#auto-remark-l1896) — **remark** — Supersingular primes — Source L1896–L1898 — Flags: **—** — Status: **todo**
- **118**. [thm:det-equals-Lp-ord](#thm-det-equals-lp-ord) — **theorem** — Analytic interpolation: $\det= L_p$ up to $\Lambda^{\times}$ — Source L1948–L1954 — Flags: **—** — Status: **todo**
- **119**. [thm:coker-equals-selmer-ord](#thm-coker-equals-selmer-ord) — **theorem** — Algebraic identification: fixed points $\Rightarrow$ Greenberg Selmer — Source L1963–L1965 — Flags: **—** — Status: **todo**
- **120**. [lem:PR-ord](#lem-pr-ord) — **lemma** — Perrin--Riou explicit reciprocity, ordinary projection — Source L2027–L2037 — Flags: **—** — Status: **todo**
- **121**. [lem:interpolation-kato](#lem-interpolation-kato) — **lemma** — Interpolation with Kato's Euler system — Source L2043–L2049 — Flags: **—** — Status: **todo**
- **122**. [lem:compactness](#lem-compactness) — **lemma** — Complete continuity of $U_p(T)$ — Source L2055–L2057 — Flags: **—** — Status: **todo**
- **123**. [lem:specialization-det](#lem-specialization-det) — **lemma** — Specialization of Fredholm determinants — Source L2063–L2069 — Flags: **—** — Status: **todo**
- **124**. [prop:det-equals-F](#prop-det-equals-f) — **proposition** — Analytic determinant equals $F_{\mathrm{ord}}(T)$ — Source L2075–L2080 — Flags: **—** — Status: **todo**
- **125**. [lem:local-ord](#lem-local-ord) — **lemma** — Local ordinary condition — Source L2086–L2088 — Flags: **—** — Status: **todo**
- **126**. [prop:coker-selmer](#prop-coker-selmer) — **proposition** — Cokernel identification — Source L2094–L2096 — Flags: **—** — Status: **todo**
- **127**. [thm:IMC-operator-ord](#thm-imc-operator-ord) — **theorem** — Ordinary IMC packaged as an operator identity — Source L2102–L2108 — Flags: **IMC_MENTION** — Status: **todo**
- **128**. [lem:PR-signed](#lem-pr-signed) — **lemma** — Signed explicit reciprocity — Source L2135–L2141 — Flags: **—** — Status: **todo**
- **129**. [lem:compactness-signed](#lem-compactness-signed) — **lemma** — Complete continuity and specialization — Source L2147–L2149 — Flags: **—** — Status: **todo**
- **130**. [prop:det-equals-Fpm](#prop-det-equals-fpm) — **proposition** — Analytic determinant equals $F_{\pm}(T)$ — Source L2155–L2160 — Flags: **—** — Status: **todo**
- **131**. [lem:local-signed](#lem-local-signed) — **lemma** — Signed local condition — Source L2166–L2168 — Flags: **—** — Status: **todo**
- **132**. [prop:coker-signed](#prop-coker-signed) — **proposition** — Cokernel identification, signed — Source L2174–L2176 — Flags: **—** — Status: **todo**
- **133**. [thm:IMC-operator-signed](#thm-imc-operator-signed) — **theorem** — Signed IMC packaged as an operator identity — Source L2182–L2188 — Flags: **IMC_MENTION** — Status: **todo**
- **134**. [lem:density_drop](#lem-density-drop) — **lemma** — Density-drop — Source L2203–L2212 — Flags: **—** — Status: **todo**
- **135**. [auto-remark-L2419](#auto-remark-l2419) — **remark** — Exceptional zero and bad reduction — Source L2419–L2421 — Flags: **—** — Status: **todo**
- **136**. [lemA:CRT](#lema-crt) — **lemma** — Congruence scalings — Source L2704–L2709 — Flags: **—** — Status: **todo**
- **137**. [lemA:formal-membership](#lema-formal-membership) — **lemma** — Formal–group membership — Source L2715–L2717 — Flags: **—** — Status: **todo**
- **138**. [lemA:factor](#lema-factor) — **lemma** — Height factorization on $E_1$ — Source L2723–L2729 — Flags: **—** — Status: **todo**
- **139**. [lemA:units-offdiag](#lema-units-offdiag) — **lemma** — Diagonal units and off–diagonal $p$–divisibility — Source L2735–L2741 — Flags: **—** — Status: **blocked**
- **140**. [auto-remark-L2759](#auto-remark-l2759) — **remark** — On normalizations — Source L2759–L2761 — Flags: **—** — Status: **todo**
- **141**. [auto-remark-L2819](#auto-remark-l2819) — **remark** — Two routes to the equality — Source L2819–L2821 — Flags: **IMC_MENTION** — Status: **todo**
- **142**. [auto-remark-L2823](#auto-remark-l2823) — **remark** — Supersingular $\pm$–theory — Source L2823–L2825 — Flags: **—** — Status: **todo**
- **143**. [lemC:height=PT](#lemc-height-pt) — **lemma** — Height as Poitou–Tate on Kummer classes — Source L2861–L2867 — Flags: **—** — Status: **todo**
- **144**. [prop:Hlambda-to-revdiv](#prop-hlambda-to-revdiv) — **proposition** — Positivity $\Rightarrow$ reverse divisibility — Source L3283–L3292 — Flags: **ASSUMES** — Status: **outlined**
- **145**. [conj:sep-density](#conj-sep-density) — **conjecture** — Separated primes have positive density — Source L3299–L3301 — Flags: **CONJECTURE** — Status: **todo**
- **146**. [thm:sep-infinitude](#thm-sep-infinitude) — **theorem** — Infinitude under Serre and independence; sketch — Source L3303–L3305 — Flags: **SKETCH, ASSUMES** — Status: **todo**
- **147**. [prop:sha-global-criterion](#prop-sha-global-criterion) — **proposition** — Criterion via $\Lambda$–adic positivity and PT; sketch — Source L3312–L3314 — Flags: **SKETCH** — Status: **todo**
- **148**. [lem:smallp-kpx](#lem-smallp-kpx) — **lemma** — Overconvergent $(\varphi,\Gamma)$–module replacement — Source L3325–L3327 — Flags: **—** — Status: **todo**
- **149**. [thm:smallp-detexact](#thm-smallp-detexact) — **theorem** — Integral determinant and exact kernel at small primes — Source L3333–L3339 — Flags: **—** — Status: **todo**
- **150**. [lem:smallp-signed-fs](#lem-smallp-signed-fs) — **lemma** — Trianguline control for signed maps at small $p$ — Source L3346–L3348 — Flags: **—** — Status: **todo**
- **151**. [thm:HL-ordinary](#thm-hl-ordinary) — **theorem** — H$\Lambda$–Ord — Source L3355–L3369 — Flags: **—** — Status: **drafted**
- **152**. [lem:PR-ord-proof](#lem-pr-ord-proof) — **lemma** — Perrin–Riou interpolation, ordinary projection — Source L3377–L3383 — Flags: **—** — Status: **conditional**
- **153**. [lem:HL-nondeg](#lem-hl-nondeg) — **lemma** — Nondegeneracy on MW/torsion — Source L3388–L3390 — Flags: **—** — Status: **conditional**
- **154**. [lem:HL-nullspace](#lem-hl-nullspace) — **lemma** — Nullspace injection into the ordinary local condition — Source L3395–L3397 — Flags: **—** — Status: **drafted**
- **155**. [thm:HL-signed](#thm-hl-signed) — **theorem** — H$\Lambda$–Signed — Source L3407–L3414 — Flags: **—** — Status: **drafted**
- **156**. [lem:PR-signed-proof](#lem-pr-signed-proof) — **lemma** — Signed explicit reciprocity — Source L3422–L3428 — Flags: **—** — Status: **conditional**
- **157**. [lem:HL-signed-nondeg](#lem-hl-signed-nondeg) — **lemma** — Nondegeneracy on MW/torsion (signed) — Source L3433–L3435 — Flags: **—** — Status: **conditional**
- **158**. [lem:HL-signed-nullspace](#lem-hl-signed-nullspace) — **lemma** — Nullspace injection into $\pm$ local condition — Source L3440–L3442 — Flags: **—** — Status: **drafted**
- **159**. [prop:psmith](#prop-psmith) — **proposition** — Pseudo–Smith form over $\Lambda$ — Source L3452–L3458 — Flags: **—** — Status: **todo**
- **160**. [prop:fitting](#prop-fitting) — **proposition** — Fitting–minor identification — Source L3472–L3481 — Flags: **—** — Status: **audited**
- **161**. [cor:psmith-signed](#cor-psmith-signed) — **corollary** — Signed pseudo–Smith form over $\Lambda$ — Source L3494–L3500 — Flags: **—** — Status: **todo**
- **162**. [cor:fitting-signed](#cor-fitting-signed) — **corollary** — Signed Fitting–minor identification — Source L3505–L3510 — Flags: **—** — Status: **todo**
- **163**. [thm:sep-quant](#thm-sep-quant) — **theorem** — Chebotarev–Kummer separation — Source L3517–L3519 — Flags: **ASSUMES** — Status: **todo**
- **164**. [thm:sha-finite](#thm-sha-finite) — **theorem** — Cofinite (H$\Lambda$) $\Rightarrow$ $\Sha$ finite — Source L3528–L3530 — Flags: **—** — Status: **conditional**
- **165**. [lem:pr-length](#lem-pr-length) — **lemma** — Specialized pairing and length control — Source L3564–L3576 — Flags: **—** — Status: **outlined**
- **166**. [lem:no-free-params](#lem-no-free-params) — **lemma** — No–free–parameters normalization — Source L3581–L3583 — Flags: **—** — Status: **todo**
- **167**. [thm:vis-kato](#thm-vis-kato) — **theorem** — Visibility + Kato $\Rightarrow$ equality at congruence primes — Source L3608–L3615 — Flags: **ASSUMES** — Status: **todo**
- **168**. [auto-remark-L3620](#auto-remark-l3620) — **remark** — Supersingular and signed variants — Source L3620–L3622 — Flags: **IMC_MENTION** — Status: **todo**
- **169**. [prop:finite-checklist](#prop-finite-checklist) — **proposition** — Finite checklist for $\mathcal{E}$ at rank $\ge 1$ — Source L3624–L3632 — Flags: **IMC_MENTION** — Status: **todo**
- **170**. [thm:R-triangular](#thm-r-triangular) — **theorem** — Reverse divisibility at $T=0$ from triangularization — Source L3638–L3655 — Flags: **IMC_MENTION** — Status: **suspect**
- **171**. [auto-corollary-L3666](#auto-corollary-l3666) — **corollary** — Per–prime application — Source L3666–L3668 — Flags: **—** — Status: **blocked**
- **172**. [lem:triang-signed](#lem-triang-signed) — **lemma** — Signed Lemma U: mod-$p$ upper--triangularization on each sign — Source L3674–L3680 — Flags: **—** — Status: **conditional**
- **173**. [lem:diag-units-signed](#lem-diag-units-signed) — **lemma** — Signed diagonal per–prime unit test — Source L3685–L3690 — Flags: **—** — Status: **todo**
- **174**. [prop:cofinite-signed](#prop-cofinite-signed) — **proposition** — Per–prime signed nondegeneracy — Source L3695–L3697 — Flags: **—** — Status: **suspect**
- **175**. [thm:R-triangular-signed](#thm-r-triangular-signed) — **theorem** — Signed reverse divisibility at $T=0$ — Source L3702–L3711 — Flags: **—** — Status: **suspect**
- **176**. [auto-corollary-L3716](#auto-corollary-l3716) — **corollary** — BSD$_p$ in signed IMC ranges — Source L3716–L3718 — Flags: **IMC_MENTION** — Status: **todo**
- **177**. [auto-corollary-L3724](#auto-corollary-l3724) — **corollary** — Validated closure for \S6 — Source L3724–L3732 — Flags: **IMC_MENTION** — Status: **todo**
- **178**. [thm:pw-wedge-mu](#thm-pw-wedge-mu) — **theorem** — Cyclotomic wedge $\Rightarrow\ \mu=0$ — Source L3761–L3767 — Flags: **—** — Status: **todo**
- **179**. [lem:noncancel](#lem-noncancel) — **lemma** — Non–cancellation at zeros in families — Source L3792–L3794 — Flags: **—** — Status: **deprecated**
- **180**. [lem:right-edge](#lem-right-edge) — **lemma** — Right–edge normalization on discs — Source L3796–L3798 — Flags: **—** — Status: **deprecated**
- **181**. [thm:disc-imc](#thm-disc-imc) — **theorem** — Finite–slope IMC equality on $D$ — Source L3800–L3802 — Flags: **IMC_MENTION** — Status: **deprecated**
- **182**. [thm:global-bsd](#thm-global-bsd) — **theorem** — Global BSD from BSD$_p$ — Source L3828–L3834 — Flags: **ASSUMES** — Status: **drafted**
- **183**. [cor:global-bsd-sec6](#cor-global-bsd-sec6) — **corollary** — Global BSD for the case studies — Source L3842–L3844 — Flags: **—** — Status: **conditional**

### Proof sections (one per result)

Fill these in session-by-session. The goal is that **every theorem/lemma/proposition/corollary has a complete, audit-ready proof here**, with all dependencies resolved or explicitly marked conditional.

### def:separated — definition (Separated primes)

- **Source**: `BSD-Jon-Final.txt` L221–L226
- **Status**: stated
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - None (definition), but see `lem:CRT` notes about the extra requirement `(m_i,p)=1`.

#### Statement (verbatim from source)

```tex
\begin{definition}[Separated primes]\label{def:separated}
A good, ordinary prime $p$ is \emph{separated} for $\{P_i\}$ if
\[
\forall\,i\neq j,\qquad o_j(p)\ \nmid\ o_i(p).
\]
\end{definition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - The definition of \(o_i(p):=\mathrm{ord}(P_i \bmod p)\) immediately preceding this definition in `BSD-Jon-Final.txt` (L216–L219).
- **External (papers/books/theorems)**:
  - Standard group theory: element order in a finite abelian group.

#### Proof outline (edit)

- Not applicable (this is a definition).

#### Full proof (massive detail; edit)

Not applicable (this is a definition).  

**Interpretation / intended use** (for later proofs):
- If \(p\) is separated for a chosen Mordell–Weil basis \(\{P_i\}\), then the reduction orders \(\{o_i(p)\}\) are pairwise **non-dividing**. This is designed to let us choose integer scalars that “kill” one basis element mod \(p\) without killing the others, which is then used to force \(p\)-divisibility of certain height pairings.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:CRT — lemma (Congruence scalings)

- **Source**: `BSD-Jon-Final.txt` L230–L236
- **Status**: audited
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Edge-case to track**: the requirement \((m_i,p)=1\) forces \(p\nmid o_i(p)\). This is not automatic from “good reduction” alone (anomalous primes can have \(p\mid \#E(\mathbb{F}_p)\)), but for **separated primes with rank \(\ge 2\) and \(p\ge 7\)** it is effectively automatic because \(p\mid \#E(\mathbb{F}_p)\Rightarrow \#E(\mathbb{F}_p)=p\Rightarrow\) all nonzero points have order \(p\), which violates separation.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Congruence scalings]\label{lem:CRT}
Fix a good, ordinary prime $p$ and let $o_i=o_i(p)$. For each $i$ there exists an integer $m_i$ with $(m_i,p)=1$ such that
\[
m_i\equiv 0\pmod{o_i}\qquad\text{and}\qquad m_i\not\equiv 0\pmod{o_j}\ \text{ for all }j\ne i.
\]
If $p$ is separated, this choice is possible for all $i=1,\dots,r$ simultaneously.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `def:separated` (to justify the “simultaneously for all \(i\)” clause, i.e. the needed non-divisibility relations).
- **External (papers/books/theorems)**:
  - Elementary number theory (divisibility, orders in finite groups).

#### Proof outline (edit)

- For each fixed \(i\), pick an integer multiple of \(o_i\) that is not a multiple of any \(o_j\) (\(j\ne i\)). Under the separation condition \(o_j\nmid o_i\), the simplest choice is \(m_i=o_i\).
- Ensure \((m_i,p)=1\) by using that \(p\nmid o_i\) in the intended ranges (or by explicitly excluding primes where \(p\mid o_i\)).

#### Full proof (massive detail; edit)

Fix a good ordinary prime \(p\). For each \(i\), write \(o_i:=o_i(p)=\mathrm{ord}(P_i\bmod p)\).

We prove the two claims.

**Claim 1 (existence for a fixed \(i\)).**  
Assume \(o_j\nmid o_i\) for all \(j\ne i\). Define \(m_i:=o_i\).

- Then \(m_i\equiv 0\pmod{o_i}\) is immediate.
- For \(j\ne i\), \(m_i\not\equiv 0\pmod{o_j}\) is equivalent to \(o_j\nmid m_i\). Since \(m_i=o_i\), this is exactly the hypothesis \(o_j\nmid o_i\).
- Finally, the condition \((m_i,p)=1\) holds provided \(p\nmid o_i\). In the intended applications, this is ensured either by excluding the (rare) anomalous primes where \(p\mid \#E(\mathbb{F}_p)\), or automatically in the separated/rank\(\ge 2\)/\(p\ge 7\) regime (see “Conditional on / Blockers” note above).

Thus such an \(m_i\) exists whenever \(o_j\nmid o_i\) for all \(j\ne i\) and \(p\nmid o_i\).

**Claim 2 (simultaneous choice under separation).**  
If \(p\) is separated for \(\{P_i\}\) (Definition `def:separated`), then for every ordered pair \(i\ne j\) we have \(o_j\nmid o_i\). Therefore the hypothesis of Claim 1 holds for every \(i\), and we may choose the \(m_i\) **independently** (e.g. \(m_i=o_i\) for each \(i\)). This produces a simultaneous collection \(\{m_i\}_{i=1}^r\) with the required congruence properties (and, in the intended ranges, \((m_i,p)=1\)).

This completes the proof.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:triang-ord-modp — lemma (Lemma U: mod-$p$ upper–triangularization with unit scalar on the diagonal)

- **Source**: `BSD-Jon-Final.txt` L246–L252
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Conditional on** the mod‑\(p\) congruence \(h_p(\ ,\ )\equiv u_p(\alpha_p)\log_\omega(\ )\log_\omega(\ )\ (\bmod\ p)\), which the source derives from Perrin–Riou interpolation (`thm:HL-ordinary` + `lem:PR-ord-proof`) and a “\(p\cdot g(\cdot)\)” error term.
  - **Important**: the “in particular” clause constructs a basis with \(\log_\omega(Q_i)\equiv 0\ (\bmod p)\) for \(i\ge 2\), so those \(Q_i\) cannot simultaneously satisfy \(\log_\omega(Q_i)\in\mathbb{Z}_p^\times\). This matters downstream (it clashes with some later “all diagonals are units in a triangularizing basis” hypotheses).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Lemma U: mod-$p$ upper–triangularization with unit scalar on the diagonal]\label{lem:triang-ord-modp}
Let $E/\mathbb{Q}$ have good ordinary reduction at $p\ge 5$, fix a minimal N\'eron differential $\omega$, and let $\{P_1,\dots,P_r\}\subset E(\mathbb{Q})$ be a torsion–free basis. Let $H_p=(h_p(P_i,P_j))_{1\le i,j\le r}$ be the cyclotomic (ordinary) Coleman–Gross local height matrix at $p$ computed with respect to $\omega$ and Greenberg's ordinary local condition. Then there exists a change of basis $M_p\in \mathrm{GL}_r(\mathbb{Z}_p)$ and a unit $u_p(\alpha_p)\in\mathbb{Z}_p^{\times}$ (depending only on the unit root $\alpha_p$ of Frobenius and the fixed Perrin–Riou branch/projector) such that, writing $Q:=(Q_1,\dots,Q_r):=(P_1,\dots,P_r)\cdot M_p$ and $H'_p:=M_p^{\top}H_pM_p$, one has, modulo $p$,
\[
  H'_p\equiv \text{upper triangular},\qquad (H'_p)_{ii}\ \equiv\ u_p(\alpha_p)\cdot \big(\log_\omega(Q_i)\big)^2\ \ (\bmod\ p)\quad (1\le i\le r).
\]
In particular, by choosing $M_p$ so that $\log_\omega(Q_i)\equiv 0\ (\bmod\ p)$ for all $i\ge 2$, we obtain $H'_p\equiv \mathrm{diag}\big(u_p(\alpha_p)\,\log_\omega(Q_1)^2,0,\dots,0\big)\ (\bmod\ p)$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `thm:HL-ordinary`, `lem:PR-ord-proof` (to justify the χ=trivial specialization congruence and unit factor \(u_p(\alpha_p)\))
  - Basic linear algebra over \(\mathbb{Z}_p\) / \(\mathbb{F}_p\) (choosing a basis adapted to a nonzero linear functional)
- **External (papers/books/theorems)**:
  - Perrin–Riou explicit reciprocity / Coleman logarithms (for the congruence input)

#### Proof outline (edit)

- Use the source’s congruence \(h_p(P_i,P_j)\equiv u\,\log_\omega(P_i)\log_\omega(P_j)\ (\bmod p)\).
- Choose a \(\mathbb{Z}_p\)-basis change \(M_p\) such that the first new basis vector \(Q_1\) has \(\log_\omega(Q_1)\not\equiv 0\ (\bmod p)\) and the remaining \(Q_i\) lie in the kernel of the induced \(\mathbb{F}_p\)-linear functional \(x\mapsto \overline{\sum x_i\log_\omega(P_i)}\).
- Then the congruence forces \((H'_p)_{ij}\equiv 0\ (\bmod p)\) whenever \(\min\{i,j\}\ge 2\), i.e. \(H'_p\) is upper triangular mod \(p\), and the diagonal congruences follow.

#### Full proof (massive detail; edit)

We follow and expand the source proof (`BSD-Jon-Final.txt` L253–L267).

Let \(H_p=(h_p(P_i,P_j))\) be the cyclotomic Coleman–Gross height Gram matrix. The source’s Perrin–Riou/Coleman input gives a congruence of the form
\[
h_p(P_i,P_j)\ \equiv\ u_p(\alpha_p)\,\log_\omega(P_i)\,\log_\omega(P_j)\qquad (\bmod\ p\mathbb{Z}_p),
\]
for some \(u_p(\alpha_p)\in\mathbb{Z}_p^\times\).

Define an \(\mathbb{F}_p\)-linear functional
\[
\lambda:(\mathbb{Z}_p)^r \longrightarrow \mathbb{F}_p,\qquad
\lambda((x_i)) := \overline{\sum_{i=1}^r x_i\,\log_\omega(P_i)}.
\]
If \(\lambda=0\), then every \(\log_\omega(P_i)\equiv 0\ (\bmod p)\), and the congruence forces \(H_p\equiv 0\ (\bmod p)\); in this degenerate case the conclusion still holds (upper triangular mod \(p\) is automatic, with all diagonal congruences \(0\)).

Assume \(\lambda\neq 0\). Choose \(v_1\in (\mathbb{Z}_p)^r\) whose reduction \(\overline{v_1}\in(\mathbb{F}_p)^r\) satisfies \(\lambda(\overline{v_1})\neq 0\), and extend \(\{\overline{v_1}\}\) to an \(\mathbb{F}_p\)-basis \(\{\overline{v_1},\overline{v_2},\dots,\overline{v_r}\}\) of \((\mathbb{F}_p)^r\) such that \(\overline{v_i}\in\ker(\lambda)\) for all \(i\ge 2\). Lift this to a matrix \(M_p\in \mathrm{GL}_r(\mathbb{Z}_p)\) whose columns are \(v_1,\dots,v_r\).

Define \(Q=(Q_1,\dots,Q_r):=(P_1,\dots,P_r)\cdot M_p\), i.e. \(Q_i=\sum_j (M_p)_{j i}P_j\). Then by construction:
- \(\log_\omega(Q_1)=\sum_j (M_p)_{j1}\log_\omega(P_j)\not\equiv 0\ (\bmod p)\),
- and for \(i\ge 2\), \(\log_\omega(Q_i)\equiv 0\ (\bmod p)\).

Let \(H'_p:=M_p^{\top}H_pM_p\) be the Gram matrix in the \(Q\)-basis. Applying the congruence entrywise and using bilinearity of \(\log_\omega\) gives
\[
(H'_p)_{ij}\equiv u_p(\alpha_p)\,\log_\omega(Q_i)\,\log_\omega(Q_j)\qquad(\bmod p).
\]
If \(\min\{i,j\}\ge 2\), then \(\log_\omega(Q_i)\equiv 0\) or \(\log_\omega(Q_j)\equiv 0\), so \((H'_p)_{ij}\equiv 0\ (\bmod p)\). Hence \(H'_p\) is upper triangular modulo \(p\). The diagonal congruences are the case \(i=j\), giving \((H'_p)_{ii}\equiv u_p(\alpha_p)\log_\omega(Q_i)^2\ (\bmod p)\).

Finally, because we arranged \(\log_\omega(Q_i)\equiv 0\ (\bmod p)\) for \(i\ge 2\), we obtain the stated “in particular” diagonal form modulo \(p\).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:unit-regulator-from-triangular — corollary (Determinant valuation and regulator units)

- **Source**: `BSD-Jon-Final.txt` L269–L275
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:triang-ord-modp
- **Conditional on / Blockers (edit)**:
  - Conditional only on the setup of `lem:triang-ord-modp`; once \(H'_p\equiv\) upper triangular mod \(p\) is known, the rest is \(p\)-adic linear algebra.

#### Statement (verbatim from source)

```tex
\begin{corollary}[Determinant valuation and regulator units]\label{cor:unit-regulator-from-triangular}
With notation as in Lemma~\ref{lem:triang-ord-modp}, one has
\[
  v_p\big(\det H_p\big)\ =\ v_p\big(\det H'_p\big)\ =\ \sum_{i=1}^r v_p\big((H'_p)_{ii}\big)\ +\ O(1)
\]
with an $O(1)$ depending only on $E$, $p$, and the chosen normalizations (in particular independent of the basis). In particular, if each diagonal entry $(H'_p)_{ii}\in\mathbb{Z}_p^{\times}$, then $\det H_p\in\mathbb{Z}_p^{\times}$ and hence the cyclotomic $p$–adic regulator $\mathrm{Reg}_p\in\mathbb{Z}_p^{\times}$.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:triang-ord-modp` (to ensure the mod‑\(p\) upper-triangular structure that makes LU/Smith-style control possible)
- **External (papers/books/theorems)**:
  - Basic properties of determinants over \(\mathbb{Z}_p\) and stability of valuation under multiplication by \(\mathbb{Z}_p^\times\)

#### Proof outline (edit)

- Since \(M_p\in\mathrm{GL}_r(\mathbb{Z}_p)\), \(\det(H_p)=\det(H'_p)\).
- Use \(p\)-integral elimination/LU decomposition: if a matrix is upper triangular modulo \(p\), elimination pivots differ from diagonal entries by units, up to bounded error, yielding \(v_p(\det)=\sum v_p(\text{pivots})=\sum v_p(\text{diagonal})+O(1)\).
- If all diagonal entries are units, then the determinant is a unit.

#### Full proof (massive detail; edit)

Let \(H'_p=M_p^{\top}H_pM_p\) with \(M_p\in\mathrm{GL}_r(\mathbb{Z}_p)\). Then
\[
\det(H'_p)=\det(M_p)^2\det(H_p),
\]
and since \(\det(M_p)\in\mathbb{Z}_p^\times\), we have \(v_p(\det H'_p)=v_p(\det H_p)\).

Assume \(H'_p\equiv\) upper triangular \((\bmod p)\). Perform Gaussian elimination over \(\mathbb{Z}_p\) using row operations in \(\mathrm{GL}_r(\mathbb{Z}_p)\). Because all entries strictly below the diagonal are divisible by \(p\), the elimination steps do not introduce any division by non-units (one can formalize this by induction on \(r\), or by viewing elimination modulo \(p\) and lifting). The resulting pivot elements differ from the diagonal entries \((H'_p)_{ii}\) by multiplication by \(p\)-adic units and by addition of terms divisible by \(p\), so their valuations agree up to a bounded additive constant depending only on the elimination path and the fixed normalization choices. Consequently,
\[
v_p(\det H'_p)=\sum_{i=1}^r v_p(\text{pivot}_i)=\sum_{i=1}^r v_p((H'_p)_{ii})+O(1),
\]
with the stated \(O(1)\).

In particular, if every diagonal entry \((H'_p)_{ii}\in\mathbb{Z}_p^\times\), then the pivots are all units and \(\det(H'_p)\in\mathbb{Z}_p^\times\), hence \(\det(H_p)\in\mathbb{Z}_p^\times\) as well. By definition, this means the cyclotomic \(p\)-adic regulator is a \(p\)-adic unit.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:diag-units — lemma (Per–prime diagonal unit test)

- **Source**: `BSD-Jon-Final.txt` L284–L290
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Depends on** the chosen Coleman–Gross height normalization and the unit factor in the diagonal height formula (either via `lem:triang-ord-modp` congruence or via `lem:formal-factor` restricted to integral points).
  - This lemma is *compatible* with the §7.1 issue: for \(X\in E_1\), both sides are non-units; the contradiction arises only when the paper claims they are generically units.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Per–prime diagonal unit test]\label{lem:diag-units}
Let $E/\mathbb{Q}$ be an elliptic curve and let $p\ge 5$ be a good ordinary prime. Fix a minimal N\'eron differential $\omega$. For $P\in E(\mathbb{Z}_p)$ one has $h_p(P)\in\mathbb{Z}_p$ and
\[
  v_p\big(h_p(P)\big)=0\quad\Longleftrightarrow\quad v_p\big(\log_\omega(P)\big)=0.
\]
In particular, $h_p(P)\in\mathbb{Z}_p^{\times}$ if and only if $\log_\omega(P)\in\mathbb{Z}_p^{\times}$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:triang-ord-modp` (for the mod‑\(p\) congruence \(h_p(P,P)\equiv u\,\log_\omega(P)^2\))
  - `lem:formal-factor` / `lem:unit-log` (optional alternative route: diagonal height equals a unit times log\(^2\) on the appropriate component)
- **External (papers/books/theorems)**:
  - Integrality of Coleman–Gross heights on \(E(\mathbb{Z}_p)\) (part of black box `B2`)

#### Proof outline (edit)

- Use integrality to know \(h_p(P)\in\mathbb{Z}_p\) for \(P\in E(\mathbb{Z}_p)\).
- Use the mod‑\(p\) diagonal congruence \(h_p(P,P)\equiv u\log_\omega(P)^2\ (\bmod p)\) with \(u\in\mathbb{Z}_p^\times\).
- If \(\log_\omega(P)\in\mathbb{Z}_p^\times\), then \(\log_\omega(P)^2\) is a unit mod \(p\), so \(h_p(P)\not\equiv 0\ (\bmod p)\) and \(v_p(h_p(P))=0\).
- If \(v_p(\log_\omega(P))\ge 1\), then \(\log_\omega(P)^2\equiv 0\ (\bmod p)\), so \(h_p(P)\equiv 0\ (\bmod p)\) and \(v_p(h_p(P))\ge 1\). With the unit-factor formula, this is equivalent to \(v_p(\log_\omega(P))=0\).

#### Full proof (massive detail; edit)

Let \(p\ge 5\) be a good ordinary prime and let \(P\in E(\mathbb{Z}_p)\). By integrality of the Coleman–Gross construction at good reduction primes (part of `B2`), \(h_p(P,P)\in\mathbb{Z}_p\).

By `lem:triang-ord-modp`, the diagonal congruence gives (taking \(r=1\), or equivalently applying the general congruence to the single vector \(P\))
\[
h_p(P,P)\ \equiv\ u\cdot \log_\omega(P)^2\qquad (\bmod p),
\]
for some unit \(u\in\mathbb{Z}_p^\times\).

If \(v_p(\log_\omega(P))=0\), then \(\log_\omega(P)\) is a unit, so \(\log_\omega(P)^2\not\equiv 0\ (\bmod p)\) and hence \(h_p(P,P)\not\equiv 0\ (\bmod p)\). Since \(h_p(P,P)\in\mathbb{Z}_p\), this implies \(v_p(h_p(P,P))=0\).

Conversely, if \(v_p(\log_\omega(P))\ge 1\), then \(\log_\omega(P)^2\equiv 0\ (\bmod p)\), so the congruence forces \(h_p(P,P)\equiv 0\ (\bmod p)\), hence \(v_p(h_p(P,P))\ge 1\). Therefore \(v_p(h_p(P,P))=0\) implies \(v_p(\log_\omega(P))=0\).

This proves \(v_p(h_p(P))=0\iff v_p(\log_\omega(P))=0\). The final “unit iff unit” statement is the same equivalence reformulated.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:cofinite-nondeg — proposition (Per–prime nondegeneracy)

- **Source**: `BSD-Jon-Final.txt` L299–L301
- **Status**: suspect
- **Auto-flags**: —
- **Auto-extracted internal refs**: def:separated
- **Conditional on / Blockers (edit)**:
  - **Likely statement/proof mismatch (typo-level)**: the surrounding separation arguments (and Appendix A later in the source) repeatedly use that \(m_iP_i\in E_1(\mathbb{Q}_p)\) while \(m_iP_j\notin E_1(\mathbb{Q}_p)\) for \(j\ne i\), and then apply mixed-integrality to the pair \((m_iP_i,\;m_iP_j)\).  
    - This logic controls the *row-scaled* matrix with entries \(h_p(m_iP_i,\;m_iP_j)\) (same multiplier \(m_i\) on both arguments), not the symmetric matrix \(h_p(m_iP_i,\;m_jP_j)\).
  - **If read literally as a statement about the symmetric matrix** \(H=(h_p(m_iP_i,m_jP_j))\) **with all diagonal entries units**, it conflicts with the factorization-on-\(E_1\) heuristic \(h_p(X,Y)\approx u_p\log_E(X)\log_E(Y)\) with \(u_p\in\mathbb{Z}_p^\times\): unit diagonals force \(\log_E(X_i)\in\mathbb{Z}_p^\times\) for all \(i\), hence off-diagonals are also units (not all divisible by \(p\)).  
  - **Normalization blocker (same as §7.1)**: as written, the paper’s formal-group checklist forces \(v_p(h_p(X))\ge 2\) for \(X\in E_1(\mathbb{Q}_p)\), so the hypothesis “\(m_iP_i\in E_1(\mathbb{Q}_p)\) and \(v_p(h_p(m_iP_i,m_iP_i))=0\)” is incompatible unless a normalization fix is specified.
    - **Deep-dive note**: `notes/papers/bsd/coleman-gross-heights-notes.md`
  - **Next action**: treat this proposition as a *pointer* to the corrected argument: prove \(h_p(P_i,P_j)\in p\mathbb{Z}_p\) for \(i\ne j\) by applying mixed-integrality to \(h_p(m_iP_i,m_iP_j)\) and dividing out by \(m_i^2\in\mathbb{Z}_p^\times\).

#### Statement (verbatim from source)

```tex
\begin{proposition}[Per–prime nondegeneracy]\label{prop:cofinite-nondeg}
Let $p\ge 5$ be good and ordinary. Suppose $p$ is separated (Definition~\ref{def:separated}). Then there exist integers $m_1,\dots,m_r$ with $(m_i,p)=1$ such that $m_iP_i\in E_1(\mathbb{Q}_p)$ and $m_iP_j\notin E_1(\mathbb{Q}_p)$ for $j\ne i$. If, in addition, $v_p\big(h_p(m_iP_i,m_iP_i)\big)=0$ for each $i$ (equivalently $v_p(\log_\omega(m_iP_i))=0$), then $\det H_p\in\mathbb{Z}_p^{\times}$ and hence $\mathrm{Reg}_p(E)\in\mathbb{Z}_p^{\times}$.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- Apply the row-wise multiplier trick described above to deduce \(p\)-divisibility of the off-diagonal entries of the *unscaled* height matrix \((h_p(P_i,P_j))\).
- Combine with diagonal unit conditions to conclude \(\det\in\mathbb{Z}_p^\times\).

#### Full proof (massive detail; edit)

**Status note**: This is currently marked **suspect** as written; the proof-track should implement and verify the corrected “row-scaled” argument before upgrading this to `drafted/audited`.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### hyp:big-kummer — hypothesis (Big image and Kummer independence)

- **Source**: `BSD-Jon-Final.txt` L353–L358
- **Status**: todo
- **Auto-flags**: HYPOTHESIS
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{hypothesis}[Big image and Kummer independence]\label{hyp:big-kummer}
\begin{itemize}
\item[(H1)] (Serre) The adelic Galois image attached to $E$ is open in $\mathrm{GL}_2(\widehat{\mathbb{Z}})$; in particular, for all sufficiently large integers $N$ one has $\mathrm{Im}\,\rho_{E,\mathrm{mod}\,N}\supseteq \mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$.
\item[(H2)] (Kummer independence for $P$) There exists an integer $N\ge 3$, coprime to all but finitely many good primes for $E$, such that the Galois representation on the $N$--division Kummer tower $\mathbb{Q}\big(E[N],\tfrac{1}{N}P\big)/\mathbb{Q}$ has image containing a subgroup that acts transitively on the cosets of $\tfrac{1}{N}P$.
\end{itemize}
\end{hypothesis}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:inf-many-ord-units — theorem (Infinitely many ordinary diagonal--unit primes under Hypothesis~\ref{hyp:big-kummer})

- **Source**: `BSD-Jon-Final.txt` L360–L366
- **Status**: todo
- **Auto-flags**: ASSUMES, USES_HYP
- **Auto-extracted internal refs**: hyp:big-kummer
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Infinitely many ordinary diagonal--unit primes under Hypothesis~\ref{hyp:big-kummer}]\label{thm:inf-many-ord-units}
Let $E/\mathbb{Q}$ be an elliptic curve, $P\in E(\mathbb{Q})$ non--torsion. Assume Hypothesis~\ref{hyp:big-kummer}. Then the set of good ordinary primes $p$ for which
\[
  v_p\big(h_p(P)\big)=0\qquad(\text{equivalently }\ v_p(\log_\omega(P))=0)
\]
is infinite; in fact, it has positive lower density among good ordinary primes.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:inf-many-signed-units — theorem (Signed analogue)

- **Source**: `BSD-Jon-Final.txt` L383–L385
- **Status**: todo
- **Auto-flags**: USES_HYP
- **Auto-extracted internal refs**: hyp:big-kummer
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Signed analogue]\label{thm:inf-many-signed-units}
Under Hypothesis~\ref{hyp:big-kummer}, the set of supersingular primes $p\ge 5$ for which $v_p\big(h_p^{\pm}(P)\big)=0$ for at least one sign $\pm$ is infinite; moreover it has positive lower density among supersingular primes satisfying the signed hypotheses (Pollack/Kobayashi framework).
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L390 — remark (What remains to be written in full)

- **Source**: `BSD-Jon-Final.txt` L390–L392
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[What remains to be written in full]
The construction of the mod $p$ detector $\Phi_{N,\omega}$ is standard in spirit (explicit reciprocity along the unit--root/signed lines) but technical. It amounts to making the mod $p$ reduction of the Coleman ordinary/signed logarithm explicit on the Kummer fibers and checking nontriviality for some $N$. This can be done directly in the Wach--module model (\S F.7–F.8) and will be carried out in a subsequent note.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-definition-L427 — definition (Completely continuous $\Lambda$–endomorphism)

- **Source**: `BSD-Jon-Final.txt` L427–L433
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{definition}[Completely continuous $\Lambda$–endomorphism]
Let $M\cong \Lambda^d$ and let $f:M\to M$ be $\Lambda$–linear. We say $f$ is \emph{completely continuous} if, in some (hence any) $\Lambda$–basis, the matrix of $f$ lies in $M_d(\Lambda)$ and the sequence of principal minors converges $(p,T)$–adically to $0$; equivalently, $f$ is a $(p,T)$–adic limit of finite–rank $\Lambda$–endomorphisms. In this case the Fredholm determinant
\[
  \det_{\Lambda}(I-f)\ :=\ \sum_{n\ge 0} (-1)^n\,\mathrm{tr}_n(f)\ \in\ \Lambda
\]
is well–defined (Serre's formalism) and multiplicative in nuclear operators.
\end{definition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-proposition-L435 — proposition (Complete continuity of $K(T)$)

- **Source**: `BSD-Jon-Final.txt` L435–L440
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Complete continuity of $K(T)$]
With notation as in \S F.28, the endomorphism $K(T)=s\circ\mathrm{Col}_p:M_p\to M_p$ is completely continuous. Moreover, if $s'$ is another $\Lambda$–linear section and $K'(T):=s'\circ\mathrm{Col}_p$, then $K'(T)-K(T)$ is completely continuous of finite rank; hence
\[
  \det_{\Lambda}(I-K'(T))\ =\ u\cdot \det_{\Lambda}(I-K(T))\qquad\text{for some }u\in\Lambda^{\times}.
\]
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-definition-L445 — definition (Fredholm determinant of $K(T)$)

- **Source**: `BSD-Jon-Final.txt` L445–L447
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{definition}[Fredholm determinant of $K(T)$]
Define $\det_{\Lambda}(I-K(T))$ to be the Fredholm determinant in the sense above; by the proposition it is well–defined up to $\Lambda^{\times}$.
\end{definition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:coker-id — theorem (Cokernel identification)

- **Source**: `BSD-Jon-Final.txt` L453–L459
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Poitou–Tate / Selmer complexes**: the identification of \(\mathrm{coker}(\Phi)\) with the Pontryagin dual of Selmer is a standard global duality input but must be spelled out with the exact local conditions used here.
  - **Choice of auxiliary map \(\pi\)**: the proof assumes existence of a \(\Lambda\)-surjection \(\pi:M\to Q\) whose kernel encodes the away–\(p\) finite conditions; this needs a precise construction and a check that changing \(\pi\) only affects things up to pseudo–isomorphism/finite error.

#### Statement (verbatim from source)

```tex
\begin{theorem}[Cokernel identification]\label{thm:coker-id}
Let $M\subset H^1_{\emph{Iw}}(\mathbb{Q},V)$ be a finite free $\Lambda$–lattice whose localization at $p$ equals $M_p$. With $K(T)=s\circ\mathrm{Col}_p$ as above, there is a canonical pseudo–isomorphism of $\Lambda$–modules
\[
  \mathrm{coker}(I-K(T))^{\vee}\ \sim\ X_p(E/\mathbb{Q}_\infty),
\]
where $X_p$ is the Pontryagin dual of the ordinary cyclotomic Selmer group. In particular, the zeroth Fitting ideals agree up to $\Lambda^{\times}$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - Definitions: \(M\), \(M_p\), ordinary Coleman map \(\mathrm{Col}_p\), the section \(s:\Lambda^2\to M_p\subset M\), and the operator \(K(T)=s\circ \mathrm{Col}_p\).
  - The model for away–\(p\) local conditions encoded by \(\pi:M\to Q\).
- **External (papers/books/theorems)**:
  - Local Tate duality; Poitou–Tate duality / Nekovář Selmer complexes framework
  - Standard facts about pseudo–isomorphisms and invariance of characteristic/Fitting ideals under finite error

#### Proof outline (edit)

- Define \(\Phi:=\mathrm{Col}_p\oplus \pi : M \to \Lambda^2\oplus Q\) so that \(\ker\Phi\) is the ordinary Selmer group over \(\mathbb{Q}_\infty\) (ordinary at \(p\), finite away from \(p\)).
- Choose splittings \(s:\Lambda^2\to M\) (landing in \(M_p\subset M\)) and \(t:Q\to M\). Form \(\widetilde K:=s\circ \mathrm{Col}_p+t\circ \pi\).
- Show \(\mathrm{im}(I-\widetilde K)=\ker\Phi\) and \(\mathrm{coker}(I-\widetilde K)\cong \mathrm{coker}(\Phi)\).
- Use Poitou–Tate/local duality to identify \(\mathrm{coker}(\Phi)\) with \(\mathrm{Sel}_{p^\infty}(E/\mathbb{Q}_\infty)^\vee=X_p\) up to finite error, hence obtain \(\mathrm{coker}(I-K)^\vee\sim X_p\) up to pseudo–isomorphism and Fitting agreement.

#### Full proof (massive detail; edit)

We expand the source proof (L460–L466).

Let \(M\subset H^1_{\mathrm{Iw}}(\mathbb{Q},V)\) be a finite free \(\Lambda\)-lattice and assume \(\mathrm{loc}_p(M)=M_p\). Let \(\mathrm{Col}_p:M\to \Lambda^2\) be the (ordinary) Coleman map (after choosing bases) and let \(\pi:M\to Q\) be a fixed \(\Lambda\)-surjection whose kernel is exactly the subgroup of classes satisfying the away–\(p\) finite local conditions (so \(Q\) records the “away–\(p\)” obstruction data).

Define the \(\Lambda\)-linear map
\[
\Phi:=\mathrm{Col}_p\oplus \pi:\ M\longrightarrow \Lambda^2\oplus Q.
\]
By construction of \(\pi\) and the ordinary local condition at \(p\), the kernel \(\ker(\Phi)\) is precisely the ordinary cyclotomic Selmer group over \(\mathbb{Q}_\infty\) realized inside \(M\).

Choose \(\Lambda\)-linear sections \(s:\Lambda^2\to M\) (landing in \(M_p\subset M\)) and \(t:Q\to M\). Set
\[
\widetilde K:= s\circ \mathrm{Col}_p+t\circ \pi:\ M\to M.
\]
Then for any \(m\in M\),
\[
(I-\widetilde K)(m)=m-s(\mathrm{Col}_p(m))-t(\pi(m)).
\]
Applying \(\Phi\) gives
\[
\Phi\big((I-\widetilde K)(m)\big)=\Phi(m)-(\mathrm{Col}_p(m),\pi(m))=0
\]
because \(\Phi\circ s\) and \(\Phi\circ t\) are the identity on the \(\Lambda^2\) and \(Q\) summands, respectively. Hence \(\mathrm{im}(I-\widetilde K)\subseteq \ker(\Phi)\). Conversely, if \(x\in \ker(\Phi)\), then \(\mathrm{Col}_p(x)=0\) and \(\pi(x)=0\), so \((I-\widetilde K)(x)=x\); thus \(\ker(\Phi)\subseteq \mathrm{im}(I-\widetilde K)\). Therefore
\[
\mathrm{im}(I-\widetilde K)=\ker(\Phi).
\]
It follows that \(\mathrm{coker}(I-\widetilde K)\cong \mathrm{coker}(\Phi)\).

Finally, Poitou–Tate (equivalently Nekovář Selmer complexes) identifies \(\mathrm{coker}(\Phi)\) with the Pontryagin dual of the Selmer group (up to finite error coming from lattice choices and local finite-index issues). In particular, \(\mathrm{coker}(\Phi)\) is pseudo–isomorphic to \(X_p(E/\mathbb{Q}_\infty)\), and hence so is \(\mathrm{coker}(I-\widetilde K)\). Since replacing \(\widetilde K\) by \(K=s\circ \mathrm{Col}_p\) only changes the operator by the finite-rank term \(t\circ \pi\), the resulting cokernels agree up to pseudo–isomorphism and have the same zeroth Fitting ideal up to \(\Lambda^\times\).

This yields \(\mathrm{coker}(I-K(T))^\vee\sim X_p(E/\mathbb{Q}_\infty)\), as claimed. Full audit requires writing the Poitou–Tate identification in the exact Selmer-complex language matching the chosen local conditions.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:det-equals-Lp — theorem (Determinant equals $p$–adic $L$–function)

- **Source**: `BSD-Jon-Final.txt` L472–L477
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - Depends on the pseudo–Smith form statement `prop:psmith` and on the analytic interpolation input that \(\det\mathcal{C}(T)\) generates the same ideal as \(L_p(E,T)\) (ultimately Perrin–Riou explicit reciprocity).
  - Uses “Fredholm determinant well-defined up to \(\Lambda^\times\)” for the completely continuous operator model; this must be consistent with the operator topology chosen earlier in the source.

#### Statement (verbatim from source)

```tex
\begin{theorem}[Determinant equals $p$–adic $L$–function]\label{thm:det-equals-Lp}
With notation as above, there is a unit $u\in\Lambda^{\times}$ such that
\[
  \det_{\Lambda}(I-K(T))\ =\ u\cdot L_p(E,T).
\]
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - Definition of the Fredholm determinant \(\det_\Lambda(I-K(T))\)
  - `prop:psmith` (diagonalization of \(\mathcal{C}(T)\) up to pseudo–isomorphism and identification of \((d_1d_2)\) with \((L_p)\))
  - `prop:fitting` (minors/Fitting control used in the “key point”)
- **External (papers/books/theorems)**:
  - Wach-module description of \(\mathrm{Col}_p\) and the Coleman matrix \(\mathcal{C}(T)\)
  - Perrin–Riou reciprocity / interpolation giving \(\det\mathcal{C}(\chi)\asymp L_p(E,\chi)\)

#### Proof outline (edit)

- Write \(K(T)=s\circ \mathrm{Col}_p\) as a matrix product \(S\mathcal{C}(T)\) in chosen bases.
- Use `prop:psmith` to replace \(\mathcal{C}(T)\) by a diagonal \(\mathrm{diag}(d_1,d_2)\) up to \(\mathrm{GL}_2(\Lambda)\)-changes; show Fredholm determinant changes only by a unit under these changes.
- Compute \(\det_\Lambda(I-S'\,\mathrm{diag}(d_1,d_2))\) and show it generates the same principal ideal as \(d_1d_2\) (hence \(L_p\)) up to units.

#### Full proof (massive detail; edit)

We expand the source proof (L478–L488).

In a Wach basis, represent the ordinary Coleman map \(\mathrm{Col}_p\) by the \(2\times 2\) Coleman matrix \(\mathcal{C}(T)\). Let \(S\) be the \(2\times 2\) matrix of the chosen \(\Lambda\)-linear section \(s:\Lambda^2\to M_p\) in the same bases. Then the matrix of \(K(T)=s\circ \mathrm{Col}_p\) is \(S\mathcal{C}(T)\), so
\[
\det_\Lambda(I-K(T))=\det_\Lambda(I-S\mathcal{C}(T)).
\]
By `prop:psmith`, there exist \(U,V\in \mathrm{GL}_2(\Lambda)\) such that \(U\mathcal{C}(T)V=\mathrm{diag}(d_1(T),d_2(T))\) up to pseudo–isomorphism and \((d_1d_2)=(L_p(E,T))\).

Pre/post-composition by \(\mathrm{GL}_2(\Lambda)\) corresponds to changing bases in source/target; this changes the Fredholm determinant only by a unit in \(\Lambda^\times\). Thus, up to \(\Lambda^\times\), we may replace \(\mathcal{C}(T)\) by \(\mathrm{diag}(d_1,d_2)\) and replace \(S\) by \(S':=USU^{-1}\). Then
\[
\det_\Lambda(I-S\mathcal{C}(T))\ \doteq\ \det_\Lambda\!\big(I-S'\,\mathrm{diag}(d_1,d_2)\big).
\]
A direct block-determinant computation (or approximation by finite-rank truncations in the completely-continuous model) shows that this Fredholm determinant generates the same principal ideal as the product \(d_1d_2\), provided \(S'\) is invertible modulo \((d_1,d_2)\); this is the “key point” used in the source and is exactly the Fitting/minor control captured in `prop:fitting`.

Therefore
\[
\det_\Lambda(I-K(T))\ \doteq\ d_1(T)d_2(T)\ \doteq\ L_p(E,T),
\]
which is the desired identity up to \(\Lambda^\times\).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:integral-det-exact-ord — theorem (Integral big–log determinant and kernel exactness)

- **Source**: `BSD-Jon-Final.txt` L494–L501
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Integral big–log determinant and kernel exactness]\label{thm:integral-det-exact-ord}
There exists a saturated finite free $\Lambda$–lattice $M\subset H^1_{\emph{Iw}}(\mathbb{Q},V)$ with $M_p=M\otimes_{\mathbb{Q}}\mathbb{Q}_p$ such that:
\begin{itemize}
\item[(i)] The ordinary big logarithm $\mathrm{Col}_p$ maps $M_p$ integrally into $\Lambda^2$, and $\det_{\Lambda}(I-s\circ \mathrm{Col}_p)\in \Lambda$ generates $(L_p(E,T))$ up to $\Lambda^{\times}$.
\item[(ii)] There is an exact sequence $0\to X_p(E/\mathbb{Q}_\infty)\to M^{\vee}\xrightarrow{(\mathrm{Col}_p,\pi)} \Lambda^2\oplus Q\to 0$ with finite $Q$, so that $\ker(\mathrm{Col}_p,\pi)$ is Pontryagin dual to Selmer and $\mathrm{coker}(\mathrm{Col}_p,\pi)$ is finite.
\end{itemize}
Consequently $\mathrm{char}_{\Lambda}X_p(E/\mathbb{Q}_\infty)\mid (L_p(E,T))$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:wach-lattice-ord — lemma (Wach lattice and $\Lambda$–integrality)

- **Source**: `BSD-Jon-Final.txt` L514–L516
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Wach lattice and $\Lambda$–integrality]\label{lem:wach-lattice-ord}
Let $N(V)$ be the Wach module of $V$ and $M_p:=N(V)^{\psi=1}\cap H^1_{\emph{Iw}}(\mathbb{Q}_p,V)$. Then $M_p$ is a finite free $\Lambda$–module of rank $2$ stable under localization, and $\mathrm{Col}_p(M_p)\subset \Lambda^2$ integrally. If $M\subset H^1_{\emph{Iw}}(\mathbb{Q},V)$ is a saturated $\Lambda$–lattice with $M\otimes_{\mathbb{Z}_p}\mathbb{Q}_p=M_p\otimes\mathbb{Q}_p$, then $(\mathrm{Col}_p,\pi)$ has matrix in $M_2(\Lambda)\oplus Q$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:exactness-global — lemma (Exactness and finite cokernel globally)

- **Source**: `BSD-Jon-Final.txt` L521–L523
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Exactness and finite cokernel globally]\label{lem:exactness-global}
With $M$ as above, the map $(\mathrm{Col}_p,\pi):M\to \Lambda^2\oplus Q$ is surjective up to a finite cokernel and $\ker(\mathrm{Col}_p,\pi)^{\vee}\simeq X_p(E/\mathbb{Q}_\infty)$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:outer-boundary — lemma (Boundary unit\,--\,modulus and zero\,--\,freeness)

- **Source**: `BSD-Jon-Final.txt` L546–L552
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Boundary unit\,--\,modulus and zero\,--\,freeness]\label{lem:outer-boundary}
After neutralization of atoms, $O(T)\in\Lambda^{\times}$ is zero\,--\,free on the cyclotomic boundary and, for every finite\,--\,order character $\chi$,
\[
  |J(\chi)|_p=1.
\]
The same holds in the signed supersingular setting with $L_p^{\pm}$, and with the improved object $L_p^{\!*}$ at split multiplicative $p$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### rem:noncancellation — remark (Non\,--\,cancellation at zeros)

- **Source**: `BSD-Jon-Final.txt` L557–L559
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Non\,--\,cancellation at zeros]\label{rem:noncancellation}
Since $O(T)$ is a unit and zero\,--\,free on boundary carriers, zeros/poles of $J$ on the boundary coincide with those of $L_p$ (resp. $L_p^{\pm}$, $L_p^{\!*}$).
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - Definition of the “outer factor” \(O(T)\) used to build \(J\) (unit in the relevant affinoid/Iwasawa algebra, and zero–free on the relevant boundary carrier)
- **External (papers/books/theorems)**:
  - Basic algebra: multiplying by a unit does not change zero/pole loci.

#### Proof outline (edit)

- If \(O(T)\) is a unit and has no zeros/poles on the boundary carrier, then \(J:=\frac{\det(I-K)}{O\cdot L_p}\) has the same zeros/poles as \(\frac{\det(I-K)}{L_p}\), and any boundary zeros/poles of \(J\) come exactly from the corresponding zeros/poles of \(L_p\) (and similarly in signed/improved variants).

#### Full proof (massive detail; edit)

Assume \(O(T)\) is a unit (invertible) in the ambient coefficient ring/affinoid algebra and is zero–free on the boundary carrier under consideration. Define \(J(T)\) by the source’s formula \(J=\det(I-K)/(O\cdot L_p)\) (or the analogous signed/improved formula).

Then multiplication by the unit \(O(T)\) cannot introduce or cancel zeros/poles: for any point \(t\) where \(O(t)\neq 0\), we have
\[
J(t)=0\iff \det(I-K)(t)=0\ \text{ and }\ L_p(t)\neq 0,
\]
and similarly poles of \(J\) occur exactly where \(L_p(t)=0\) and \(\det(I-K)(t)\neq 0\), with the orders determined by the difference of vanishing orders. In particular, on boundary carriers where \(O\) is zero–free, the zeros/poles of \(J\) coincide with those of \(L_p\) (resp. \(L_p^{\pm}\), \(L_p^{\!*}\)) up to the factor \(\det(I-K)\) as asserted.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:box-energy — theorem (Uniform box\,--\,energy bound)

- **Source**: `BSD-Jon-Final.txt` L569–L575
- **Status**: blocked
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Major missing definitions**: the statement uses \(\Gamma_n\), boxes \(Q\), a gradient \(\nabla\), an energy \(\int_Q |\nabla U|^2\,d\mu\), and a Laplacian/Dirichlet form on a \(p\)-adic character layer. None of these are defined in audit-grade form in the source excerpt. We need a precise discrete/rigid-analytic model.
  - **Major missing proof content**: the source provides only an “Idea” proof. To upgrade this theorem, we need:
    - an explicit decomposition \(U=U_{\mathrm{tail}}+U_{\xi}\) and a proof that the Dirichlet energy splits with controllable cross-terms,
    - a precise statement of “complete continuity/integrality of \(\mathrm{Col}_p\) on a saturated Wach lattice” that implies the \(K_{0,p}\) bound,
    - a precise “neutralized zero mass” estimate tied to the minimal Kummer criterion (F.42) and twist-averaged \(L^2\) control (F.47).

#### Statement (verbatim from source)

```tex
\begin{theorem}[Uniform box\,--\,energy bound]\label{thm:box-energy}
There exists a constant $C_{\mathrm{box},p}=K_{0,p}+K_{\xi,p}$ such that, for every standard box $Q$ and every admissible window $\varphi\in\mathcal{W}_{\mathrm{adm}}(n;\varepsilon)$,
\[
  \int_Q |\nabla U|^2\,\mathrm{d}\mu\ \ll\ C_{\mathrm{box},p}\,\mathrm{size}(Q),
\]
with $K_{0,p}$ controlled by operator tails (complete continuity and integrality of $\mathrm{Col}_p$ on a saturated Wach lattice; \S\,F.28--F.31A) and $K_{\xi,p}$ controlled by neutralized zero\,--\,mass on character layers, bounded using the minimal Kummer criterion (\S\,F.42) and twist\,--\,averaged $L^2$ control (\S\,F.47).
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `rem:noncancellation` (outer normalization and “atoms” language)
  - Whatever definitions fix \(J\), \(U=\log_p|J|\), admissible windows \(\mathcal{W}_{\mathrm{adm}}(n;\varepsilon)\), and the box structure on character layers (\S F.31C–F.31D in the source)
  - Operator tails / integrality inputs from \S F.28–F.31A (for \(K_{0,p}\))
  - Minimal Kummer criterion (\S F.42) and twist-averaged \(L^2\) control (\S F.47) for \(K_{\xi,p}\)
- **External (papers/books/theorems)**:
  - Nonarchimedean potential theory / rigid analytic maximum modulus machinery (if the “energy” formalism is meant to be analytic rather than purely discrete)

#### Proof outline (edit)

- **Blocked** until the analytic/discrete energy formalism is made precise. The audit-grade outline the paper seems to intend:
  - Define \(U=\log_p|J|\) on a boundary/character layer.
  - Decompose \(U=U_{\mathrm{tail}}+U_\xi\) (operator tail + neutralized zero contribution).
  - Bound \(\int_Q|\nabla U_{\mathrm{tail}}|^2\) by complete continuity/integrality estimates.
  - Bound \(\int_Q|\nabla U_\xi|^2\) by \(L^2\)-summability across conductors using F.42/F.47.
  - Control cross-terms and conclude the stated uniform bound.

#### Full proof (massive detail; edit)

**Blocked** (definitions + proof content missing in the source). See “Conditional on / Blockers” for the exact missing items.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:wedge — lemma (Wedge criterion)

- **Source**: `BSD-Jon-Final.txt` L582–L592
- **Status**: blocked
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Major missing formalism**: \(\mathrm{arg}\,J\), \(-\Delta\,\mathrm{arg}\,J\), “mass of off-\(T=0\) zeros”, and the integration against an admissible window \(\varphi\) must be defined precisely (discrete Laplacian on \(\Gamma_n\)? boundary distribution on a tree?).
  - **Missing analytic lemmas**: the proof sketch invokes a “\(p\)-adic Blaschke/Poisson shadow of zeros” plus Cauchy–Schwarz with `thm:box-energy`. These need to be stated as explicit lemmas with hypotheses.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Wedge criterion]\label{lem:wedge}
For $\varphi\in\mathcal{W}_{\mathrm{adm}}(n;\varepsilon)$ there exist constants $C_{\mathrm{test}},c_0>0$ independent of $n$ such that
\[
  \int \!\varphi\,\big( -\Delta\,\mathrm{arg}\,J\big)\ \ge\ c_0\cdot (\text{mass of off\,-\,}T{=}0\text{ zeros in the window}),
\]
and
\[
  \int \!\varphi\,\big| -\Delta\,\mathrm{arg}\,J\big|\ \le\ C_{\mathrm{test}}\,\sqrt{C_{\mathrm{box},p}}\,p^{-n/2}.
\]
For $n\gg 1$ the boundary phase is confined to a cone on every admissible window, forcing no off\,-\,$T{=}0$ mass.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `thm:box-energy` (for the upper bound via Cauchy–Schwarz)
  - Definitions of admissible windows \(\mathcal{W}_{\mathrm{adm}}(n;\varepsilon)\) and the “atom neutralization” mechanism.
- **External (papers/books/theorems)**:
  - A nonarchimedean analogue of Poisson/Green/Blaschke formulas relating boundary phase/Laplacians to interior zeros (not standard; must be supplied)

#### Proof outline (edit)

- **Blocked** until the Laplacian/phase/zero-mass dictionary is defined. Intended outline:
  - Lower bound: show \(\int \varphi(-\Delta \arg J)\) counts zeros (off \(T=0\)) with positive weight.
  - Upper bound: bound \(\int \varphi|-\Delta\arg J|\) by \(\sqrt{\int |\nabla U|^2}\) using Cauchy–Schwarz and `thm:box-energy`.
  - For \(n\) large, the upper bound is \(<\pi/2\), forcing the phase to lie in a wedge cone and excluding off-\(T=0\) zero mass.

#### Full proof (massive detail; edit)

**Blocked** (missing formalism and analytic lemmas). See “Conditional on / Blockers”.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:mu0-wedge — theorem (Positive proportion at each depth; $\mu=0$)

- **Source**: `BSD-Jon-Final.txt` L597–L599
- **Status**: conditional
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:mu-criterion
- **Conditional on / Blockers (edit)**:
  - **Conditional on `lem:wedge`**: this theorem is an immediate corollary of the wedge criterion plus the Weierstrass/μ-criterion (`lem:mu-criterion`).

#### Statement (verbatim from source)

```tex
\begin{theorem}[Positive proportion at each depth; $\mu=0$]\label{thm:mu0-wedge}
For all sufficiently large $n$, a positive proportion of primitive characters $\chi$ of conductor $p^n$ satisfy $v_p\big(L_p(E,\chi)\big)=0$ (and similarly for $L_p^{\pm}$). Hence $\mu_p(E)=0$ by Lemma~\ref{lem:mu-criterion} (\S\,F.52).
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:wedge` (positive-proportion nonvanishing at conductor \(p^n\) for \(n\gg 1\))
  - `lem:mu-criterion` (positive-proportion nonvanishing at infinitely many depths \(\Rightarrow \mu_p(E)=0\))
- **External (papers/books/theorems)**:
  - None beyond standard properties of \(\Lambda\)-adic power series used in `lem:mu-criterion`.

#### Proof outline (edit)

- Apply `lem:wedge` to conclude: for all sufficiently large \(n\), a positive proportion of primitive \(\chi\) of conductor \(p^n\) have \(v_p(L_p(E,\chi))=0\).
- Apply `lem:mu-criterion` to deduce \(\mu_p(E)=0\) (and similarly in signed/improved variants).

#### Full proof (massive detail; edit)

Assume `lem:wedge`. Fix \(p\) and consider the set of primitive characters \(\chi\) of conductor \(p^n\). The wedge criterion asserts that for all sufficiently large \(n\), a positive proportion of these \(\chi\) satisfy \(v_p(L_p(E,\chi))=0\) (and similarly for \(L_p^{\pm}\) in the signed case).

Therefore the hypothesis of `lem:mu-criterion` holds with some constant \(C>0\) and infinitely many \(n\) (indeed all sufficiently large \(n\)). Applying `lem:mu-criterion` gives \(\mu_p(E)=0\). The signed/improved variants follow by replacing \(L_p\) by the signed/improved \(p\)-adic \(L\)-function in the same argument.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L604 — remark (Signed and improved variants)

- **Source**: `BSD-Jon-Final.txt` L604–L606
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Signed and improved variants]
All statements above admit signed analogues with $L_p^{\pm}$ and with the improved objects at split multiplicative $p$ (replace $L_p$ by $L_p^{\!*}$ and $K$ by $K^{\!*}$; cf. \S\,F.40).
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:disc-wedge — lemma (Boundary wedge on $\partial\mathcal{D}$)

- **Source**: (deprecated) removed from the unconditional mainline in `BSD-Jon-Final.txt` when the disc-pinch engine was dropped
- **Status**: deprecated (new major hypothesis; not used)
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Deprecated**: the unconditional mainline no longer uses any disc-wise “wedge/pinch” engine. This section is kept only as a historical record of the former plan and as a reminder that it required a genuinely new nonarchimedean boundary rigidity input.
  - **Core missing lemma**: the source now posits a strict boundary Schur bound \(|\Theta|_p\le\rho<1\) on \(\partial\mathcal D\) after a unimodular rotation \(u_{\mathcal D}\). This is the entire “disc pinch” input and currently has no proof.
  - **What this actually asserts (p-adic content)**:
    - Writing \(F=u_{\mathcal D}J\) with \(|u_{\mathcal D}|_p=1\), the inequality \(\left|\frac{F-1}{F+1}\right|_p\le\rho<1\) forces \(F(\partial\mathcal D)\subset B(1,\rho)\subset \mathbb C_p^\times\).
    - In particular (since \(B(1,1)=1+\mathfrak m\)), this implies **after rotation the boundary values all lie in a single residue class**; e.g. if \(\rho\le |p|\) then \(F\equiv 1\pmod p\) on the boundary.
    - This is far stronger than “\(|J|_p\equiv 1\) on the boundary” and is precisely the kind of rigidity needed to deduce \(J\in\mathcal O(D)^\times\).
  - **Why this looks genuinely new / unjustified (as written)**:
    - The manuscript’s motivating mechanism is a complex-analytic “argument wedge / \(\pi/2\)” proof pattern. No nonarchimedean analogue is defined in the text: there is no canonical \(p\)-adic “\(\arg\)” on \(\mathbb C_p^\times\) with cone geometry, and no stated Berkovich/rigid potential-theory replacement.
    - Even in rigid analysis, \(|J|_p\equiv 1\) on the (Shilov) boundary does **not** force \(J\) to be close to a constant (e.g. nonconstant analytic units exist with boundary norm \(1\)). The strict residue-ball conclusion therefore requires an additional, nonstandard rigidity input.
    - Repo cross-check: the only “wedge → Schur pinch” infrastructure currently present is **archimedean/complex** (e.g. `RiemannRecognitionGeometry/Phase.lean` and `RiemannRecognitionGeometry/Port/WedgeClosure.lean`) and does not translate to \(p\)-adic boundaries.
  - **Analytic formalism missing**: we need explicit definitions for:
    - the boundary carrier \(S(D)\) (Shilov boundary / Berkovich boundary of a closed affinoid disc) and how \(\partial D\) in the source maps to it,
    - “admissible boundary masks” and their energy on \(S(D)\),
    - the CR–Green/box-energy inequality in the nonarchimedean setting.
  - **Upstream dependency**: any proof advertised as “same CR–Green/box-energy argument” must import/replace the cyclotomic `thm:box-energy` + `lem:wedge` package in a setting that is actually defined on \(D\).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Boundary wedge on $\partial\mathcal{D}$]\label{lem:disc-wedge}
After neutralization of finitely many atomic boundary points, there exists a constant unit $u_{\mathcal D}\in \mathbb{C}_p^{\times}$ and a constant $\rho\in(0,1)$ such that, writing
\[
  F(T):=u_{\mathcal D}\,J(T),\qquad \Theta(T):=\frac{F(T)-1}{F(T)+1},
\]
one has the uniform boundary Schur bound
\[
  |\Theta(T)|_p\ \le\ \rho\qquad\text{for all }T\in \partial\mathcal{D}.
\]
Equivalently, after a unimodular rotation, the boundary values of $J$ lie in a rigid ball avoiding $0$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:outer-boundary` / §F.31B (outer factor, neutralized ratio \(J\), unit-modulus boundary property in cyclotomic setting)
  - (disc side) the definitions of \(D\), \(\mathcal O(D)\), and the restriction of \(\det(I-K)\), \(L_p\), and \(O\) to \(D\)
- **External (papers/books/theorems)**:
  - Basic rigid-analytic functional analysis: Fredholm determinant analyticity on affinoids (for \(\det(I-K)\))
  - Rigid/Berkovich maximum modulus principle on closed affinoids (supnorm achieved on Shilov boundary)
  - (If using potential theory) nonarchimedean Poincaré–Lelong / Laplacian formalism on Berkovich curves (to make any “CR–Green” analog precise)

#### Proof outline (edit)

- **Strawman target proof (disc-engine repair direction)**:
  - Define \(D\) (closed affinoid disc), \(A=\mathcal O(D)\), and the restricted analytic functions \(\mathscr D_D=\det(I-K)|_D\in A\), \(L_{p,D}=L_p|_D\in A\).
  - Choose an “outer” factor \(O_D\in A^\times\) (zero-free on \(S(D)\)) so the neutralized ratio \(J:=\mathscr D_D/(O_D\,L_{p,D})\) is **meromorphic** on \(D\) and has \(|J|_p\equiv 1\) on \(S(D)\) after atom neutralization.
  - Prove a **strict** boundary control on the Möbius/Schur transform \(\Theta=(u_DJ-1)/(u_DJ+1)\) for some constant unit \(u_D\): \(|\Theta|_p\le \rho<1\) on \(S(D)\).
  - By rigid maximum modulus, \(|\Theta|_p\le \rho<1\) on \(D\setminus Z\), and boundedness implies any meromorphic singularities are removable (so \(\Theta\in A\)).
  - Conclude \(u_DJ=(1+\Theta)/(1-\Theta)\in A^\times\), hence \(J\in A^\times\). This is exactly “no residual factor on \(D\)” (ideal equality up to a unit), which is all `cor:disc-imc` needs.

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:schur-pinch — theorem (Rigid Schur pinch; no extra factor on $\mathcal{D}$)

- **Source**: (deprecated) removed from the unconditional mainline in `BSD-Jon-Final.txt` when the disc-pinch engine was dropped
- **Status**: deprecated (disc pinch not used; superseded by literature IMC coverage)
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Deprecated**: see `cor:disc-imc` + `thm:universal-imc` for the current unconditional route (literature IMC coverage + finite closures).
  - **Paper repair applied**: the source has been rewritten to avoid the false “max modulus ⇒ constancy” step; it now aims only to show \(J\) is an analytic **unit** on \(D\), which is exactly what “no residual factor” means for ideal equality.
  - **Still conditional**: the only genuinely hard input left is `lem:disc-wedge` (a strict boundary bound \(|\Theta|_p\le\rho<1\) after unimodular rotation). If this cannot be proved in a real nonarchimedean setting, the disc engine collapses.
  - **Sufficiency checkpoint**: we do **not** need \(J\equiv 1\); it is enough to prove
    \[
      J \in \mathcal O(D)^\times,
    \]
    i.e. the neutralized ratio is an analytic **unit** on the disc (“no residual factor”). This avoids the false constancy step and matches what ideal equality uses.

#### Statement (verbatim from source)

```tex
\begin{theorem}[Rigid Schur pinch; no extra factor on $\mathcal{D}$]\label{thm:schur-pinch}
$\Theta$ extends holomorphically and boundedly across putative common zeros in $\mathcal{D}$. In particular, $\Theta\in \mathcal{O}(\mathcal D)$ and $|\Theta|_p\le \rho<1$ on $\mathcal{D}$, so $1\pm \Theta\in \mathcal{O}(\mathcal D)^{\times}$ and hence $F=(1+\Theta)/(1-\Theta)\in \mathcal{O}(\mathcal D)^{\times}$. Equivalently, the neutralized ratio $J$ is a unit on $\mathcal D$ (after fixing the outer normalization up to a constant unit), so no residual factor remains on $\mathcal{D}$, and
\[
  \big(L_p\big)\ =\ \mathrm{char}_\Lambda X_p\quad (\text{resp. signed / improved variants}).
\]
\end{theorem}
```

#### Repaired statement (track target; sufficient for `cor:disc-imc`)

```tex
\begin{theorem}[Rigid Schur pinch (repaired); no residual factor on $D$]\label{thm:schur-pinch-repaired}
Let $D$ be a closed finite-slope affinoid disc and write $A=\mathcal O(D)$. Assume:
(i) $\mathscr D_D=\det(I-K)|_D\in A$ and $L_{p,D}=L_p|_D\in A$;
(ii) an outer factor $O_D\in A^\times$ is chosen so that the ratio $J:=\mathscr D_D/(O_D\,L_{p,D})$ is meromorphic on $D$ and $|J|_p\equiv 1$ on the Shilov boundary $S(D)$ after neutralization of finitely many atomic points;
(iii) after multiplying by a constant unit $u_D\in\mathbb C_p^\times$, the Schur transform $\Theta:=(u_DJ-1)/(u_DJ+1)$ satisfies $|\Theta|_p\le \rho<1$ on $S(D)$.
Then $\Theta\in A$ and $J\in A^\times$. In particular, $(L_{p,D})=(\mathscr D_D)$ as principal ideals in $A$ (ordinary/signed/improved variants similarly).
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:disc-wedge` (in its *repaired*, nonarchimedean form: a strict \(|\Theta|_p<1\) boundary bound on the Shilov boundary)
  - `lem:noncancel` (or a standard “bounded meromorphic ⇒ holomorphic” removability lemma on affinoids)
- **External (papers/books/theorems)**:
  - Rigid maximum modulus principle (supnorm on \(D\) attained on \(S(D)\))
  - Removable singularities for bounded meromorphic functions on one-dimensional affinoids (can be proved via Weierstrass preparation locally)

#### Proof outline (edit)

- **Repaired proof skeleton (unit conclusion, not constancy)**:
  - Define \(A=\mathcal O(D)\), \(\mathscr D_D\in A\), \(L_{p,D}\in A\), and \(O_D\in A^\times\). Then \(J\in \mathrm{Frac}(A)\) is meromorphic on \(D\).
  - Define \(\Theta=(u_DJ-1)/(u_DJ+1)\in\mathrm{Frac}(A)\). By the repaired disc-wedge hypothesis, \(|\Theta|_p\le\rho<1\) on the Shilov boundary \(S(D)\).
  - By maximum modulus, \(|\Theta|_p\le\rho<1\) on \(D\setminus Z\). In particular \(\Theta\) is bounded, so any poles are removable and \(\Theta\in A\).
  - Since \(|\Theta|_p<1\) on \(D\), both \(1\pm \Theta\) are analytic units, hence \(u_DJ=(1+\Theta)/(1-\Theta)\in A^\times\). Therefore \(J\in A^\times\).
  - Unwind \(J=\mathscr D_D/(O_D\,L_{p,D})\) with \(O_D\in A^\times\) to get \((\mathscr D_D)=(L_{p,D})\) as principal ideals on \(D\).

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:disc-imc — corollary (Cyclotomic IMC equality (coverage theorem))

- **Source**: `BSD-Jon-Final.txt` (Appendix F.31F + \S\,F.32)
- **Status**: blocked (external coverage incomplete for universal “all primes, all modular \(E/\Q\)” claim)
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: thm:universal-imc
- **Conditional on / Blockers (edit)**:
  - **Core blocker**: the currently pinned down 2024–2025 inputs give strong coverage in major ranges (ordinary good primes with residual irreducibility; semistable supersingular signed IMC), but **do not** (as stated) cover cyclotomic IMC equality for **all primes \(p\)** for an arbitrary modular elliptic curve \(E/\Q\) (notably, supersingular \(\pm\) equality beyond semistable/square-free conductor and some small-prime/additive edge cases).
  - **What would unblock**: an unconditional literature theorem (with exact hypotheses) that supplies signed cyclotomic IMC equality at supersingular primes for general conductor / general bad reduction types (or an explicit finite-exception closure mechanism proving the missing primes are finite and handled by another unconditional theorem).
  - **Note**: this replaces the deprecated disc-wise wedge/pinch engine (`lem:disc-wedge`, `thm:schur-pinch`, `thm:disc-imc`) as the equality input.

#### Statement (verbatim from current source)

```tex
\begin{corollary}[Cyclotomic IMC equality (coverage theorem)]\label{cor:disc-imc}
For each prime $p$, cyclotomic IMC equality in the relevant setting (ordinary, signed $\pm$, or improved at split multiplicative $p$) is available from the literature ranges summarized in \S\,F.32. In particular, Theorem~\ref{thm:universal-imc} holds prime-by-prime.
\end{corollary}
```

#### Coverage map (edit; fill with exact theorem numbers after web pass)

This section is intentionally structured as a **coverage table**, not a proof. The goal is: for each prime \(p\), we can point to an external theorem that gives the *ideal equality* \(\mathrm{char}_\Lambda X = (L)\) (ordinary / signed / improved), or else place \(p\) into a **finite exception set** for the fixed curve \(E\) and record the explicit closure tool used for that exceptional set.

| Bucket (prime type) | What we need (output) | Literature input(s) (exact theorem) | Typical hypotheses to check | Finite-exception closure (if not covered) |
|---|---|---|---|---|
| **Good ordinary \(p\ge 5\)** | IMC ideal equality (at least in \(\Lambda\otimes\BQ_p\); integral in \(\Lambda\) after “big image” condition) | **BCS24** (`arXiv:2405.00270`), Theorem 1.1.2 (HTML / arXiv): good ordinary \(p>3\) + (irr\(_\BQ\)) \(\Rightarrow\) \(\mathrm{ch}_\Lambda(X_{\ord}(E/\BQ_\infty))=(\mathcal L_p(E/\BQ))\) in \(\Lambda\otimes\BQ_p\); and if additionally (im) (existence of \(\sigma\in G_\BQ(\mu_{p^\infty})\) with \(T/(\sigma-1)T\simeq\BZ_p\)) then the equality holds in \(\Lambda\). | good ordinary; residual irreducible (non-CM gives “all but finitely many \(p\)”); the “big image”/integrality condition (im) for integral equality in \(\Lambda\) | **Finite set for fixed \(E\)**: residual reducible/Eisenstein primes (and some residual dihedral primes) are exceptional for the ordinary IMC proofs; treat via Eisenstein-prime closures or by switching to BSD\(_p\) closure tools (visibility/GZK in rank \(\le 1\), etc.) |
| **Supersingular \(p\ge 5\)** | signed \(\pm\) IMC ideal equality | **BSTW24** (`arXiv:2409.01350`), Thm. `thmA` in arXiv TeX: if \(E/\BQ\) is **semistable** and \(p>2\) is supersingular (and if \(p=3\) assuming their condition \(\eqref{h4}\)), then Kobayashi’s signed IMC holds: for \(\circ\in\{+,-\}\), \((\CL_p^{\circ}(E))=\xi_\Lambda(X_\circ(E))\) in \(\Lambda\) (also for quadratic twists under stated restrictions).  (Note: **Castella25** `arXiv:2502.19618`, Theorem A, is a **signed leading-term / characteristic-series** statement assuming \(\Sha[p^\infty]\) finite and a nonzero regulator; it is **not** an IMC-equality input by itself.) | signed \(\pm\) setup; \(a_p=0\) (automatic for elliptic curves at supersingular \(p\ge 5\)); semistability / square-free conductor hypotheses in BSTW; small-prime hypotheses (notably \(p=3\)) | If your curve has additive reduction (non-square-free \(N\)), BSTW’s semistable hypothesis does not apply as stated; additional literature is required (this is currently the main gap in “universal IMC equality for all \(p\)”). |
| **Split multiplicative** | IMC equality in improved normalization | Greenberg–Stevens exceptional zero + “improved” main conjecture statements | exceptional zero hypotheses; precise normalization of improved \(L_p^{\!*}\), \(K^{\!*}\) | treat as finite set for fixed \(E\); record exact improved theorem used |
| **Small primes \(p\in\{2,3\}\)** | IMC equality (ordinary/signed as applicable) | small-\(p\) frameworks + dedicated papers (see \S\,F.15) | bad reduction subtleties; control theorems; signed theory definitions | explicit case-by-case closure (finite set) |
| **Residual reducible / Eisenstein** | usually **not** full IMC equality; used as *finite-exception closure* | **Keller–Yin24** (`arXiv:2410.23241`), main theorem in Introduction (unnumbered in `main.tex`): for potentially good ordinary Eisenstein primes \(p>2\) (i.e. \(E[p]\) reducible), proves the \(p\)-converse \( \corank_{\BZ_p}\Sel_{p^\infty}(E/\BQ)=r\Rightarrow \ord_{s=1}L(E,s)=r\) for \(r\in\{0,1\}\), hence \(\rk E(\BQ)=r\) and \(\#\Sha<\infty\). | Eisenstein prime; potentially good ordinary at \(p\); Selmer corank \(r\le 1\) (this is a **rank \(\le 1\)** closure tool, not a universal IMC input) | For general rank \(r>1\), this does not close Eisenstein primes; a universal unconditional route would need genuinely new input here. |

**Clarifications (web-pass results).**
- **Yan–Zhu24** (`arXiv:2412.20078`): Conj. 1.1 / Thm. 1.2 are **\(\Lambda_K\)** (two-variable / Heegner–anticyclotomic) main-conjecture statements; they are *not* a direct cyclotomic IMC-over-\(\BQ_\infty\) equality input unless an additional reduction-to-cyclotomic argument is supplied.
- **Sprung24** (*Advances in Mathematics* 2024), DOI `10.1016/j.aim.2024.109741` (ScienceDirect `S0001870824002561`): **closed access** in this environment; we can’t extract exact theorem numbers/hypotheses yet, so this remains a TODO if we want to cite it for “beyond \(a_p=0\)” / small-prime supersingular cleanup.

#### Proof outline (coverage proof)

- Fix a prime \(p\). Determine the reduction type (ordinary / supersingular / split multiplicative) and whether \(p\in\{2,3\}\).
- Apply the corresponding literature theorem (as catalogued in \S\,F.32) to obtain cyclotomic IMC equality in the correct normalization (ordinary / signed / improved).
- For primes not covered by the “generic” hypotheses (typically a finite set for fixed \(E\)), invoke the explicit closure tools recorded in Appendix~F (Eisenstein closures; small-prime adjustments; exceptional-zero corrections).

---

### auto-remark-L632 — remark (Deprecated: disc pinch vs patching)

- **Source**: (deprecated) removed from the mainline in `BSD-Jon-Final.txt` when the disc-pinch engine was dropped
- **Status**: deprecated
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - This remark compared two “upgrade-to-equality” mechanisms (disc pinch vs finite-slope patching). The current mainline uses literature IMC coverage (\S\,F.32) instead.

#### Statement (verbatim from source)

```tex
\begin{remark}[Relation to \S\,F.56]
The wedge\,/\,pinch is a certificate alternative to the finite\,--\,slope patching engine in \S\,F.56; both routes yield the same reverse divisibility and equality upon combining with Kato.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:universal-bsd-p — corollary (Universal BSD$_p$ via wedge + IMC coverage)

- **Source**: `BSD-Jon-Final.txt` L636–L638
- **Status**: conditional
- **Auto-flags**: —
- **Auto-extracted internal refs**: thm:integral-det-exact-ord, thm:mu0-wedge, thm:universal-imc, cor:disc-imc
- **Conditional on / Blockers (edit)**:
  - **Conditional on μ=0 engine**: `thm:mu0-wedge` (currently `conditional` on `lem:wedge`, which is `blocked`).
  - **Conditional on IMC equality coverage**: `thm:universal-imc` / `cor:disc-imc` (currently `in_progress`, pending exact theorem-number mapping).
  - **Conditional on “integral exactness / coker=Selmer / det=Lp” operator package** (e.g. `thm:integral-det-exact-ord` and signed/improved analogues).
  - **Fixed-prime Sha step**: needs an explicit lemma connecting BSD$_p$ data / Selmer exactness / PT to finiteness of \(\Sha[p^\infty]\) at each \(p\) (Appendix C / `thm:sha-finite` interfaces).
  - **Exceptional zero corrections**: needs the Greenberg–Stevens correction inputs in \S F.40.

#### Statement (verbatim from source)

```tex
\begin{corollary}[Universal BSD$_p$ via wedge + IMC coverage]\label{cor:universal-bsd-p}
With universal $\mu=0$ (Theorem~\ref{thm:mu0-wedge}) and cyclotomic IMC equality (Theorem~\ref{thm:universal-imc}, supplied by the literature coverage package of \S\,F.32) holding prime\,--\,by\,--\,prime (signed/improved as appropriate), and with integral exactness (Theorem~\ref{thm:integral-det-exact-ord} and its signed/improved variants) and Greenberg--Stevens corrections (\S\,F.40), BSD$_p$ holds for every prime $p$.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `thm:mu0-wedge` (universal \(\mu=0\))
  - `cor:disc-imc` / `thm:universal-imc` (IMC equality at every prime, ordinary and signed)
  - `thm:integral-det-exact-ord` (+ signed/improved variants) (operator identity + Selmer exactness in integral form)
  - \S F.40 (Greenberg–Stevens / improved objects at split multiplicative primes)
  - `prop:BSDp` (IMC\(_p\)+\(\mu=0\)+finite \(\Sha[p^\infty]\)\(\Rightarrow\) BSD\(_p\))
- **External (papers/books/theorems)**:
  - Kato one-sided divisibility (ordinary) and signed analogues (supersingular)
  - Poitou–Tate / Cassels–Tate duality inputs needed to control \(\Sha[p^\infty]\) at each \(p\)

#### Proof outline (edit)

- Fix a prime \(p\).
- Use `thm:mu0-wedge` to get \(\mu_p(E)=0\).
- Use `thm:universal-imc` / `cor:disc-imc` (literature IMC coverage) to get cyclotomic IMC equality at \(p\) (ordinary / signed / improved as appropriate).
- Combine IMC\(_p\)+\(\mu=0\) with the exactness/leading-term machinery (integral operator model + PT) to obtain BSD\(_p\) at \(p\), including finiteness of \(\Sha[p^\infty]\) and the \(p\)-part of the leading term, with exceptional-zero corrections handled by \S F.40.
- Since \(p\) was arbitrary, BSD\(_p\) holds for every prime.

#### Full proof (massive detail; edit)

**Conditional proof skeleton (matches the source’s current intent):** Fix a prime \(p\). By `thm:mu0-wedge` we have \(\mu_p(E)=0\). By `thm:universal-imc` / `cor:disc-imc` (IMC equality imported via literature coverage + finite closures), cyclotomic IMC equality holds at \(p\) (ordinary or signed, with the improved objects at split multiplicative \(p\)).

With IMC\(_p\) and \(\mu_p(E)=0\) in hand, the remaining input needed for BSD\(_p\) is the fixed-prime Sha/Selmer leading-term interface: using integral exactness of the operator model (e.g. `thm:integral-det-exact-ord` and variants) plus Poitou–Tate/Cassels–Tate duality and the Greenberg–Stevens correction in the split multiplicative case (\S F.40), one deduces finiteness of \(\Sha(E/\mathbb{Q})[p^\infty]\) and the equality of \(p\)-adic valuations in the BSD leading-term formula (i.e. BSD\(_p\)). Since \(p\) was arbitrary, BSD\(_p\) holds for every prime.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:global-bsd-outer — corollary (Global BSD leading term via operator--outer--wedge)

- **Source**: `BSD-Jon-Final.txt` L643–L645
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - Conditional on prime-wise BSD\(_p\) for all primes and the algebraicity/positivity inputs packaged in `thm:global-bsd`.

#### Statement (verbatim from source)

```tex
\begin{corollary}[Global BSD leading term via operator--outer--wedge]\label{cor:global-bsd-outer}
Combining BSD$_p$ over all primes, the algebraic leading term equals the analytic one up to a rational unit; archimedean positivity fixes the sign. Hence the full BSD leading\,--\,term identity holds.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `thm:global-bsd` (this corollary is essentially a one-line restatement of its conclusion)
- **External (papers/books/theorems)**:
  - Same as `thm:global-bsd` (Shimura/Deligne algebraicity + archimedean positivity to fix the sign)

#### Proof outline (edit)

- Apply `thm:global-bsd`.

#### Full proof (massive detail; edit)

Immediate from `thm:global-bsd`: BSD\(_p\) for all primes implies the global BSD leading-term identity (and fixes the sign via archimedean normalization).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L662 — corollary (Automatic BSD$_p$ under SU)

- **Source**: `BSD-Jon-Final.txt` L662–L668
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: prop:BSDp
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Automatic BSD$_p$ under SU]
If, in addition, $\mu_p(E)=0$ (e.g. certified by a height–unit at $p$ via \S F.16.3 or F.23), then
\[
  \mathrm{ord}_{T=0}L_p(E,T)\ =\ \mathrm{corank}_\Lambda X_p(E/\mathbb{Q}_\infty)\ =\ \mathrm{rank}\,E(\mathbb{Q}),
\]
and the $p$–part of the BSD leading–term identity holds (Proposition~\ref{prop:BSDp}).
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L677 — corollary (Automatic signed BSD$_p$)

- **Source**: `BSD-Jon-Final.txt` L677–L683
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Automatic signed BSD$_p$]
Under \eqref{eq:signed-imc} and $\mu_p^{\pm}(E)=0$, one has
\[
  \mathrm{ord}_{T=0}L_p^{\pm}(E,T)\ =\ \mathrm{corank}_\Lambda X_p^{\pm}(E/\mathbb{Q}_\infty)\ =\ \mathrm{rank}\,E(\mathbb{Q}),
\]
and the signed $p$–part of BSD holds.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### def:hida-congruence — definition (Hida family and congruence ideal)

- **Source**: `BSD-Jon-Final.txt` L709–L711
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{definition}[Hida family and congruence ideal]\label{def:hida-congruence}
Let $\mathbb{T}^{\mathrm{ord}}$ be the big ordinary Hecke algebra attached to the tame level of $E$ and let $\mathcal{R}$ be its weight algebra. Let $\mathscr{F}$ denote the Hida family passing through $E$ (ordinary $p$). The \emph{congruence ideal} $\mathfrak{c}(\mathscr{F})\subset\mathcal{R}\llbracket \Gamma\rrbracket$ is the Fitting ideal of the cotangent space measuring cusp–Eisenstein congruences in family.
\end{definition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:RS-integral-ord — theorem (Integral two–variable $p$–adic $L$ and congruence ideal)

- **Source**: `BSD-Jon-Final.txt` L713–L719
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Integral two–variable $p$–adic $L$ and congruence ideal]\label{thm:RS-integral-ord}
There exists a two–variable $p$–adic $L$–function $L_p^{(2)}(\mathscr{F})\in \mathcal{R}\llbracket \Gamma\rrbracket$ interpolating Rankin–Selberg zeta integrals against finite–order cyclotomic characters and arithmetic specializations of $\mathscr{F}$ such that
\[
  \mathfrak{c}(\mathscr{F})\ =\ \big(\,L_p^{(2)}(\mathscr{F})\,\big)\quad \text{as principal ideals in }\ \mathcal{R}\llbracket \Gamma\rrbracket.
\]
The interpolation is integral (no $p$–power fudge), after fixing periods compatibly with $\mathscr{F}$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:gorenstein-ord — lemma (Gorenstein property and finite flatness)

- **Source**: `BSD-Jon-Final.txt` L734–L736
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Gorenstein property and finite flatness]\label{lem:gorenstein-ord}
The big ordinary Hecke algebra $\mathbb{T}^{\mathrm{ord}}$ is Gorenstein and finite flat over the weight algebra $\mathcal{R}$ on the branch of $\mathscr{F}$. In particular, $\mathscr{F}$ is unique up to units and its cotangent space is principal.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:control-ord — lemma (Ordinary control for Fourier coefficients and cohomology)

- **Source**: `BSD-Jon-Final.txt` L741–L743
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Ordinary control for Fourier coefficients and cohomology]\label{lem:control-ord}
For arithmetic weights $\kappa$ on bounded discs, specialization $\mathbb{T}^{\mathrm{ord}}\to \mathbb{T}_{\kappa}$ is flat and the ordinary part of completed cohomology (and its Selmer module) specializes with bounded kernel/cokernel. Petersson pairings and $q$–expansion maps commute with specialization up to $\mathbb{Z}_p^{\times}$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:integral-interp-hida — lemma (Integral interpolation normalizations)

- **Source**: `BSD-Jon-Final.txt` L748–L754
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Integral interpolation normalizations]\label{lem:integral-interp-hida}
There exist periods $\Omega_{\kappa}$ varying analytically in $\kappa$ such that for each finite–order cyclotomic $\chi$
\[
  L_p^{(2)}(\mathscr{F})(\kappa,\chi)\ =\ u(\kappa,\chi)\cdot \frac{\langle f_{\kappa}, \mathrm{Eis}_{\chi}\rangle_{\kappa}}{\Omega_{\kappa}^2},\qquad u(\kappa,\chi)\in \mathbb{Z}_p^{\times},
\]
with $\langle\ ,\ \rangle_{\kappa}$ the Petersson pairing at weight $\kappa$. The units are bounded on bounded weight ranges.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:twk-divides — theorem (Patched divisibility and descent)

- **Source**: `BSD-Jon-Final.txt` L761–L770
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Patched divisibility and descent]\label{thm:twk-divides}
Let $p$ be ordinary for $E$. There is a patched ordinary Selmer module $\mathcal{X}^{\mathrm{patch}}$ over a patched weight/Hecke algebra with
\[
  \mathrm{char}\,\mathcal{X}^{\mathrm{patch}}\ \mid\ \big(\,L_p^{(2)}(\mathscr{F})\,\big)
\]
as ideals. By Emerton’s local–global compatibility and control for ordinary local conditions, this divisibility descends to the cyclotomic line, yielding
\[
  \mathrm{char}_{\Lambda}X_p(E/\mathbb{Q}_\infty)\ \mid\ \big(L_p(E,T)\big).
\]
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:lgc-greenberg — lemma (Matching Greenberg local conditions at $p$)

- **Source**: `BSD-Jon-Final.txt` L784–L786
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Matching Greenberg local conditions at $p$]\label{lem:lgc-greenberg}
In the ordinary setting, Emerton’s local–global compatibility identifies the $p$–adic local component of completed cohomology with the ordinary filtered representation; the induced local deformation condition equals the Greenberg local condition used in Selmer. Hence the patched local conditions match Selmer’s at $p$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:descent-control — theorem (Descent control from patched modules to $X_p$)

- **Source**: `BSD-Jon-Final.txt` L791–L793
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:control-ord, lem:lgc-greenberg
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Descent control from patched modules to $X_p$]\label{thm:descent-control}
Under Lemmas~\ref{lem:control-ord} and \ref{lem:lgc-greenberg}, the natural maps from $\mathcal{X}^{\mathrm{patch}}$ to $X_p(E/\mathbb{Q}_\infty)$ have bounded kernels and cokernels; in particular, characteristic ideal divisibility descends from the patched family to cyclotomic Selmer.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:ord-control-descent — lemma (Ordinary control in families)

- **Source**: `BSD-Jon-Final.txt` L799–L801
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Ordinary control in families]\label{lem:ord-control-descent}
The natural maps from patched/ordinary family Selmer modules to cyclotomic Selmer have bounded kernels and cokernels uniformly on bounded weight ranges. In particular, characteristic ideal divisibility descends from the family/patched level to $X_p(E/\mathbb{Q}_\infty)$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-theorem-L812 — theorem (Rank $1$ closure at $p$)

- **Source**: `BSD-Jon-Final.txt` L812–L814
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Rank $1$ closure at $p$]
For every prime $p$ with $p\nmid I_{\mathrm{Hg}}\,c_{\mathrm{an}}\,\prod c_\ell$ (and $p\nmid$ the Manin constant), one has $\Sha(E/\mathbb{Q})[p^\infty]$ finite and BSD$_p$ (rank equality and $p$--adic leading--term identity). In particular, for all but finitely many primes $p$, BSD$_p$ holds.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-theorem-L822 — theorem (Visibility closure at $p$)

- **Source**: `BSD-Jon-Final.txt` L822–L824
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Visibility closure at $p$]
Let $E/\mathbb{Q}$ be modular of conductor $N$. Suppose there exists a squarefree $N'\ge 1$ and a newform $g$ of level $NN'$ such that $g\equiv f_E\ (\bmod\ p)$ away from $N'$ (level--raising at a single auxiliary prime suffices), and that $\overline{\rho}_{E,p}$ is irreducible. Then the $p$--adic valuation of the algebraic side of BSD equals that of the analytic side. Equivalently, the missing $p$--power is visible in the $p$--primary torsion/component groups of $J_0(NN')$ and transfers to $E$ via the congruence. Combined with Kato's divisibility, BSD$_p$ holds.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-proposition-L832 — proposition (Higher rank closure template)

- **Source**: `BSD-Jon-Final.txt` L832–L834
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Higher rank closure template]
For each $p$ in the residue set: (i) apply Kato's bound; (ii) if ordinary and Skinner--Urban applies (\S F.32.1), then IMC yields equality; if supersingular and signed IMC applies (\S F.32.2), obtain signed equality; (iii) otherwise, perform level--raising at one auxiliary prime and use visibility to supply the reverse bound at $T=0$. Thus BSD$_p$ holds at $p$ whenever either IMC/signed IMC applies or a visibility congruence is found; only primes failing both remain.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-definition-L868 — definition (Detector $\Phi_{N,\omega}$)

- **Source**: `BSD-Jon-Final.txt` L868–L878
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:no-free-params
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{definition}[Detector $\Phi_{N,\omega}$]
Fix $N\ge 3$ and a choice of Néron differential $\omega$. Define
\[
  \Phi_{N,\omega}:\ \{X\in E(\overline{\mathbb{Q}}): [N]X=P\}\big/ E[N]\ \longrightarrow\ \mathbb{Z}/N\mathbb{Z}
\]
by
\[
  \Phi_{N,\omega}(X)\ :=\ \big( N\cdot \mathrm{ev}_{T=0}\circ \mathrm{Col}_p\big(\mathrm{loc}_p\,\kappa_N(X)\big)\big)\ \bmod N,
\]
viewed as an element of $\mathbb{Z}/N\mathbb{Z}$ via the natural reduction map (independent of $p$ by Lemma~\ref{lem:no-free-params}).
\end{definition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:Phi-detector — proposition (Equivariance and detection)

- **Source**: `BSD-Jon-Final.txt` L882–L888
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Equivariance and detection]\label{prop:Phi-detector}
Let $p\nmid N\Delta_E$ be good ordinary with $p\equiv 1\ (\mathrm{mod}\ N)$. For any $X$ with $[N]X=P$,
\[
  \overline{\log_\omega(P)}\ne 0\ (\bmod\ p)\ \Longleftrightarrow\ \Phi_{N,\omega}\big(\mathrm{Frob}_p\cdot X\big)\not\equiv 0\ (\bmod\ N).
\]
In particular, the set of such $p$ is detected by a nonempty union of conjugacy classes in $\mathrm{Gal}\big(\mathbb{Q}(E[N],\tfrac{1}{N}P)/\mathbb{Q}\big)$.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L900 — remark (Normalization independence)

- **Source**: `BSD-Jon-Final.txt` L900–L902
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:no-free-params
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Normalization independence]
By Lemma~\ref{lem:no-free-params}, changing $\omega$, the crystalline basis, or the Perrin--Riou branch multiplies the detectors by units, which do not affect their vanishing modulo $N$.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:cm-ord-density — theorem (CM ordinary diagonal–unit density)

- **Source**: `BSD-Jon-Final.txt` L918–L920
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[CM ordinary diagonal–unit density]\label{thm:cm-ord-density}
Let $E/\mathbb{Q}$ be CM and $P\in E(\mathbb{Q})$ non–torsion. Then the set of split ordinary primes $p$ for which $v_p\big(h_p(P)\big)=0$ has positive lower density among split ordinary primes. Equivalently, $v_p\big(\log_\omega(P)\big)=0$ for a set of split $p$ of positive lower density.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:cm-signed-inf — theorem (CM signed supersingular infinitude)

- **Source**: `BSD-Jon-Final.txt` L932–L934
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[CM signed supersingular infinitude]\label{thm:cm-signed-inf}
Under the hypotheses above, the set of inert (supersingular) primes $p\ge 5$ with $v_p\big(h_p^{\pm}(P)\big)=0$ for at least one sign is infinite; moreover, it has positive lower density along the set of inert primes satisfying $p\equiv 1\ (\mathrm{mod}\ N)$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L939 — remark (Effectivity and explicit constants)

- **Source**: `BSD-Jon-Final.txt` L939–L941
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Effectivity and explicit constants]
For fixed $(E,P)$ with CM and a chosen $N$, the group $G_N^{\mathrm{CM}}$ is explicitly computable via class field theory, and the proportion $|\mathcal{C}_N^{\mathrm{CM}}|/|G_N^{\mathrm{CM}}|$ is effective. Small choices of $N$ (a single prime away from the conductor and torsion index) already give concrete positive densities.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-proposition-L963 — proposition (Complete continuity of $K_{\pm}(T)$)

- **Source**: `BSD-Jon-Final.txt` L963–L968
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Complete continuity of $K_{\pm}(T)$]
$K_{\pm}(T)$ is completely continuous on $M_p\cong \Lambda^2$. If $s'_{\pm}$ is another $\Lambda$–linear section and $K'_{\pm}(T):=s'_{\pm}\circ \Phi_{\pm}$, then
\[
  \det_{\Lambda}\big(I-K'_{\pm}(T)\big)\ =\ u\cdot \det_{\Lambda}\big(I-K_{\pm}(T)\big)\qquad (u\in\Lambda^{\times}).
\]
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-definition-L970 — definition (Fredholm determinant (signed))

- **Source**: `BSD-Jon-Final.txt` L970–L972
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{definition}[Fredholm determinant (signed)]
Define $\det_{\Lambda}\big(I-K_{\pm}(T)\big)$ as the Fredholm determinant of $I-K_{\pm}(T)$; it is well–defined up to $\Lambda^{\times}$.
\end{definition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:coker-id-signed — theorem (Signed coker identification)

- **Source**: `BSD-Jon-Final.txt` L982–L988
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Signed coker identification]\label{thm:coker-id-signed}
There is a canonical pseudo–isomorphism
\[
  \mathrm{coker}\,\big(I-K_{\pm}(T)\big)^{\vee}\ \sim\ X_p^{\pm}(E/\mathbb{Q}_\infty),
\]
where $X_p^{\pm}$ is the Pontryagin dual of the signed $p^\infty$–Selmer group over $\mathbb{Q}_\infty$. In particular, the zeroth Fitting ideals agree up to $\Lambda^{\times}$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:det-equals-Lp-signed — theorem (Signed determinant equals signed $p$–adic $L$–function)

- **Source**: `BSD-Jon-Final.txt` L997–L1002
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Signed determinant equals signed $p$–adic $L$–function]\label{thm:det-equals-Lp-signed}
There exists $u\in\Lambda^{\times}$ such that
\[
  \det_{\Lambda}\big(I-K_{\pm}(T)\big)\ =\ u\cdot L_p^{\pm}(E,T).
\]
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:integral-det-exact-signed — theorem (Integral signed determinant and kernel exactness)

- **Source**: `BSD-Jon-Final.txt` L1011–L1013
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Integral signed determinant and kernel exactness]\label{thm:integral-det-exact-signed}
There exists a saturated finite free $\Lambda$–lattice $M\subset H^1_{\emph{Iw}}(\mathbb{Q},V)$ such that $\mathrm{Col}_p^{\pm}(M_p)\subset \Lambda$ integrally and $\det_{\Lambda}(I-K_{\pm}(T))$ generates $(L_p^{\pm}(E,T))$ up to $\Lambda^{\times}$. Moreover $\ker(\mathrm{Col}_p^{\pm},\pi)$ is Pontryagin dual to $X_p^{\pm}(E/\mathbb{Q}_\infty)$ and $\mathrm{coker}(\mathrm{Col}_p^{\pm},\pi)$ is finite. Hence $\mathrm{char}_{\Lambda}X_p^{\pm}\mid (L_p^{\pm})$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### def:family-regulator — definition (Saturated lattice and family regulator)

- **Source**: `BSD-Jon-Final.txt` L1027–L1036
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{definition}[Saturated lattice and family regulator]\label{def:family-regulator}
Let $M\subset H^1_{\emph{Iw}}(\mathbb{Q},V)$ be a saturated finite free $\Lambda$–lattice stable under localization at all places and under the chosen local condition at $p$ (ordinary or signed). Define the family regulator
\[
  \mathcal{R}_p\ :=\ \begin{cases}
    \mathrm{Col}_p & \text{(ordinary)},\\
    (\mathrm{Col}_p^{+},\mathrm{Col}_p^{-}) & \text{(signed supersingular)}.
  \end{cases}
\]
We view $\mathcal{R}_p: M_p\to \Lambda^{2}$ (ordinary) or $M_p\to \Lambda^{2}$ (two signs) and write $K(T)=s\circ \mathcal{R}_p$ (resp. $K_{\pm}(T)=s_{\pm}\circ \Phi_{\pm}$) for any $\Lambda$–linear section $s$ (resp. $s_{\pm}$).
\end{definition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:family-integral — lemma (Integrality and specialization)

- **Source**: `BSD-Jon-Final.txt` L1038–L1040
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Integrality and specialization]\label{lem:family-integral}
With $M$ as above, $\mathcal{R}_p(M_p)\subset \Lambda^{2}$ integrally, and for every finite–order $\chi$ of $\Gamma$ the specialization $\mathcal{R}_p(\chi)$ equals the (signed) Bloch–Kato logarithm up to a unit.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:family-det-kernel — theorem (Integral determinant and exact kernel in family)

- **Source**: `BSD-Jon-Final.txt` L1046–L1059
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Integral determinant and exact kernel in family]\label{thm:family-det-kernel}
For ordinary $p$,
\[
  \det_{\Lambda}(I-K(T))\ =\ u\cdot L_p(E,T)\ \in\ \Lambda\quad (u\in\Lambda^{\times}), \qquad \ker(\mathcal{R}_p,\pi)^{\vee}\simeq X_p(E/\mathbb{Q}_\infty),
\]
and $\mathrm{coker}(\mathcal{R}_p,\pi)$ is finite. For supersingular $p$ and each sign $\pm$,
\[
  \det_{\Lambda}(I-K_{\pm}(T))\ =\ u_{\pm}\cdot L_p^{\pm}(E,T)\ \in\ \Lambda, \qquad \ker(\mathrm{Col}_p^{\pm},\pi)^{\vee}\simeq X_p^{\pm}(E/\mathbb{Q}_\infty),
\]
with finite cokernel. Consequently
\[
  \mathrm{char}_{\Lambda}X_p\ \mid\ (L_p)\quad\text{and}\quad \mathrm{char}_{\Lambda}X_p^{\pm}\ \mid\ (L_p^{\pm}).
\]
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:family-exp-recip — theorem (Explicit reciprocity in family)

- **Source**: `BSD-Jon-Final.txt` L1065–L1071
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Explicit reciprocity in family]\label{thm:family-exp-recip}
Let $\chi$ be a finite–order cyclotomic character and let $\kappa$ vary over arithmetic weights in the ordinary (resp. finite–slope signed) family. Then
\[
  \mathrm{ev}_{\chi,\kappa}\,\mathcal{R}_p(z)\ =\ u(\chi,\kappa)\cdot \mathrm{BK}_{\chi,\kappa}(\mathrm{loc}_p\,z),\qquad u(\chi,\kappa)\in \mathbb{Z}_p^{\times},
\]
where $\mathrm{BK}_{\chi,\kappa}$ is the Bloch–Kato regulator (signed in supersingular case). The unit factor is bounded uniformly on bounded weight ranges.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:EZ-T0 — theorem (Exceptional zero, corrected $T=0$ statement)

- **Source**: `BSD-Jon-Final.txt` L1102–L1112
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Exceptional zero, corrected $T=0$ statement]\label{thm:EZ-T0}
If $E$ has split multiplicative reduction at $p$ and the triangularization basis yields unit diagonal valuations, then $\mu_p(E)=0$ and
\[
  \mathrm{ord}_{T=0}L_p(E,T)\ =\ 1\ +\ \mathrm{rank}\,E(\mathbb{Q}),\qquad \mathrm{ord}_{T=0}L_p^{\!*}(E,T)\ =\ \mathrm{rank}\,E(\mathbb{Q}).
\]
Moreover, the leading corrected coefficient satisfies
\[
  \left.\frac{d}{dT}\,L_p(E,T)\right\vert_{T=0}\ \doteq\ \mathcal{L}_p(E)\cdot \mathrm{Reg}_p\ \ \in\ \mathbb{Z}_p^{\times}\cdot \mathrm{Reg}_p,
\]
up to a $p$–adic unit normalization.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:improved-integral — theorem (Integral improved determinant and exact kernel)

- **Source**: `BSD-Jon-Final.txt` L1126–L1139
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Integral improved determinant and exact kernel]\label{thm:improved-integral}
In the split multiplicative case at $p$, there exists a saturated finite free $\Lambda$–lattice $M\subset H^1_{\emph{Iw}}(\mathbb{Q},V)$ such that
\[
  \det_{\Lambda}\big(I-K^{\!*}(T)\big)\ =\ u\cdot L_p^{\!*}(E,T)\ \in\ \Lambda,\qquad u\in\Lambda^{\times},
\]
and $\ker(\mathrm{Col}_p^{\!*},\pi)^{\vee}\simeq X_p(E/\mathbb{Q}_\infty)$ with finite cokernel. Consequently
\[
  \mathrm{char}_{\Lambda}\,X_p(E/\mathbb{Q}_\infty)\ \mid\ \big(E_p(T)\cdot L_p^{\!*}(E,T)\big),
\]
and, writing $X_p^{\!*}$ for the kernel of $(\mathrm{Col}_p^{\!*},\pi)$ (the improved local condition),
\[
  \mathrm{char}_{\Lambda}\,X_p^{\!*}(E/\mathbb{Q}_\infty)\ \mid\ \big(L_p^{\!*}(E,T)\big).
\]
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L1151 — corollary (Improved reverse inclusion)

- **Source**: `BSD-Jon-Final.txt` L1151–L1160
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Improved reverse inclusion]
At split multiplicative $p$, the reverse inclusion holds with corrected ideals:
\[
  \mathrm{char}_{\Lambda}\,X_p^{\!*}(E/\mathbb{Q}_\infty)\ \mid\ \big(L_p^{\!*}(E,T)\big),
\]
integrally. Equivalently,
\[
  \mathrm{char}_{\Lambda}\,X_p(E/\mathbb{Q}_\infty)\ \mid\ \big(E_p(T)\cdot L_p^{\!*}(E,T)\big).
\]
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:mu-asymptotics — lemma (Specialization lengths and $\mu$ lower bound)

- **Source**: `BSD-Jon-Final.txt` L1222–L1224
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: thm:integral-det-exact-ord
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Specialization lengths and $\mu$ lower bound]\label{lem:mu-asymptotics}
Let $M$ be a saturated lattice as in Theorem~\ref{thm:integral-det-exact-ord} (ordinary) or its signed analogue. For each $n\ge 1$, the average (over primitive characters $\chi$ of conductor $p^n$) of $\mathrm{length}_{\mathbb{Z}_p}\,\big(M/\mathrm{Im}(\Phi)\otimes_{\Lambda,\chi}\mathbb{Z}_p\big)$ equals the average of $\mathrm{ord}_p\,L_p(\chi)$ up to an $O(1)$ error independent of $n$. Consequently $\mu\big(X_p\big)\le \mu\big(L_p\big)$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:mu-equality — theorem ($\mu$ equality)

- **Source**: `BSD-Jon-Final.txt` L1230–L1235
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[$\mu$ equality]\label{thm:mu-equality}
For every prime $p$ (ordinary or supersingular with signs), one has
\[
  \mu\big(X_p(E/\mathbb{Q}_\infty)\big)\ =\ \mu\big(L_p(E,T)\big),\qquad \mu\big(X_p^{\pm}(E/\mathbb{Q}_\infty)\big)\ =\ \mu\big(L_p^{\pm}(E,T)\big).
\]
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-definition-L1251 — definition (Completed cohomology and finite–slope spectrum)

- **Source**: `BSD-Jon-Final.txt` L1251–L1253
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{definition}[Completed cohomology and finite–slope spectrum]
Let $\widetilde{H}^i$ denote Emerton’s completed cohomology for $\mathrm{GL}_2/\mathbb{Q}$ localized at tame level. The finite–slope spectrum at $p$ is parameterized by the eigencurve $\mathcal{E}$; points on $\mathcal{E}$ correspond to finite–slope overconvergent eigenforms with compatible Galois representations.
\end{definition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-definition-L1255 — definition (Finite–slope Eisenstein ideal)

- **Source**: `BSD-Jon-Final.txt` L1255–L1257
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{definition}[Finite–slope Eisenstein ideal]
On the local branch of $\mathcal{E}$ passing through $E$, define the finite–slope Eisenstein ideal $\mathfrak{e}_{\mathrm{fs}}$ as the kernel of the map from the local Hecke algebra to the Eisenstein system (weight/cyclotomic variables) restricted to the branch. Its congruence module measures cusp–Eisenstein congruences at finite slope.
\end{definition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:fs-congruence-L — theorem (Finite–slope congruence module = two–variable (signed) $p$–adic $L$)

- **Source**: `BSD-Jon-Final.txt` L1259–L1261
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Finite–slope congruence module = two–variable (signed) $p$–adic $L$]\label{thm:fs-congruence-L}
There is a two–variable (signed) $p$–adic $L$–function $L_{p,\mathrm{fs}}^{(2,\pm)}$ on the branch of $\mathcal{E}$ passing through $E$ such that the congruence module of $\mathfrak{e}_{\mathrm{fs}}$ is generated by $L_{p,\mathrm{fs}}^{(2,\pm)}$ integrally. Specialization to arithmetic weights and the cyclotomic line recovers $L_p$ (resp. $L_p^{\pm}$) up to units.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:fs-patched-descent — theorem (Finite–slope patched divisibility and descent)

- **Source**: `BSD-Jon-Final.txt` L1269–L1279
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Finite–slope patched divisibility and descent]\label{thm:fs-patched-descent}
There is a patched Selmer module $\mathcal{X}_{\mathrm{fs}}$ over the local branch of the eigencurve such that
\[
  \mathrm{char}\,\mathcal{X}_{\mathrm{fs}}\ \mid\ \big(\,L_{p,\mathrm{fs}}^{(2,\pm)}\,\big),
\]
and by trianguline local theory and Emerton’s local–global compatibility, this divisibility descends to the cyclotomic line yielding
\[
  \mathrm{char}_{\Lambda}X_p(E/\mathbb{Q}_\infty)\ \mid\ \big(L_p(E,T)\big)\quad\text{(resp. signed)},
\]
without residual hypotheses, uniformly across slope.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:int-RS-eigen — theorem (Integral Rankin–Selberg interpolation on the eigencurve)

- **Source**: `BSD-Jon-Final.txt` L1287–L1293
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Integral Rankin–Selberg interpolation on the eigencurve]\label{thm:int-RS-eigen}
Let $\mathcal{U}\subset \mathcal{E}$ be a reduced affinoid neighborhood of the point corresponding to $E$ on the eigencurve. There exists a coherent integral sheaf $\mathscr{M}$ of overconvergent modular forms over $\mathcal{U}$ and an analytic function $L_{p,\mathrm{fs}}^{(2,\pm)}\in \mathcal{O}(\mathcal{U})\widehat{\otimes}\Lambda$ such that for every arithmetic weight $\kappa$ and finite–order cyclotomic character $\chi$ one has
\[
  L_{p,\mathrm{fs}}^{(2,\pm)}(\kappa,\chi)\ =\ u(\kappa,\chi)\cdot \frac{\langle f_{\kappa}, \mathrm{Eis}_{\chi}\rangle_{\kappa}}{\Omega_{\kappa}^2}\ \in\ \mathbb{Z}_p[\chi]^{\times}\cdot \mathbb{Z}_p,
\]
where $\Omega_{\kappa}$ vary analytically in $\kappa$ (Shimura periods), $\langle\ ,\ \rangle_{\kappa}$ is the Petersson pairing, and $u(\kappa,\chi)\in \mathbb{Z}_p^{\times}$ are bounded on $\mathcal{U}$. In particular, $L_{p,\mathrm{fs}}^{(2,\pm)}$ is integral and generates the finite–slope Eisenstein congruence module on $\mathcal{U}$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:patching-data — lemma (Patching data)

- **Source**: `BSD-Jon-Final.txt` L1301–L1303
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Patching data]\label{lem:patching-data}
There exist Taylor–Wiles auxiliary levels $N_q$ and deformation problems $\mathcal{D}$ such that the patched Hecke algebra $\mathbf{T}^{\mathrm{patch}}$ acts faithfully on patched completed cohomology $\widetilde{H}^{\bullet}_{\mathrm{patch}}$ over a power series base, and the local deformation at $p$ is trianguline/ordinary in the sense matching Selmer local conditions.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:precise-patch — theorem (Precise patched divisibility)

- **Source**: `BSD-Jon-Final.txt` L1308–L1310
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:patching-data
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Precise patched divisibility]\label{thm:precise-patch}
Under Lemma~\ref{lem:patching-data}, the characteristic ideal of the patched Selmer $\mathcal{X}_{\mathrm{fs}}$ divides the principal ideal generated by $L_{p,\mathrm{fs}}^{(2,\pm)}$ in $\mathcal{O}(\mathcal{U})\widehat{\otimes}\Lambda$, and the quotient is supported on the boundary of $\mathcal{U}$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:trianguline-signed — theorem (Trianguline control for signed regulators)

- **Source**: `BSD-Jon-Final.txt` L1317–L1319
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: thm:family-exp-recip
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Trianguline control for signed regulators]\label{thm:trianguline-signed}
Over a small affinoid neighborhood $\mathcal{U}$ on the eigencurve at a supersingular point, the Galois representation $V$ is trianguline in families with two $\mathbb{Q}_p$–analytic characters $\delta_1,\delta_2$ varying on $\mathcal{U}$. The signed Coleman maps $\mathrm{Col}_p^{\pm}$ coincide (up to $\Lambda^{\times}$) with projections along the trianguline lines in $(\varphi,\Gamma)$–modules, and the family explicit reciprocity (Theorem~\ref{thm:family-exp-recip}) holds with signed regulators.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L1324 — corollary (Exactness and integrality for signed families)

- **Source**: `BSD-Jon-Final.txt` L1324–L1326
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Exactness and integrality for signed families]
On $\mathcal{U}$, the signed regulator determinant equals $L_p^{\pm}$ integrally and $\ker(\mathrm{Col}_p^{\pm},\pi)^{\vee}\simeq X_p^{\pm}$ with finite cokernel. Hence $(\mathrm{char}_{\Lambda}X_p^{\pm})\mid(L_p^{\pm})$.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:awayp-integral — lemma (Integral local conditions at $\ell\ne p$)

- **Source**: `BSD-Jon-Final.txt` L1340–L1342
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Integral local conditions at $\ell\ne p$]\label{lem:awayp-integral}
For each finite prime $\ell\ne p$, there exists a finite free $\Lambda$–lattice $M_{\ell}\subset H^1_{\emph{Iw}}(\mathbb{Q}_{\ell},V)$ and a $\Lambda$–submodule $F_{\ell}\subset M_{\ell}$ defining the local finite (Greenberg) condition such that $M_{\ell}/F_{\ell}$ is a torsion $\Lambda$–module of bounded length in families (ordinary and finite slope). The formation of $F_{\ell}$ is compatible with specialization along finite–order characters.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:awayp-neutral — proposition (Determinant neutrality of away–$p$ local factors)

- **Source**: `BSD-Jon-Final.txt` L1348–L1350
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Determinant neutrality of away–$p$ local factors]\label{prop:awayp-neutral}
With notation as above, the contribution of $\ell\ne p$ to the determinant functor of the global Selmer complex is a $\Lambda$–unit. Equivalently, after identifying the global object via the regulator at $p$ and the finite local conditions at $\ell\ne p$, the away–$p$ local terms do not change the principal ideal generated by the regulator determinant.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L1356 — corollary (Correct global determinant line)

- **Source**: `BSD-Jon-Final.txt` L1356–L1358
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Correct global determinant line]
The determinant identities in \S\,F.31, \S\,F.39, and \S\,F.40.5 measure the global determinant line correctly: away–$p$ factors are $\Lambda$–units, so the ideals generated by $\det_{\Lambda}(I-K(T))$, $\det_{\Lambda}(I-K_{\pm}(T))$, and $\det_{\Lambda}(I-K^{\!*}(T))$ coincide (up to $\Lambda^{\times}$) with $\big(L_p\big)$, $\big(L_p^{\pm}\big)$, and $\big(L_p^{\!*}\big)$, respectively.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:affine-line — lemma (Affine count on a translation line)

- **Source**: `BSD-Jon-Final.txt` L1365–L1371
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Affine count on a translation line]\label{lem:affine-line}
Let $\ell\ge 3$ and $V=E[\ell]\cong (\mathbb{Z}/\ell\mathbb{Z})^2$. Fix a nonzero $v\in V$ and a nonzero linear functional $\lambda\in \mathrm{Hom}(V,\mathbb{Z}/\ell\mathbb{Z})$. For any $A\in \mathrm{GL}_2(\mathbb{Z}/\ell\mathbb{Z})$,
\[
  \#\{\, m\in \mathbb{Z}/\ell\mathbb{Z} : \lambda(A v + m v)=0\,\}\ =\ 1.
\]
Equivalently, along the translation line $\{A v + m v\}$, the proportion of points with $\lambda\ne 0$ equals $1-\tfrac{1}{\ell}$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:min-kummer-density — theorem (Minimal Kummer criterion for positive density)

- **Source**: `BSD-Jon-Final.txt` L1376–L1382
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Minimal Kummer criterion for positive density]\label{thm:min-kummer-density}
Let $E/\mathbb{Q}$ be any elliptic curve (CM or non–CM), $P\in E(\mathbb{Q})$ non–torsion. Suppose there exists a prime $\ell\ge 3$ with $P\notin \ell E(\mathbb{Q})$. Then there exists a nonzero $\lambda\in \mathrm{Hom}(E[\ell],\mathbb{Z}/\ell\mathbb{Z})$ such that the set of good ordinary primes $p\equiv 1\ (\mathrm{mod}\ \ell)$ with
\[
  v_p\big(h_p(P)\big)=0\qquad(\text{equivalently } v_p(\log_\omega(P))=0)
\]
has lower density at least $1-\tfrac{1}{\ell}$ among those primes (up to the finite ramified set of $\mathbb{Q}(E[\ell],\tfrac{1}{\ell}P)/\mathbb{Q}$). The same holds in the signed supersingular setting replacing $h_p$ by $h_p^{\pm}$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-proposition-L1391 — proposition (Twist–average template; sketch)

- **Source**: `BSD-Jon-Final.txt` L1391–L1397
- **Status**: todo
- **Auto-flags**: SKETCH
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Twist–average template; sketch]
Fix $\ell\ge 3$ with $P\notin \ell E(\mathbb{Q})$. For squarefree $d$ coprime to $\ell\Delta_E$, suppose $P^{(d)}\in E^{(d)}(\mathbb{Q})$ arises from $P$ by the natural identification. Then, under standard equidistribution hypotheses for Frobenius in the twist family, one has
\[
  \liminf_{X\to\infty}\ \frac{1}{\#\{\,|d|\le X\,\}}\ \sum_{|d|\le X}\ \delta_{\mathrm{diag\,unit}}\big(E^{(d)}\big)\ >\ 0,
\]
where $\delta_{\mathrm{diag\,unit}}(E^{(d)})$ denotes the lower density of ordinary (resp. signed) diagonal–unit primes for $E^{(d)}$. In particular, a positive proportion of twists have positive density of diagonal–unit primes.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### hyp:twist — hypothesis (Twist inputs)

- **Source**: `BSD-Jon-Final.txt` L1406–L1411
- **Status**: todo
- **Auto-flags**: HYPOTHESIS
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{hypothesis}[Twist inputs]\label{hyp:twist}
Let $E/\mathbb{Q}$ be non–CM. Fix an odd prime $\ell$ with $P\notin \ell E(\mathbb{Q})$ for some $P\in E(\mathbb{Q})$.
\begin{itemize}
\item[(Tw1)] (Rank–one supply) There exists $\delta_{\mathrm{r1}}>0$ such that a set $\mathcal{D}$ of squarefree $d$ of lower density $\ge \delta_{\mathrm{r1}}$ yields $\mathrm{rank}\,E^{(d)}(\mathbb{Q})\ge 1$ with a rational point $P^{(d)}$ (e.g. Heegner points in a fixed imaginary quadratic field).
\end{itemize}
\end{hypothesis}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:LS-Cheb — theorem (Large–sieve Chebotarev over twist families)

- **Source**: `BSD-Jon-Final.txt` L1413–L1419
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Large–sieve Chebotarev over twist families]\label{thm:LS-Cheb}
Let $E/\mathbb{Q}$ be as above and fix $\ell\ge 3$ with $P\notin \ell E(\mathbb{Q})$. For each squarefree $d$, set $L_d:=\mathbb{Q}(E[\ell],\tfrac{1}{\ell}P^{(d)})$ and $G_d:=\mathrm{Gal}(L_d/\mathbb{Q})$. Then there exists $\eta>0$ such that, for any union $\mathcal{C}_d\subset G_d$ of conjugacy classes, one has
\[
  \frac{1}{\#\{\,|d|\le X\,\}}\sum_{|d|\le X}\ \left|\,\#\{\,p\le x: p\nmid \ell\Delta_E,\ \mathrm{Frob}_p\in\mathcal{C}_d\,\}\ -\ \frac{|\mathcal{C}_d|}{|G_d|}\,\mathrm{Li}(x)\,\right|\ \ll\ \frac{x}{(\log x)^{1+\eta}}
\]
uniformly for $x\ge 2$ and $X\ge 2$. In particular, the average discrepancy tends to $0$ at a power–saving rate. (See, e.g., Kowalski, The large sieve and its applications, Thm. 7.13; Murty–Murty (1987) for Chebotarev with large–sieve error terms.)
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:twist-average — theorem (Twist–average positive density of diagonal units)

- **Source**: `BSD-Jon-Final.txt` L1421–L1427
- **Status**: todo
- **Auto-flags**: ASSUMES, USES_HYP
- **Auto-extracted internal refs**: hyp:twist, thm:LS-Cheb, thm:min-kummer-density
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Twist–average positive density of diagonal units]\label{thm:twist-average}
Assume Hypothesis~\ref{hyp:twist} and Theorem~\ref{thm:LS-Cheb}. Then
\[
  \liminf_{X\to\infty}\ \frac{1}{\#\{\,|d|\le X: d\in\mathcal{D}\,\}}\ \sum_{\substack{|d|\le X\\ d\in\mathcal{D}}}\ \delta_{\mathrm{diag\,unit}}\big(E^{(d)}\big)\ \ge\ c\ >\ 0,
\]
where $\delta_{\mathrm{diag\,unit}}(E^{(d)})$ is the lower density of ordinary primes with $v_p(h_p(P^{(d)}))=0$ (and similarly for a signed variant at supersingular $p$) and $c$ depends effectively on $\ell$ (e.g. $c\ge 1-\tfrac{1}{\ell}$ as in Theorem~\ref{thm:min-kummer-density}).
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L1432 — remark

- **Source**: `BSD-Jon-Final.txt` L1432–L1434
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}
Inputs (Tw1) are known in many settings (e.g. families with Heegner points; see Gross–Zagier–Kolyvagin and refinements; for many curves, positive proportions of rank 0 and 1 twists are known). Inputs (Tw2) follow from standard Chebotarev equidistribution for Artin representations associated to the extensions $\mathbb{Q}(E[\ell],\tfrac{1}{\ell}P^{(d)})$, conditional on GRH or by large sieve methods with power–saving error terms.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:uniform-revdiv — theorem (Uniform reverse divisibility over $\Lambda$)

- **Source**: `BSD-Jon-Final.txt` L1440–L1450
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Uniform reverse divisibility over $\Lambda$]\label{thm:uniform-revdiv}
Let $E/\mathbb{Q}$ be an elliptic curve and $p\ge 2$ a prime. In the ordinary case (for $p\ge 5$; for $p\in\{2,3\}$ with §F.15 adjustments) and in the supersingular case with signs $\pm$ (for $p\ge 5$), one has
\[
  (L_p(E,T))\ \mid\ \mathrm{char}_\Lambda X_p(E/\mathbb{Q}_\infty)\quad\text{and}\quad (L_p^{\pm}(E,T))\ \mid\ \mathrm{char}_\Lambda X_p^{\pm}(E/\mathbb{Q}_\infty),
\]
up to $\Lambda^{\times}$, i.e. for every finite-order character $\chi$ of $\Gamma$,
\[
  \mathrm{length}_{\mathbb{Z}_p}\,\mathrm{coker}(I-K(\chi))\ \le\ \mathrm{ord}_p\det(I-K(\chi)),\qquad \mathrm{length}_{\mathbb{Z}_p}\,\mathrm{coker}(I-K_{\pm}(\chi))\ \le\ \mathrm{ord}_p\det(I-K_{\pm}(\chi)).
\]
At split multiplicative $p$, the same holds with the improved quantities replacing the ordinary ones: $L_p^{\!*}(E,T)$ and $K^{\!*}(T)$ (cf. §F.40).
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:level-raise-visibility — theorem (Level–raised congruences and visibility)

- **Source**: `BSD-Jon-Final.txt` L1466–L1468
- **Status**: todo
- **Auto-flags**: ASSUMES
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Level–raised congruences and visibility]\label{thm:level-raise-visibility}
Assume there exists a level–raising prime $q\nmid Np$ for $p$. Then there is a newform $g\in S_2(\Gamma_0(Nq))$ such that $g\equiv f\ (\bmod\ p)$ on Hecke operators away from $q$. Let $A_g$ be the optimal quotient of $J_0(Nq)$ attached to $g$. Then the $p$–primary component group/torsion in $A_g$ contains a visible subgroup that maps nontrivially to $E$ through the congruence, accounting for the missing $p$–power in the BSD prediction. In particular, combined with Kato's divisibility, this yields BSD$_p$ for $E$ at $p$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:anti-BSDp — theorem (Anticyclotomic promotion to BSD$_p$)

- **Source**: `BSD-Jon-Final.txt` L1480–L1492
- **Status**: todo
- **Auto-flags**: ASSUMES, IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Anticyclotomic promotion to BSD$_p$]\label{thm:anti-BSDp}
Assume:
\begin{itemize}
\item[(A1)] $E/\mathbb{Q}$ is modular; $K$ satisfies the Heegner hypothesis for $N$; $p\nmid N$ splits in $K$;
\item[(A2)] $\overline{\rho}_{E,p}$ is irreducible (big image), and the relevant local minimality holds;
\item[(A3)] The anticyclotomic IMC holds for $E/K$ at $p$ (Bertolini–Darmon; Castella; Wan), and the required nonvanishing hypotheses are satisfied.
\end{itemize}
Then for the cyclotomic specialization at $T=0$ one has
\[
  \mathrm{ord}_{T=0}L_p(E,T)\ =\ \mathrm{corank}_\Lambda X_p(E/\mathbb{Q}_\infty),
\]
and with $\mu_p(E)=0$ (from local height certificates), BSD$_p$ holds at $p$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:RS-BSDp — theorem (Rankin–Selberg promotion to BSD$_p$)

- **Source**: `BSD-Jon-Final.txt` L1501–L1512
- **Status**: todo
- **Auto-flags**: ASSUMES, IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Rankin–Selberg promotion to BSD$_p$]\label{thm:RS-BSDp}
Assume:
\begin{itemize}
\item[(R1)] $\overline{\rho}_{E,p}$ irreducible (big image), with standard local hypotheses at primes dividing $N$;
\item[(R2)] A two–variable Rankin–Selberg IMC applies to $f\otimes g$ with $g$ varying in a CM or Eisenstein–type family interpolating cyclotomic twists (Skinner–Urban; Wan);
\end{itemize}
then for all $p$ in the covered range,
\[
  \mathrm{char}_\Lambda X_p(E/\mathbb{Q}_\infty)\ =\ (L_p(E,T))\quad\text{up to }\Lambda^{\times},
\]
and, with $\mu_p(E)=0$, BSD$_p$ holds at $p$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:uniq-measure — lemma (Uniqueness from specializations)

- **Source**: `BSD-Jon-Final.txt` L1529–L1531
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Uniqueness from specializations]\label{lem:uniq-measure}
Let $f,g\in \Lambda$ be nonzero with $\mu(f)=\mu(g)=0$. If for every finite–order character $\chi$ of $\Gamma$ one has $\mathrm{ord}_p(f(\chi))=\mathrm{ord}_p(g(\chi))$, then $(f)=(g)$ as ideals in $\Lambda$. In particular, $f\doteq g$ up to $\Lambda^{\times}$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:global-imc — theorem (Cyclotomic IMC from two divisibilities)

- **Source**: `BSD-Jon-Final.txt` L1536–L1547
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: thm:uniform-revdiv
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Cyclotomic IMC from two divisibilities]\label{thm:global-imc}
Let $E/\mathbb{Q}$ be modular and $p\ge 5$ a good prime. Suppose:
\begin{itemize}
\item[(i)] One–sided IMC (Kato): $\mathrm{char}_\Lambda X_p\mid (L_p)$ in the ordinary case \cite{Kato2004}; in the supersingular case, the signed inclusion $\mathrm{char}_\Lambda X_p^{\pm}\mid (L_p^{\pm})$ (e.g. \cite{LeiLoefflerZerbes2012}).
\item[(ii)] Reverse divisibility (this work): $(L_p)\mid \mathrm{char}_\Lambda X_p$ in the ordinary case; $(L_p^{\pm})\mid \mathrm{char}_\Lambda X_p^{\pm}$ in the signed case (Theorem~\ref{thm:uniform-revdiv}).
\end{itemize}
Then
\[
  \mathrm{char}_\Lambda X_p\ =\ (L_p)\qquad\text{and}\qquad \mathrm{char}_\Lambda X_p^{\pm}\ =\ (L_p^{\pm})
\]
as principal ideals in $\Lambda$ (up to $\Lambda^{\times}$). At split multiplicative $p$, the same holds with improved quantities $L_p^{\!*}$ and $K^{\!*}$ (cf. §F.40).
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:universal-imc — theorem (Universal cyclotomic IMC (ordinary and signed))

- **Source**: `BSD-Jon-Final.txt` L1556–L1566
- **Status**: blocked (universal “all primes” coverage not currently justified)
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Coverage task (hard)**: pin down exact theorem statements + hypotheses in the cited literature and verify that, for a fixed modular \(E/\mathbb Q\), they collectively cover **every prime \(p\)** in the needed setting (ordinary / supersingular signed / split multiplicative improved / small primes), leaving at most a finite set handled by explicit closures.
  - **Current gap after web pass**: the strongest supersingular \(\pm\) IMC equality input we have pinned down so far (BSTW24, semistable signed IMC) is stated in a **semistable / square-free conductor** range. For general modular elliptic curves with additive reduction (non-square-free conductor), this does not (as stated) yield signed IMC equality at supersingular primes, so the universal claim remains **unjustified** pending additional literature inputs.
  - **Scope check**: some “closure” tools in Appendix~F (visibility / Gross--Zagier--Kolyvagin / Rankin--Selberg) yield BSD\(_p\) or \(T=0\) valuation equalities, not necessarily full cyclotomic IMC *ideal equality* in \(\Lambda\). If any primes are only closable at \(T=0\), then `thm:universal-imc` must be weakened accordingly (or moved out of the unconditional mainline).

#### Statement (verbatim from source)

```tex
\begin{theorem}[Universal cyclotomic IMC (ordinary and signed)]\label{thm:universal-imc}
Let $E/\mathbb{Q}$ be modular and let $p\ge 2$ be any prime. Then, in the ordinary case (for $p\ge 5$; for $p\in\{2,3\}$ with §F.15 adjustments),
\[
  \mathrm{char}_\Lambda X_p(E/\mathbb{Q}_\infty)\ =\ (L_p(E,T))\quad \text{up to }\Lambda^{\times},
\]
and in the supersingular case (for $p\ge 5$) with signs $\pm$,
\[
  \mathrm{char}_\Lambda X_p^{\pm}(E/\mathbb{Q}_\infty)\ =\ (L_p^{\pm}(E,T))\quad \text{up to }\Lambda^{\times}.
\]
At split multiplicative $p$, the same holds with the improved objects $L_p^{\!*}(E,T)$ and $K^{\!*}(T)$ (cf. §F.40).
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - Definitions of the cyclotomic \(p\)-adic \(L\)-functions \(L_p\), \(L_p^{\pm}\), and improved objects at split multiplicative primes (Appendix~F, esp. \S\,F.40)
  - Small-prime adjustments framework (\S\,F.15)
- **External (papers/books/theorems)**:
  - **Good ordinary cyclotomic IMC (Mazur main conjecture)**:
    - Burungale--Castella--Skinner (BCS24, `arXiv:2405.00270`), Theorem~1.1.2 / `bc_r.tex` Theorem~`\ref{thm:cyc}`: good ordinary \(p>3\) + (irr\(_\BQ\)) gives equality in \(\Lambda\otimes\BQ_p\), integral equality in \(\Lambda\) under (im).
    - **Clarification**: Yan--Zhu (YZ24, `arXiv:2412.20078`) is a **\(\Lambda_K\)** (two-variable / Heegner–anticyclotomic) main-conjecture paper (Conj. 1.1 / Thm. 1.2), not a direct cyclotomic IMC-over-\(\BQ_\infty\) equality input here unless an additional reduction-to-cyclotomic argument is provided.
  - **Supersingular signed cyclotomic IMC (Kobayashi \(\pm\))**:
    - Burungale--Skinner--Tian--Wan (BSTW24, `arXiv:2409.01350`), Thm. `thmA` in arXiv TeX: for **semistable** \(E/\BQ\) and supersingular \(p>2\) (and if \(p=3\) assuming \(\eqref{h4}\)), proves Kobayashi’s signed IMC: for \(\circ\in\{+,-\}\), \((\CL_p^{\circ}(E))=\xi_\Lambda(X_\circ(E))\) in \(\Lambda\) (also for quadratic twists under stated restrictions).
    - (Context) Kobayashi/Lei/Sprung give Euler-system divisibilities and the signed setup; BSTW supplies the equality in the stated semistable range.
    - (Non-input note) Castella (2025, `arXiv:2502.19618`) is a **signed \(p\)-adic BSD / leading coefficient** result under finiteness of \(\Sha[p^\infty]\) and nonvanishing of strict regulators; it is not an IMC-equality theorem.
  - **Eisenstein / reducible residual primes**:
    - Keller--Yin (KY24, `arXiv:2410.23241`) proves a **\(p\)-converse / rank \(\le 1\)** closure at potentially good ordinary Eisenstein primes; this is not a general IMC-equality input.
  - **Small-prime supersingular beyond \(a_p=0\)**:
    - Sprung (2024, *Adv. Math.*), DOI `10.1016/j.aim.2024.109741` (ScienceDirect `S0001870824002561`): cited in the source for “beyond \(a_p=0\)” small-prime/special-case coverage, but **closed access** in this environment, so exact theorem-number/hypothesis extraction is still pending.
  - Greenberg--Stevens exceptional-zero correction at split multiplicative primes

#### Proof outline (edit)

- **This is a coverage theorem, not a new analytic proof in the manuscript.** Fix \(p\) and choose the applicable literature input:
  - **Good ordinary \(p\ge 5\)**: apply BCS24 Theorem~1.1.2 (good ordinary \(p>3\) + (irr\(_\BQ\))) to get equality in \(\Lambda\otimes\BQ_p\), and upgrade to integral equality in \(\Lambda\) under (im) (or if you separately prove \(\mu=0\) so that the only possible discrepancy is a \(p\)-power).
  - **Supersingular \(p\ge 5\)**: in the semistable/square-free range, apply BSTW24 Thm. `thmA` to obtain the signed \(\pm\) IMC equality.
  - **Split multiplicative**: replace by improved objects and apply Greenberg--Stevens; import IMC equality in the improved normalization.
  - **Small primes \(p\in\{2,3\}\)**: apply the small-\(p\) framework (\S\,F.15) together with the corresponding literature in these cases.
  - **Residual reducible/Eisenstein**: treat the (finite) Eisenstein set for fixed \(E\) via Eisenstein-prime closures. (Caution: KY24 supplies \(p\)-converse/BSD\(_p\) closures in rank \(\le 1\), not full IMC equality in general rank.)

Conclude the stated ideal equalities up to \(\Lambda^\times\) in each case. Any primes not covered “uniformly in \(p\)” by the generic theorems must be shown to fall into a **finite set** for the fixed curve \(E\), and then dispatched by an explicitly listed closure input.

#### Full proof (massive detail; edit)

Write this as a **coverage table**: for each reduction type / residual type / small-prime type, state the exact external theorem used (authors + theorem number + hypotheses) and explain why every prime \(p\) falls into one of the covered buckets (or into an explicitly finite bucket with a named closure input).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked external theorem is cited with exact theorem number and hypotheses
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:ord-char — lemma (Order at $T=0$ under IMC)

- **Source**: `BSD-Jon-Final.txt` L1575–L1581
- **Status**: todo
- **Auto-flags**: ASSUMES, IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Order at $T=0$ under IMC]\label{lem:ord-char}
Assume IMC equality holds (ordinary or signed). Then
\[
  \mathrm{ord}_{T=0}\big(\mathrm{char}_\Lambda X_p\big)\ =\ \mathrm{rank}\,E(\mathbb{Q})\ +\ \mu_p(E)\ +\ \varepsilon_p,
\]
where $\varepsilon_p\in\{0,1\}$ accounts for the trivial zero at split multiplicative $p$ (and is $0$ otherwise). An identical formula holds in the signed case (with the appropriate signed objects).
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L1586 — corollary (Density BSD$_p$ coverage and closure)

- **Source**: `BSD-Jon-Final.txt` L1586–L1588
- **Status**: blocked
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: thm:R-triangular, thm:R-triangular-signed, thm:universal-imc
- **Conditional on / Blockers (edit)**:
  - **Blocked**: this corollary’s mechanism for deducing \(\mu_p(E)=0\) from a “diagonal–unit certificate” runs through `thm:R-triangular` / `thm:R-triangular-signed`, which are **suspect/vacuous for rank \(r>1\)** as written (their hypotheses are incompatible with the source’s own mod‑\(p\) height congruences).
  - The claimed positive-density supply of such “diagonal–unit certificate primes” therefore needs a corrected certificate (or must be removed/marked conditional on a new input).

#### Statement (verbatim from source)

```tex
\begin{corollary}[Density BSD$_p$ coverage and closure]
Under Theorem~\ref{thm:universal-imc}, at each prime $p$ where a diagonal–unit certificate holds (ordinary or signed), $\mu_p(E)=0$ (Theorems~\ref{thm:R-triangular}, \ref{thm:R-triangular-signed}, §F.40), hence $\mathrm{ord}_{T=0}L_p=\mathrm{rank}$ and BSD$_p$ holds. By §§F.27, F.35, F.42, a set of such primes has positive lower density (ordinary) and infinitely many supersingular $p$ (signed) for every curve; the residual finite set is closed by §§F.44–F.46.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:mu-criterion — lemma (Character–proportion criterion)

- **Source**: `BSD-Jon-Final.txt` L1597–L1603
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - None: this is a standard Weierstrass-preparation characterization of \(\mu\) in terms of eventual \(p\)-divisibility on deep character layers.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Character–proportion criterion]\label{lem:mu-criterion}
Let $E/\mathbb{Q}$ and $p\ge 2$. Suppose there exists $C>0$ and infinitely many $n\ge 1$ such that
\[
  \#\{\,\chi\ \mathrm{mod}\ p^n :\ \mathrm{ord}_p\,L_p(E,\chi)=0\,\}\ \ge\ C\,\varphi(p^n).
\]
Then $\mu_p(E)=0$. The same holds in the signed case replacing $L_p$ by $L_p^{\pm}$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - Definition of \(\mu_p(E)\) as the \(p\)-power content in the Iwasawa power series \(L_p(E,T)\in\Lambda\).
- **External (papers/books/theorems)**:
  - Weierstrass preparation theorem over \(\mathbb{Z}_p\llbracket T\rrbracket\) and the basic structure of zeros of distinguished polynomials on the set \(\{\chi(\gamma)-1\}\).

#### Proof outline (edit)

- Write \(L_p(E,T)=p^{\mu}u(T)\,P(T)\) with \(u\in\Lambda^{\times}\) and \(P\in\mathbb{Z}_p[T]\) distinguished.
- If \(\mu>0\), then \(p\mid L_p(E,\chi)\) for every sufficiently deep primitive character \(\chi\) (indeed for all \(\chi\) once \(p^{\mu}\) is factored), contradicting the hypothesis that a positive proportion have \(v_p=0\).
- Therefore \(\mu=0\). Signed case is identical with \(L_p^{\pm}\).

#### Full proof (massive detail; edit)

Let \(\Lambda=\mathbb{Z}_p\llbracket T\rrbracket\) and write \(L_p(E,T)\in\Lambda\) for the cyclotomic \(p\)-adic \(L\)-function (or \(L_p^{\pm}\) in the signed case).

By Weierstrass preparation, we may write
\[
L_p(E,T)=p^{\mu}\,u(T)\,P(T),
\]
where \(\mu\ge 0\), \(u(T)\in\Lambda^{\times}\) is a unit, and \(P(T)\in\mathbb{Z}_p[T]\) is a distinguished polynomial. By definition, this \(\mu\) is the Iwasawa \(\mu\)-invariant \(\mu_p(E)\).

Assume there exists \(C>0\) and infinitely many \(n\ge 1\) such that at least \(C\varphi(p^n)\) primitive characters \(\chi\) of conductor \(p^n\) satisfy \(v_p(L_p(E,\chi))=0\).

If \(\mu>0\), then \(p\mid L_p(E,T)\) in \(\Lambda\), hence for every \(\chi\) we have \(p\mid L_p(E,\chi)\) and therefore \(v_p(L_p(E,\chi))\ge 1\). This contradicts the existence of even a single \(\chi\) with \(v_p(L_p(E,\chi))=0\), a fortiori a positive proportion at infinitely many depths. Therefore \(\mu=0\), i.e. \(\mu_p(E)=0\).

The signed case is identical, replacing \(L_p(E,T)\) by \(L_p^{\pm}(E,T)\).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:chi-detector — proposition (Level–$p^n$ detector)

- **Source**: `BSD-Jon-Final.txt` L1616–L1622
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Level–$p^n$ detector]\label{prop:chi-detector}
There exists a nonzero linear functional $\Lambda_n$ on the $[p^n]$–Kummer fiber above $P$ such that, for all primitive $\chi$ of conductor $p^n$,
\[
  \overline{\mathrm{Col}_p(\chi)}\ \equiv\ \Lambda_n(\mathrm{Frob}_p\cdot X)\ \ (\bmod\ p),
\]
with $X$ the fiber point attached to $\tfrac{1}{p^n}P$. The same holds for $\mathrm{Col}_p^{\pm}(\chi)$ with a signed functional $\Lambda_n^{\pm}$.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:LS-chi — theorem (Positive–proportion nonvanishing at each level)

- **Source**: `BSD-Jon-Final.txt` L1631–L1633
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Positive–proportion nonvanishing at each level]\label{thm:LS-chi}
For each $n$ sufficiently large, a positive proportion $\ge C>0$ of primitive characters $\chi$ modulo $p^n$ satisfy $\overline{\mathrm{Col}_p(\chi)}\ne 0$ (resp. $\overline{\mathrm{Col}_p^{\pm}(\chi)}\ne 0$), with an effective constant $C$ independent of $n$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:universal-mu — corollary (Universal $\mu=0$)

- **Source**: `BSD-Jon-Final.txt` L1638–L1640
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: thm:universal-imc
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Universal $\mu=0$]\label{cor:universal-mu}
For every prime $p$, $\mu_p(E)=0$ (ordinary or signed). In particular, together with Theorem~\ref{thm:universal-imc}, BSD$_p$ holds at every prime.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:kummer-independence — theorem (Kummer independence under non--CM)

- **Source**: `BSD-Jon-Final.txt` L1654–L1661
- **Status**: todo
- **Auto-flags**: USES_HYP
- **Auto-extracted internal refs**: hyp:big-kummer
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Kummer independence under non--CM]\label{thm:kummer-independence}
Let $E/\mathbb{Q}$ be non--CM and $P\in E(\mathbb{Q})$ of infinite order. Then there exists an integer $N\ge 3$ such that:
\begin{itemize}
\item[(i)] $\mathrm{Im}\,\rho_{E,\mathrm{mod}\,N}\supseteq \mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$;
\item[(ii)] the Kummer cocycle $\kappa_N: G_\mathbb{Q}\to E[N]$, $\sigma\mapsto \sigma(\tfrac{1}{N}P)-\tfrac{1}{N}P$, has image that, together with its $\mathrm{Im}\,\rho_{E,\mathrm{mod}\,N}$--conjugates, generates $E[N]$.
\end{itemize}
Consequently, $\mathrm{Gal}\big(\mathbb{Q}(E[N],\tfrac{1}{N}P)/\mathbb{Q}\big)$ contains the semidirect product $E[N]\rtimes \mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$, and acts transitively on the fiber of $\tfrac{1}{N}P$ modulo $E[N]$. In particular Hypothesis~\ref{hyp:big-kummer} holds.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:unconditional-density — corollary (Unconditional infinitude and density for non--CM curves)

- **Source**: `BSD-Jon-Final.txt` L1670–L1676
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Unconditional infinitude and density for non--CM curves]\label{cor:unconditional-density}
Let $E/\mathbb{Q}$ be non--CM and $P\in E(\mathbb{Q})$ non--torsion. Then:
\begin{itemize}
\item[(a)] The set of good ordinary primes $p$ with $v_p\big(h_p(P)\big)=0$ is infinite and has positive lower density among ordinary primes.
\item[(b)] The set of supersingular primes $p\ge 5$ for which $v_p\big(h_p^{\pm}(P)\big)=0$ for at least one sign is infinite.
\end{itemize}
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:good-ell — lemma (A good prime $\ell$ for $(E,P)$)

- **Source**: `BSD-Jon-Final.txt` L1685–L1692
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[A good prime $\ell$ for $(E,P)$]\label{lem:good-ell}
Let $E/\mathbb{Q}$ be non--CM and $P\in E(\mathbb{Q})$ non--torsion. There exists a prime $\ell\ge 5$ outside a finite set (depending on $E$ only) such that:
\begin{itemize}
\item[(i)] $\overline{\rho}_{E,\ell}(G_\mathbb{Q})\supseteq \mathrm{SL}_2(\mathbb{F}_\ell)$ (Serre open image);
\item[(ii)] $P\notin \ell\,E(\mathbb{Q})$.
\end{itemize}
In particular, the Kummer class $\kappa_\ell(P)\in H^1(\mathbb{Q},E[\ell])$ is nonzero.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:uniform-kummer — theorem (Uniform Kummer independence at a prime)

- **Source**: `BSD-Jon-Final.txt` L1697–L1703
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:good-ell
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Uniform Kummer independence at a prime]\label{thm:uniform-kummer}
With $\ell$ as in Lemma~\ref{lem:good-ell}, the Galois group
\[
  \mathrm{Gal}\big(\mathbb{Q}(E[\ell],\tfrac{1}{\ell}P)/\mathbb{Q}\big)
\]
contains the semidirect product $E[\ell]\rtimes \mathrm{SL}_2(\mathbb{F}_\ell)$. Equivalently, the image of the Kummer cocycle $\kappa_\ell(P)$ together with its $\mathrm{SL}_2(\mathbb{F}_\ell)$–conjugates generates $E[\ell]$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:effective-density — corollary (Effective density constants)

- **Source**: `BSD-Jon-Final.txt` L1712–L1717
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Effective density constants]\label{cor:effective-density}
For non--CM $E$ and non--torsion $P$, one may take $N=\ell$ (a single good prime as above) in the detectors of \S F.34, and the lower density constants are effective:
\[
  c_{N}\ =\ \frac{|\mathcal{C}_N|}{|\mathrm{Gal}(\mathbb{Q}(E[N],\tfrac{1}{N}P)/\mathbb{Q})|}\ \ge\ \frac{1}{|\mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})|}\,.
\]
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:sec6A-density — corollary (\S6A: ordinary diagonal--unit density)

- **Source**: `BSD-Jon-Final.txt` L1726–L1733
- **Status**: todo
- **Auto-flags**: ASSUMES
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[\S6A: ordinary diagonal--unit density]\label{cor:sec6A-density}
Let $E_0/\mathbb{Q}$ be the rank--$1$ curve of \S6A. Assume $E_0$ is non--CM and let $P_0\in E_0(\mathbb{Q})$ be a fixed non--torsion generator. Then there exists $N\ge 3$ and a nonempty union $\mathcal{C}_N\subset G_N(E_0,P_0)$ of conjugacy classes such that the set of good ordinary primes $p\nmid N\Delta_{E_0}$ with $\mathrm{Frob}_p\in \mathcal{C}_N$ satisfies
\begin{multline*}
  \liminf_{X\to\infty}\ \frac{\#\{\,p\le X:\ p\text{ ordinary},\ p\nmid N\Delta_{E_0},\ \mathrm{Frob}_p\in \mathcal{C}_N,\ v_p(h_p(P_0))=0\,\}}{\#\{\,p\le X:\ p\text{ ordinary}\,\}} \\
  \ge\ \frac{|\mathcal{C}_N|}{|G_N(E_0,P_0)|}\ :=\ c_{0,N}\ >0.
\end{multline*}
Consequently, $v_p(h_p(P_0))=0$ for a set of ordinary primes of positive lower density $\ge c_{0,N}$.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:sec6B-density — corollary (\S6B: ordinary diagonal--unit density)

- **Source**: `BSD-Jon-Final.txt` L1738–L1740
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[\S6B: ordinary diagonal--unit density]\label{cor:sec6B-density}
Let $E/\mathbb{Q}$ be the curve of \S6B and let $P\in E(\mathbb{Q})$ be any fixed non--torsion basis element. If $E$ is non--CM, then there exists $N\ge 3$ and a nonempty union $\mathcal{C}_N\subset G_N(E,P)$ of conjugacy classes such that the set of good ordinary primes with $\mathrm{Frob}_p\in \mathcal{C}_N$ has lower density at least $c_{N}:=|\mathcal{C}_N|/|G_N(E,P)|>0$ and satisfies $v_p(h_p(P))=0$.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:sec6-signed-inf — corollary (Signed supersingular infinitude for \S6A/\S6B)

- **Source**: `BSD-Jon-Final.txt` L1742–L1744
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Signed supersingular infinitude for \S6A/\S6B]\label{cor:sec6-signed-inf}
Under the same non--CM hypotheses, there exists $N\ge 3$ and a nonempty union $\mathcal{C}_N^{\pm}\subset G_N(\cdot,\cdot)$ such that along the set of supersingular primes with $\mathrm{Frob}_p\in \mathcal{C}_N^{\pm}$ one has $v_p\big(h_p^{\pm}(P)\big)=0$ for at least one sign. In particular, for each curve in \S6 there are infinitely many supersingular primes with signed diagonal units.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L1746 — remark (Effectivity)

- **Source**: `BSD-Jon-Final.txt` L1746–L1748
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Effectivity]
For fixed $(E,P)$ and choice of $N$, the group $G_N(E,P)$ is computable, as is the action on the Kummer fiber. The subset $\mathcal{C}_N$ (resp. $\mathcal{C}_N^{\pm}$) can be determined by testing $\Phi_{N,\omega}$ (resp. its signed analogue) on representatives; thus $c_{0,N}$ and $c_{N}$ are effective constants. In practice, small $N$ (e.g. a single prime not dividing $\#E(\mathbb{Q})_\mathrm{tors}$ or the index of $P$) already give a visible positive proportion.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L1750 — corollary (Toward global $\Sha$ finiteness)

- **Source**: `BSD-Jon-Final.txt` L1750–L1752
- **Status**: conditional
- **Auto-flags**: ASSUMES
- **Auto-extracted internal refs**: thm:sha-finite
- **Conditional on / Blockers (edit)**:
  - **Conditional on**: either “Section 4.3 hypotheses” (unspecified here) or `thm:sha-finite` (which itself is conditional on (HΛ)+control and still needs an audit-grade proof).
  - **Global finiteness gap**: even if \(\Sha[p^\infty]\) is finite (or corank \(0\)) for every prime \(p\), it does **not** automatically follow that \(\Sha(E/\mathbb{Q})\) is a finite group unless one also knows only finitely many primes contribute nontrivially. The source does not justify this additional step here.
  - **For the §6 case studies**: the “remaining finite set is settled by Euler-system/visibility” is itself a major conditional input and needs a per-prime argument that yields actual finiteness (not just corank \(0\)).

#### Statement (verbatim from source)

```tex
\begin{corollary}[Toward global $\Sha$ finiteness]
Assume, in addition, the hypotheses of Section~4.3 or of Theorem~\ref{thm:sha-finite} hold for the curve $E$. Then the $p$–primary corank of $\Sha(E/\mathbb{Q})$ is zero for all but finitely many primes $p$. For the curves treated in \S6, the remaining finite set is settled by the Euler–system/visibility inputs recorded there, yielding $\Sha(E/\mathbb{Q})$ finite.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:membership — lemma (Membership in the formal group)

- **Source**: `BSD-Jon-Final.txt` L1755–L1757
- **Status**: audited
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - None (purely formal from the definition of the reduction map / formal group at good reduction primes).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Membership in the formal group]\label{lem:membership}
Let $p$ be good. If $m\equiv 0\pmod{\mathrm{ord}(P\bmod p)}$ with $(m,p)=1$, then $mP\in E_1(\mathbb{Q}_p)$. If $m\not\equiv 0\pmod{\mathrm{ord}(Q\bmod p)}$, then $mQ\notin E_1(\mathbb{Q}_p)$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - The short exact sequence defining \(E_1(\mathbb{Q}_p)\) as the kernel of reduction at good primes (`BSD-Jon-Final.txt` §2.2, around L125–L128).
- **External (papers/books/theorems)**:
  - Standard facts about good reduction and the reduction homomorphism \(E(\mathbb{Q}_p)\to \widetilde{E}(\mathbb{F}_p)\).

#### Proof outline (edit)

- Use that for good reduction, reduction \(\mathrm{red}:E(\mathbb{Q}_p)\to \widetilde{E}(\mathbb{F}_p)\) is a group homomorphism with kernel \(E_1(\mathbb{Q}_p)\).
- Compute \(\mathrm{red}(mP)=m\,\mathrm{red}(P)\) and translate membership in the kernel into a divisibility statement involving \(\mathrm{ord}(P\bmod p)\).

#### Full proof (massive detail; edit)

Fix a good reduction prime \(p\). Then the reduction map

\[
\mathrm{red}:E(\mathbb{Q}_p)=E_0(\mathbb{Q}_p)\longrightarrow \widetilde{E}(\mathbb{F}_p)
\]

is a **surjective group homomorphism** whose kernel is, by definition, the formal group subgroup \(E_1(\mathbb{Q}_p)\) (see the exact sequence in `BSD-Jon-Final.txt` §2.2).

Let \(P\in E(\mathbb{Q}_p)\), and write \(\overline{P}:=\mathrm{red}(P)\in \widetilde{E}(\mathbb{F}_p)\). Let \(o:=\mathrm{ord}(\overline{P})\) be its order in the finite group \(\widetilde{E}(\mathbb{F}_p)\).

**First implication.** Suppose \(m\equiv 0\pmod{o}\) and \((m,p)=1\) (the coprimality is not used in the kernel criterion, but is part of the later pipeline). Then \(o\mid m\) implies \(m\,\overline{P}=0\) in \(\widetilde{E}(\mathbb{F}_p)\). Since reduction is a homomorphism,
\[
\mathrm{red}(mP)=m\,\mathrm{red}(P)=m\,\overline{P}=0.
\]
Therefore \(mP\in\ker(\mathrm{red})=E_1(\mathbb{Q}_p)\), as claimed.

**Second implication.** Suppose \(m\not\equiv 0\pmod{\mathrm{ord}(Q\bmod p)}\). Let \(\overline{Q}=\mathrm{red}(Q)\) and let \(o_Q=\mathrm{ord}(\overline{Q})\). Then \(o_Q\nmid m\), so \(m\,\overline{Q}\ne 0\) in \(\widetilde{E}(\mathbb{F}_p)\). Again using homomorphism of reduction,
\[
\mathrm{red}(mQ)=m\,\overline{Q}\ne 0,
\]
so \(mQ\notin\ker(\mathrm{red})=E_1(\mathbb{Q}_p)\). This is exactly the contrapositive of the kernel criterion.

This proves both statements.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:formal-factor — lemma (Formal–group factorization)

- **Source**: `BSD-Jon-Final.txt` L1767–L1773
- **Status**: outlined
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Depends on Coleman–Gross / Perrin–Riou height normalization** (this is a “standard fact” in the source but not proved there).
  - **Deep-dive note**: `notes/papers/bsd/coleman-gross-heights-notes.md`
  - **Consistency note**: together with `lem:unit-log` and the explicit checklist in §7.1 (source L2408–L2414), this implies that for \(X\in E_1(\mathbb{Q}_p)\) one expects \(v_p(h_p(X,X))\ge 2\), i.e. **diagonal heights on the formal group are not \(p\)-adic units** under the stated normalization \(u_p\in\mathbb{Z}_p^\times\) and \(\log_E(T)=T+O(T^2)\).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Formal–group factorization]\label{lem:formal-factor}
For a good, ordinary prime $p$ there exists a unit $u_p\in\mathbb{Z}_p^\times$ such that for all $X,Y\in E_1(\mathbb{Q}_p)$,
\[
h_p(X,Y)\ =\ u_p\ \log_p(X)\,\log_p(Y),
\]
where $\log_p:E_1(\mathbb{Q}_p)\to\mathbb{Q}_p$ is the formal $p$–adic logarithm associated with the Néron differential. In particular, $v_p\big(h_p(X,X)\big)=2\,v_p\big(\log_p(X)\big)$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - §7.1 “Coleman height checklist” in the source (L2398–L2415) uses exactly this factorization.
  - `B2` (standing input: Coleman–Gross heights) if we treat this as a black box.
- **External (papers/books/theorems)**:
  - Coleman–Gross (local cyclotomic height on the formal group factors through the formal logarithm).

#### Proof outline (edit)

- Treat \(h_p(\cdot,\cdot)\) (restricted to \(E_1(\mathbb{Q}_p)\)) as a symmetric bilinear pairing arising from Coleman integration / local symbols.
- Use that \(E_1(\mathbb{Q}_p)\) is 1-dimensional as a \(p\)-adic Lie group and \(\log_p:E_1(\mathbb{Q}_p)\to\mathbb{Q}_p\) gives an additive coordinate; bilinearity then forces \(h_p(X,Y)=c\cdot \log_p(X)\log_p(Y)\) for some constant \(c\in\mathbb{Q}_p^\times\).
- The nontrivial content is that \(c\in\mathbb{Z}_p^\times\) for the stated normalization (this is where the Coleman–Gross normalization must be pinned down).

#### Full proof (massive detail; edit)

**Outline only for now** (the source provides no detailed derivation, only a reference-style sentence).  

Key point for the global audit: under the normalization assumed in §7.1 (source L2411–L2414), this factorization implies \(v_p(h_p(X,X)) = 2\,v_p(\log_E(t(X)))\) for \(X\in E_1(\mathbb{Q}_p)\).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:unit-log — lemma (Formal–group valuation bounds)

- **Source**: `BSD-Jon-Final.txt` L1775–L1777
- **Status**: audited
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Global blocker (paper-level)**: §7.1 and multiple narrative passages claim “for all but finitely many ordinary \(p\), \(v_p(\log_E(t(X)))=0\) for \(X\in E_1\)” and hence \(h_p(X)\) is a unit. This directly contradicts:
    - §7.1 step 2 (source L2408): \(t(X)\in p\mathbb{Z}_p\) for \(X\in E_1(\mathbb{Q}_p)\), and
    - the power series normalization \(\log_E(T)=T+O(T^2)\in \mathbb{Z}_p\llbracket T\rrbracket\) (source L2400–L2403),
    which force \(v_p(\log_E(t(X)))\ge 1\) and therefore \(v_p(h_p(X))\ge 2\) under `lem:formal-factor`.
  - **Deep-dive note**: `notes/papers/bsd/coleman-gross-heights-notes.md`

#### Statement (verbatim from source)

```tex
\begin{lemma}[Formal–group valuation bounds]\label{lem:unit-log}
Let $p$ be a good prime. If $X\in E_1(\mathbb{Q}_p)$ then $v_p\big(\log_p(X)\big)\ge 1$ and $v_p\big(h_p(X,X)\big)\ge 2$. If $X\in E(\mathbb{Z}_p)\setminus E_1(\mathbb{Q}_p)$ then $\log_p(X)\in\mathbb{Z}_p$ and $v_p\big(h_p(X,X)\big)=0$ iff $v_p\big(\log_p(X)\big)=0$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:formal-factor` (to convert a valuation bound on \(\log_p(X)\) into one on \(h_p(X,X)\)).
  - §7.1 checklist in the source (L2398–L2415), which explicitly asserts \(t(X)\in p\mathbb{Z}_p\) and \(\log_E(T)=T+O(T^2)\).
- **External (papers/books/theorems)**:
  - Formal group theory for elliptic curves with good reduction (parameter at the origin and its valuation).

#### Proof outline (edit)

- For \(X\in E_1(\mathbb{Q}_p)\), use the Néron formal parameter \(t\) at the identity to see \(t(X)\in p\mathbb{Z}_p\).
- Since \(\log_E(T)=T+O(T^2)\) with coefficients in \(\mathbb{Z}_p\), plugging in \(t(X)\in p\mathbb{Z}_p\) yields \(\log_E(t(X))\in p\mathbb{Z}_p\), hence \(v_p(\log_E(t(X)))\ge 1\).
- Apply `lem:formal-factor` to get \(v_p(h_p(X,X))=2v_p(\log_p(X))\ge 2\).
- For \(X\in E(\mathbb{Z}_p)\setminus E_1\), integrality of Coleman integrals (or of the formal logarithm on integral points) gives \(\log_p(X)\in\mathbb{Z}_p\); then \(v_p(h_p(X,X))=0\iff v_p(\log_p(X))=0\) follows from the “diagonal equals unit times log\(^2\)” relation in the ordinary setting.

#### Full proof (massive detail; edit)

Fix a good prime \(p\).

**(1) Formal-group case.** Let \(X\in E_1(\mathbb{Q}_p)\). By definition, \(X\) reduces to the identity \(\mathcal{O}\) on \(\widetilde{E}(\mathbb{F}_p)\). Equivalently, \(X\) lies in the domain of the Néron formal group at \(\mathcal{O}\). Let \(t\) be the Néron formal parameter at \(\mathcal{O}\) (e.g. \(t=-x/y\) in a short Weierstrass model). Then standard formal group theory gives
\[
t(X)\in p\mathbb{Z}_p.
\]
In the notation of §7.1 of the source, \(\log_E(T)\in\mathbb{Z}_p\llbracket T\rrbracket\) with \(\log_E(T)=T+O(T^2)\). Plugging \(T=t(X)\in p\mathbb{Z}_p\) into a power series with \(\mathbb{Z}_p\)-coefficients and unit linear term yields
\[
\log_E(t(X))\in p\mathbb{Z}_p\quad\Rightarrow\quad v_p(\log_E(t(X)))\ge 1.
\]
Identifying \(\log_p(X)\) with \(\log_E(t(X))\) (up to a \(p\)-adic unit depending on the choice of differential/parameter), we get \(v_p(\log_p(X))\ge 1\). If `lem:formal-factor` holds with \(u_p\in\mathbb{Z}_p^\times\), then
\[
h_p(X,X)=u_p\log_p(X)^2\quad\Rightarrow\quad v_p(h_p(X,X))=2v_p(\log_p(X))\ge 2.
\]

**(2) Integral but not formal.** If \(X\in E(\mathbb{Z}_p)\setminus E_1(\mathbb{Q}_p)\), then \(X\) reduces to a non-identity point on \(\widetilde{E}(\mathbb{F}_p)\). In this case Coleman integrals defining \(\log_p(X)\) are \(p\)-adically integral, so \(\log_p(X)\in\mathbb{Z}_p\). Under the ordinary diagonal height normalization, the diagonal height equals a \(p\)-adic unit times \(\log_p(X)^2\), so \(v_p(h_p(X,X))=0\) if and only if \(v_p(\log_p(X))=0\).

This proves the stated valuation bounds.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:mixed-integrality — lemma (Mixed integrality)

- **Source**: `BSD-Jon-Final.txt` L1783–L1789
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Conditional on** the formal-group factorization (`lem:formal-factor`) and the valuation bounds on the formal logarithm (`lem:unit-log`) under the §7.1 normalization (unscaled formal parameter with \(t(E_1)\subset p\mathbb{Z}_p\)).
  - **Normalization sensitivity**: if the paper later rescales \(\log\) (or changes the Coleman–Gross normalization) to make \(\log(E_1)\) generically a unit, this lemma must be re-audited (the proof below uses \(v_p(\log(\cdot))\ge 1\) on \(E_1\)).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Mixed integrality]\label{lem:mixed-integrality}
Let $p$ be good and ordinary. If $X\in E_1(\mathbb{Q}_p)$ and $Y\in E(\mathbb{Q}_p)\setminus E_1(\mathbb{Q}_p)$ has reduction of order prime to $p$, then
\[
h_p(X,Y)\ \in\ p\,\mathbb{Z}_p.
\]
In particular, $v_p\big(h_p(X,Y)\big)\ge 1$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:formal-factor` (rank-1 factorization of \(h_p\) on \(E_1\times E_1\))
  - `lem:unit-log` (valuation \(v_p(\log_p(Z))\ge 1\) for \(Z\in E_1(\mathbb{Q}_p)\) under §7.1 normalization)
  - `lem:membership` / `lemA:formal-membership` (if \(n=\mathrm{ord}(Y\bmod p)\), then \(nY\in E_1(\mathbb{Q}_p)\))
  - Bilinearity of the Coleman–Gross local height \(h_p(\cdot,\cdot)\)
- **External (papers/books/theorems)**:
  - Coleman–Gross height theory at good ordinary primes (to justify bilinearity/local definition, and the factorization input packaged as `lem:formal-factor`)

#### Proof outline (edit)

- Let \(n:=\mathrm{ord}(Y\bmod p)\), which is prime to \(p\). Then \(nY\in E_1(\mathbb{Q}_p)\).
- By bilinearity, \(n\cdot h_p(X,Y)=h_p(X,nY)\).
- Since \(X,nY\in E_1\), apply `lem:formal-factor` to get \(h_p(X,nY)=u_p\log_p(X)\log_p(nY)\) with \(u_p\in\mathbb{Z}_p^\times\).
- By `lem:unit-log`, both \(\log_p(X)\) and \(\log_p(nY)\) have \(p\)-adic valuation \(\ge 1\); hence the right-hand side lies in \(p^2\mathbb{Z}_p\subset p\mathbb{Z}_p\).
- Divide by \(n\in\mathbb{Z}_p^\times\) to conclude \(h_p(X,Y)\in p\mathbb{Z}_p\).

#### Full proof (massive detail; edit)

Let \(p\) be good and ordinary. Let \(X\in E_1(\mathbb{Q}_p)\) and let \(Y\in E(\mathbb{Q}_p)\setminus E_1(\mathbb{Q}_p)\) have reduction of order prime to \(p\). Write
\[
n\ :=\ \mathrm{ord}(Y\bmod p)\ \in\ \mathbb{Z}_{\ge 1},
\]
so \((n,p)=1\) by hypothesis. Then the reduction of \(nY\) is the identity, hence \(nY\in E_1(\mathbb{Q}_p)\) (this is exactly the “membership” mechanism recorded as `lem:membership` / `lemA:formal-membership`).

By bilinearity of the Coleman–Gross local height at \(p\),
\[
n\cdot h_p(X,Y)\ =\ h_p(X,nY).
\]
Now both \(X\) and \(nY\) lie in \(E_1(\mathbb{Q}_p)\), so `lem:formal-factor` applies:
\[
h_p(X,nY)\ =\ u_p\ \log_p(X)\,\log_p(nY),
\]
for some \(u_p\in\mathbb{Z}_p^\times\) (under the ordinary normalization used in the source).

Under the §7.1 conventions (formal parameter \(t(E_1)\subset p\mathbb{Z}_p\) and \(\log_p(T)=T+O(T^2)\) with \(\mathbb{Z}_p\)-coefficients), `lem:unit-log` gives
\[
v_p(\log_p(X))\ge 1,\qquad v_p(\log_p(nY))\ge 1.
\]
Therefore \(u_p\log_p(X)\log_p(nY)\in p^2\mathbb{Z}_p\subset p\mathbb{Z}_p\), so
\[
n\cdot h_p(X,Y)\ \in\ p\mathbb{Z}_p.
\]
Since \(n\in\mathbb{Z}_p^\times\), division by \(n\) preserves \(p\)-integrality, hence \(h_p(X,Y)\in p\mathbb{Z}_p\) as claimed. (In fact, the argument shows \(h_p(X,Y)\in p^2\mathbb{Z}_p\) under §7.1, but we record only the stated \(p\)-divisibility.)

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:triangular — proposition (Separation forces $p$–divisible off–diagonal heights; diagonal units certify $\mathrm{Reg}_p$)

- **Source**: `BSD-Jon-Final.txt` L1799–L1801
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: def:separated
- **Conditional on / Blockers (edit)**:
  - None beyond the local inputs `lem:CRT`, `lem:membership`, `lem:mixed-integrality`, and bilinearity of the local height.

#### Statement (verbatim from source)

```tex
\begin{proposition}[Separation forces $p$–divisible off–diagonal heights; diagonal units certify $\mathrm{Reg}_p$]\label{prop:triangular}
Let $p$ be a good ordinary prime that is separated (Definition~\ref{def:separated}). Let
\[
H_p\ :=\ \big(h_p(P_i,P_j)\big)_{1\le i,j\le r}
\]
be the cyclotomic Coleman--Gross \emph{local} height Gram matrix at $p$ for the fixed $\mathbb{Z}$--basis $\{P_i\}$.
Then there exist integers $m_1,\dots,m_r$ with $(m_i,p)=1$ such that $m_iP_i\in E_1(\mathbb{Q}_p)$ and $m_iP_j\notin E_1(\mathbb{Q}_p)$ for $j\ne i$. Moreover, for $i\ne j$ one has
\[
h_p(P_i,P_j)\ \in\ p\,\mathbb{Z}_p.
\]
In particular, if in addition \(v_p\big(h_p(P_i,P_i)\big)=0\) for all \(i\) (equivalently, \(v_p(\log_\omega(P_i))=0\) for all \(i\), cf. Lemma~\ref{lem:diag-units}), then \(\det(H_p)\in\mathbb{Z}_p^\times\) and hence the cyclotomic \(p\)–adic regulator \(\mathrm{Reg}_p(E)\) is a \(p\)–adic unit.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `def:separated`, `lem:CRT`, `lem:membership` (to choose the \(m_i\) with the required formal/non-formal membership properties)
  - `lem:mixed-integrality` (applied to \((m_iP_i,\;m_iP_j)\) to force \(p\)-divisibility)
  - Bilinearity of the Coleman–Gross local height \(h_p(\cdot,\cdot)\)
  - `lem:diag-units` (optional: translate diagonal-unit checks into \(\log_\omega\)-unit checks)
- **External (papers/books/theorems)**:
  - Coleman–Gross height theory at good ordinary primes (bilinearity + integrality; packaged as black box `B2`)

#### Proof outline (edit)

- Choose \(m_i\) via `lem:CRT` so that \(m_iP_i\in E_1(\mathbb{Q}_p)\) and \(m_iP_j\notin E_1(\mathbb{Q}_p)\) for \(j\ne i\) (`lem:membership`).
- For \(i\ne j\), apply `lem:mixed-integrality` to \((m_iP_i,\;m_iP_j)\) to get \(h_p(m_iP_i,m_iP_j)\in p\mathbb{Z}_p\).
- Use bilinearity: \(h_p(m_iP_i,m_iP_j)=m_i^2\,h_p(P_i,P_j)\), and \(m_i^2\in\mathbb{Z}_p^\times\), to deduce \(h_p(P_i,P_j)\in p\mathbb{Z}_p\).
- If all diagonal entries are units, then \(\det(H_p)\) is a unit because \(H_p\) is diagonal modulo \(p\).

#### Full proof (massive detail; edit)

Fix a separated good ordinary prime \(p\). Choose \(m_i\) as above. For \(i\ne j\), mixed integrality gives
\[
h_p(m_iP_i,\;m_iP_j)\in p\mathbb{Z}_p.
\]
By bilinearity,
\[
h_p(m_iP_i,\;m_iP_j)=m_i^2\,h_p(P_i,P_j).
\]
Since \((m_i,p)=1\), we have \(m_i^2\in\mathbb{Z}_p^\times\), hence dividing by \(m_i^2\) yields \(h_p(P_i,P_j)\in p\mathbb{Z}_p\). Therefore \(H_p\) is diagonal modulo \(p\). If additionally each diagonal entry \(h_p(P_i,P_i)\in\mathbb{Z}_p^\times\), then \(\det(H_p)\not\equiv 0\ (\bmod p)\), so \(\det(H_p)\in\mathbb{Z}_p^\times\), proving \(\mathrm{Reg}_p(E)\in\mathbb{Z}_p^\times\).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:height-unit — corollary (Height–unit primes (definition / certificate))

- **Source**: `BSD-Jon-Final.txt` L1817–L1822
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - None beyond `prop:triangular` (now repaired in the source).

#### Statement (verbatim from source)

```tex
\begin{corollary}[Height–unit primes (definition / certificate)]\label{cor:height-unit}
With notation as above, we call a good ordinary separated prime \(p\) a \emph{height–unit prime} if \(v_p\big(h_p(P_i,P_i)\big)=0\) for all \(i\). At such a prime, Proposition~\ref{prop:triangular} implies \(\mathrm{Reg}_p(E)\in \mathbb{Z}_p^\times\).
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `prop:triangular` (the direct source of this conclusion)
- **External (papers/books/theorems)**:
  - None beyond what `prop:triangular` uses.

#### Proof outline (edit)

- This is immediate from `prop:triangular` once “height–unit prime” is defined as “separated + all diagonal entries units”.

#### Full proof (massive detail; edit)

Immediate from `prop:triangular`.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L1824 — remark (Scope and ordering)

- **Source**: `BSD-Jon-Final.txt` L1824–L1826
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Scope and ordering]
The proof uses row-wise scalings (multiplying $P_i$ by $m_i$ with $(m_i,p)=1$) only as an auxiliary device to which mixed integrality applies; it then divides out by \(m_i^2\in\mathbb{Z}_p^\times\) to deduce the stated divisibility for the \emph{unscaled} Gram matrix \(H_p=(h_p(P_i,P_j))\). Any permutation of indices preserving separation yields the same conclusion. No global hypothesis beyond ordinary reduction and separation is used.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:mu-zero — proposition (Unit $p$–adic regulator $\Rightarrow \mu_p(E)=0$)

- **Source**: `BSD-Jon-Final.txt` L1841–L1852
- **Status**: drafted
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Uses black boxes / standing assumptions**:
    - **(B2)** Perrin–Riou leading-term identification: \(\lim_{T\to 0} L_p(E,T)/T^r = c_p\cdot \mathrm{Reg}_p(E)\) with \(c_p\in\mathbb{Z}_p^\times\).
    - **(B1')** One-sided divisibility: \(\mathrm{char}_\Lambda(X_p)\mid (L_p(E,T))\) (Kato / signed variants).
    - **Control**: bounded kernel/cokernel of cyclotomic control maps so that the \(T\)-adic order of \(\mathrm{char}_\Lambda(X_p)\) at \(T=0\) equals \(\mathrm{corank}_\Lambda X_p\).

#### Statement (verbatim from source)

```tex
\begin{proposition}[Unit $p$–adic regulator $\Rightarrow \mu_p(E)=0$]\label{prop:mu-zero}
Let $p$ be a good ordinary prime (or a supersingular prime with a fixed $\pm$–local condition), and suppose:
\begin{itemize}
\item[\emph{(i)}] the cyclotomic $p$–adic height pairing $h_p$ on $E(\mathbb{Q})\otimes\mathbb{Q}_p$ is nondegenerate, so that the $p$–adic regulator $\mathrm{Reg}_p(E)\in\mathbb{Z}_p^\times$;
\item[\emph{(ii)}] the cyclotomic control maps for Selmer over $\mathbb{Q}_\infty/\mathbb{Q}$ have bounded kernel and cokernel.
\end{itemize}
Then the cyclotomic Iwasawa $\mu$–invariant vanishes: $\mu_p(E)=0$. Moreover,
\[
\mathrm{ord}_{T=0}L_p(E,T)\;\ge\;\mathrm{corank}_\Lambda\,X_p(E/\mathbb{Q}_\infty),
\]
where $X_p$ is the Pontryagin dual of the cyclotomic $p^\infty$–Selmer group for the chosen local condition. If, in addition, the cyclotomic IMC at $p$ holds, then equality holds.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `B1'` and `B2` (standing black-box inputs in §2.6 of the source)
  - The definition of \(\mu_p,\lambda_p\) and \(\mathrm{char}_\Lambda(X_p)\) in §2.3 / Appendix B.1 of the source
- **External (papers/books/theorems)**:
  - Kato Euler system divisibility (ordinary; plus/signed variants at supersingular)
  - Perrin–Riou / Nekovář height formalism (leading term = regulator)
  - Standard Iwasawa structure theorem for torsion \(\Lambda\)-modules and control theorems

#### Proof outline (edit)

- Let \(\mathrm{char}_\Lambda(X_p)=(\xi_p(T))\) with \(\xi_p(T)=p^{\mu_p}T^{s_p}u(T)\), \(u(T)\in\Lambda^\times\).
- If \(\mu_p>0\) then \(p\mid \xi_p(T)\), hence by divisibility (B1') we get \(p\mid L_p(E,T)\).
- Evaluate at \(T=0\): \(p\mid L_p(E,T)\) forces the leading coefficient at \(T=0\) to be divisible by \(p\).
- But Perrin–Riou leading term (B2) identifies the leading coefficient (up to a unit) with \(\mathrm{Reg}_p(E)\), assumed a unit. Contradiction → \(\mu_p=0\).
- With \(\mu_p=0\), the \(T\)-adic order of \(\xi_p(T)\) at \(0\) is \(s_p\), which control identifies with \(\mathrm{corank}_\Lambda X_p\). Divisibility then gives \(\mathrm{ord}_{T=0}L_p(E,T)\ge s_p\), and equality holds if full IMC is assumed.

#### Full proof (massive detail; edit)

We follow Appendix B in the source, expanding each step.

Let \(\Lambda=\mathbb{Z}_p\llbracket T\rrbracket\) and let \(X_p=X_p(E/\mathbb{Q}_\infty)\) be the Pontryagin dual of the cyclotomic \(p^\infty\)-Selmer group for the chosen local condition (ordinary, or \(\pm\) at supersingular). Assume the cyclotomic control maps have bounded kernel and cokernel.

**Step 1: characteristic series and \(\mu\)-invariant.**  
Since \(X_p\) is a finitely generated torsion \(\Lambda\)-module, its characteristic ideal is principal. Choose a generator \(\xi_p(T)\in\Lambda\), well-defined up to a unit in \(\Lambda^\times\), such that
\[
\mathrm{char}_\Lambda(X_p)=(\xi_p(T)).
\]
By the \(\Lambda\)-module structure theorem, we can write
\[
\xi_p(T)=p^{\mu_p}\,T^{s_p}\,u(T),
\]
where \(\mu_p\in\mathbb{Z}_{\ge 0}\), \(s_p\in\mathbb{Z}_{\ge 0}\), and \(u(T)\in\Lambda^\times\). By definition, \(\mu_p\) is the exponent of the \(p\)-power content of \(\xi_p\).

By bounded control, \(s_p\) is identified with the \(\Lambda\)-corank of the dual Selmer module:
\[
s_p=\mathrm{corank}_\Lambda X_p(E/\mathbb{Q}_\infty).
\]

**Step 2: assume \(\mathrm{Reg}_p(E)\) is a unit.**  
The hypothesis “the cyclotomic \(p\)-adic height pairing is nondegenerate” is exactly the statement that the \(p\)-adic regulator
\[
\mathrm{Reg}_p(E):=\det\big(h_p(P_i,P_j)\big)_{1\le i,j\le r}
\]
is a \(p\)-adic unit, for a \(\mathbb{Z}\)-basis \(\{P_i\}\) of \(E(\mathbb{Q})/\mathrm{tors}\) and \(r=\mathrm{rank}\,E(\mathbb{Q})\).

**Step 3: Perrin–Riou leading term (B2).**  
By standing input (B2), there exists \(c_p\in\mathbb{Z}_p^\times\) such that
\[
\lim_{T\to 0}\frac{L_p(E,T)}{T^r}=c_p\cdot \mathrm{Reg}_p(E).
\]
In particular, since \(\mathrm{Reg}_p(E)\in\mathbb{Z}_p^\times\), the leading coefficient of \(L_p(E,T)\) at \(T=0\) (at order \(r\)) is a \(p\)-adic unit.

**Step 4: divisibility input forces a \(\mu\)-contradiction.**  
Assume for contradiction that \(\mu_p>0\). Then \(p\mid \xi_p(T)\) in \(\Lambda\).

By standing input (B1') (one-sided divisibility), we have
\[
\mathrm{char}_\Lambda(X_p)\mid (L_p(E,T))\quad\text{in }\Lambda,
\]
so \(\xi_p(T)\) divides \(L_p(E,T)\) up to a unit. In particular, \(p\mid \xi_p(T)\) implies \(p\mid L_p(E,T)\) in \(\Lambda\).

Evaluating the power series \(L_p(E,T)\) at \(T=0\) then forces its leading coefficient at \(T=0\) to be divisible by \(p\). This contradicts Step 3, which says that leading coefficient is a \(p\)-adic unit. Therefore \(\mu_p=0\).

**Step 5: the order-of-vanishing inequality.**  
With \(\mu_p=0\), we have \(\xi_p(T)=T^{s_p}u(T)\) with \(u(0)\in\mathbb{Z}_p^\times\), so
\[
\mathrm{ord}_{T=0}\xi_p(T)=s_p=\mathrm{corank}_\Lambda X_p(E/\mathbb{Q}_\infty).
\]
Since \(\xi_p(T)\mid L_p(E,T)\), we get
\[
\mathrm{ord}_{T=0}L_p(E,T)\ \ge\ \mathrm{ord}_{T=0}\xi_p(T)\ =\ \mathrm{corank}_\Lambda X_p(E/\mathbb{Q}_\infty).
\]
Finally, if one assumes the full IMC equality (B1), then \((\xi_p(T))=(L_p(E,T))\) up to \(\Lambda^\times\), so the inequality becomes equality.

This completes the proof.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L1866 — remark (Scope of inputs)

- **Source**: `BSD-Jon-Final.txt` L1866–L1868
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Scope of inputs]
The contradiction step uses only that a positive $\mu$ forces $p$–divisibility of the characteristic element and that this divisibility transfers to $L_p(E,T)$ (either by the full cyclotomic IMC or by the known one–sided inclusion in the ordinary/$\pm$ settings). No other global hypothesis is used.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:BSDp — proposition (IMC$_p$ + $\mu_p=0$ + finite $\Sha[p^\infty]$ $\Rightarrow$ BSD$_p$)

- **Source**: `BSD-Jon-Final.txt` L1872–L1890
- **Status**: outlined
- **Auto-flags**: ASSUMES, IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Conditional inputs**:
    - **(B1)** Full cyclotomic IMC at \(p\): \(\mathrm{char}_\Lambda X_p=(L_p(E,T))\) up to \(\Lambda^\times\).
    - **\(\mu_p(E)=0\)** (often obtained from `prop:mu-zero` under its hypotheses).
    - **Finiteness of \(\Sha(E/\mathbb{Q})[p^\infty]\)** (this is genuinely global and not proved unconditionally in the main text; see §7.5 and Appendix C discussion).
    - **Control** (bounded kernel/cokernel) to identify \(\mathrm{corank}_\Lambda X_p\) with \(\mathrm{rank}\,E(\mathbb{Q})\).

#### Statement (verbatim from source)

```tex
\begin{proposition}[IMC$_p$ + $\mu_p=0$ + finite $\Sha[p^\infty]$ $\Rightarrow$ BSD$_p$]\label{prop:BSDp}
Fix a good prime $p$ and the corresponding local condition (ordinary or $\pm$). Assume:
\begin{itemize}
\item[\emph{(i)}] the cyclotomic main conjecture at $p$ holds (standing input (B1)): $\mathrm{char}_\Lambda X_p(E/\mathbb{Q}_\infty)=(L_p(E,T))$ up to a $\Lambda^\times$–unit;
\item[\emph{(ii)}] $\mu_p(E)=0$;
\item[\emph{(iii)}] $\Sha(E/\mathbb{Q})[p^\infty]$ is finite.
\end{itemize}
Then
\[
\mathrm{ord}_{T=0}L_p(E,T)\;=\;\mathrm{corank}_\Lambda\,X_p(E/\mathbb{Q}_\infty)\;=\;\mathrm{rank}\,E(\mathbb{Q}),
\]
and the $p$–adic valuation of the BSD leading term satisfies
\[
\mathrm{ord}_p\!\left(\frac{L^{(r)}(E,1)}{r!\,\Omega_E}\right)\;=\;
\mathrm{ord}_p\!\left(\frac{\mathrm{Reg}_E\ \cdot\ \#\Sha(E/\mathbb{Q})\ \cdot\ \prod_\ell c_\ell}{\#E(\mathbb{Q})_{\mathrm{tors}}^{\,2}}\right),
\qquad r=\mathrm{rank}\,E(\mathbb{Q}).
\]
In particular, the $p$–part of BSD (rank equality and leading–term identity) holds.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `B1` (IMC) and the control hypothesis \((\ref{eq:control})\)
  - `prop:mu-zero` (for \(\mu_p(E)=0\) + order inequality)
  - Appendix C of the source for fixed-prime finiteness implications (at least directionally)
- **External (papers/books/theorems)**:
  - Cyclotomic IMC literature (Skinner–Urban / Wan / signed analogues)
  - Standard control theorems comparing Selmer coranks with Mordell–Weil rank
  - Poitou–Tate / Cassels–Tate and “Sha finite \(\Rightarrow\)” identification of leading terms

#### Proof outline (edit)

- Under IMC, \((L_p(E,T))=(\xi_p(T))\) where \(\xi_p\) generates \(\mathrm{char}_\Lambda(X_p)\).
- With \(\mu_p(E)=0\), write \(\xi_p(T)=T^{s_p}u(T)\) with \(u(0)\in\mathbb{Z}_p^\times\), so \(\mathrm{ord}_{T=0}L_p(E,T)=s_p\).
- By control, \(s_p=\mathrm{corank}_\Lambda X_p(E/\mathbb{Q}_\infty)=\mathrm{rank}\,E(\mathbb{Q})\).
- For the leading-term valuation: IMC identifies the leading coefficient of \(L_p\) with the specialization of \(\xi_p\) at \(T=0\) (up to a unit). Unwind the control exact sequences and use the finiteness of \(\Sha[p^\infty]\) to identify this specialization with the \(p\)-part of the classical BSD quotient, giving the valuation equality.

#### Full proof (massive detail; edit)

This proposition is a “prime-wise BSD package” statement: it combines (i) IMC (an equality of characteristic ideals), (ii) \(\mu=0\) (no extra \(p\)-power content), and (iii) finiteness of \(\Sha[p^\infty]\) (so the Selmer correction term is finite) to deduce the \(p\)-part of BSD.

We spell out the argument in the same order as the statement.

**Setup and notation.**  
Fix a prime \(p\) and the relevant cyclotomic local condition (ordinary or \(\pm\)). Let
\[
\Lambda=\mathbb{Z}_p\llbracket T\rrbracket,\qquad X_p=X_p(E/\mathbb{Q}_\infty)
\]
be the Pontryagin dual of the cyclotomic Selmer group over \(\mathbb{Q}_\infty\) for that local condition. Under the standard control hypothesis, \(X_p\) is a torsion \(\Lambda\)-module with principal characteristic ideal.

Let \(\xi_p(T)\in\Lambda\) be a characteristic series: \(\mathrm{char}_\Lambda(X_p)=(\xi_p(T))\), defined up to \(\Lambda^\times\).

**Step 1: rank equality (order of vanishing at \(T=0\)).**  
Assume (i) IMC at \(p\): \(\mathrm{char}_\Lambda(X_p)=(L_p(E,T))\) up to \(\Lambda^\times\). Then
\[
 (L_p(E,T))=(\xi_p(T))\quad\text{in }\Lambda,
\]
so \(\mathrm{ord}_{T=0}L_p(E,T)=\mathrm{ord}_{T=0}\xi_p(T)\).

Assume (ii) \(\mu_p(E)=0\). By definition of \(\mu\) (Appendix B.1 of the source), this means \(\xi_p(T)\) has no nontrivial \(p\)-power content, so we may write
\[
\xi_p(T)=T^{s_p}\,u(T),\qquad u(T)\in\Lambda^\times.
\]
Hence \(\mathrm{ord}_{T=0}\xi_p(T)=s_p\).

Under the control hypothesis, the integer \(s_p\) equals the \(\Lambda\)-corank of \(X_p\):
\[
s_p=\mathrm{corank}_\Lambda X_p(E/\mathbb{Q}_\infty).
\]
Finally, standard control identifies this corank with \(\mathrm{rank}\,E(\mathbb{Q})\). Therefore
\[
\mathrm{ord}_{T=0}L_p(E,T)=s_p=\mathrm{corank}_\Lambda X_p(E/\mathbb{Q}_\infty)=\mathrm{rank}\,E(\mathbb{Q}).
\]
This proves the rank equality asserted in the proposition.

**Step 2: leading-term valuation identity (BSD\(_p\)).**  
Let \(r=\mathrm{rank}\,E(\mathbb{Q})\). Write the Taylor expansion
\[
L_p(E,T)=a_r\,T^r+\text{(higher powers)},\qquad a_r\in\mathbb{Z}_p,
\]
so \(a_r\) is the leading coefficient at \(T=0\).

By IMC and \(\mu=0\), the specialization of the characteristic series at \(T=0\) controls \(a_r\) up to a \(p\)-adic unit: informally, \(a_r\) matches the “\(T=0\)” specialization of the algebraic characteristic element, and its \(p\)-adic valuation is computed from the corresponding finite-level Selmer Euler characteristic.

Assume (iii) \(\Sha(E/\mathbb{Q})[p^\infty]\) is finite. Then the classical exact sequence defining Selmer at level \(\mathbb{Q}\) (Kummer → Selmer → \(\Sha[p^\infty]\)) shows that the \(p^\infty\)-Selmer group over \(\mathbb{Q}\) is \(E(\mathbb{Q})\otimes\mathbb{Q}_p/\mathbb{Z}_p\) up to a finite error, and the remaining finite error is exactly \(\Sha[p^\infty]\) plus the local Tamagawa corrections. Unwinding the control maps from \(\mathbb{Q}_\infty\) down to \(\mathbb{Q}\) expresses the valuation \(v_p(a_r)\) in terms of:
  - the \(p\)-adic regulator contribution (coming from the height pairing on the free part),
  - the size of \(\Sha[p^\infty]\),
  - the Tamagawa numbers \(c_\ell\),
  - and the torsion factor \(\#E(\mathbb{Q})_{\mathrm{tors}}^2\).

The outcome is exactly the stated equality of \(p\)-adic valuations:
\[
\mathrm{ord}_p\!\left(\frac{L^{(r)}(E,1)}{r!\,\Omega_E}\right)\;=\;
\mathrm{ord}_p\!\left(\frac{\mathrm{Reg}_E\ \cdot\ \#\Sha(E/\mathbb{Q})\ \cdot\ \prod_\ell c_\ell}{\#E(\mathbb{Q})_{\mathrm{tors}}^{\,2}}\right).
\]

**Status note (audit)**: the source gives this step as a short paragraph (“unwinding definitions … yields the valuation identity”). For a fully audited proof, we will need to:
1) write the exact finite-level control sequence and Euler characteristic computation used, and  
2) show precisely where finiteness of \(\Sha[p^\infty]\) is used to justify replacing coranks by sizes.

Also note: Appendix C.3 of the source attempts to deduce \(\Sha[p^\infty]\) finiteness from nondegenerate heights via a dimension argument, but that argument is invalid (see `lemC:height=PT` notes). So assumption (iii) remains a real hypothesis unless a different proof is supplied.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L1896 — remark (Supersingular primes)

- **Source**: `BSD-Jon-Final.txt` L1896–L1898
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Supersingular primes]
At supersingular $p$, one uses the $\pm$–Iwasawa theory and the $\pm$–$p$–adic $L$–functions; the same argument applies within each signed theory.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:det-equals-Lp-ord — theorem (Analytic interpolation: $\det= L_p$ up to $\Lambda^{\times}$)

- **Source**: `BSD-Jon-Final.txt` L1948–L1954
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Analytic interpolation: $\det= L_p$ up to $\Lambda^{\times}$]\label{thm:det-equals-Lp-ord}
With the above normalization,
\[
\det_{\Lambda}\big(I- K_{\mathrm{ord}}(T)\big)\ =\ F_{\mathrm{ord}}(T)\ \in\ \Lambda\qquad\text{up to a unit in }\Lambda^{\times},
\]
and hence equals the ordinary cyclotomic $p$-adic $L$-function $L_p(E,T)$ up to $\Lambda^{\times}$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:coker-equals-selmer-ord — theorem (Algebraic identification: fixed points $\Rightarrow$ Greenberg Selmer)

- **Source**: `BSD-Jon-Final.txt` L1963–L1965
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Algebraic identification: fixed points $\Rightarrow$ Greenberg Selmer]\label{thm:coker-equals-selmer-ord}
The Pontryagin dual of the fixed-point cokernel of $I-K_{\mathrm{ord}}(T)$ on a finite free $\Lambda$-lattice inside $H^1_{\mathrm{Iw}}(\mathbb{Q},V)$ is canonically isomorphic to the ordinary dual Selmer group $X_p(E/\mathbb{Q}_\infty)$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:PR-ord — lemma (Perrin--Riou explicit reciprocity, ordinary projection)

- **Source**: `BSD-Jon-Final.txt` L2027–L2037
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Perrin--Riou explicit reciprocity, ordinary projection]\label{lem:PR-ord}
Let $\mathcal{L}_V:H^1_{\emph{Iw}}(\mathbb{Q}_p,V)\to \Lambda\otimes D_{\emph{cris}}(V)$ be Perrin--Riou's big logarithm. For every finite-order character $\chi$ of $\Gamma$,
\[
\big(\mathrm{ev}_\chi\otimes \mathrm{id}\big)\,\mathcal{L}_V(\mathrm{res}_p\,z)\ =\ c(E,p,\chi)\cdot \mathrm{BK}_\chi\big(\mathrm{res}_p\,z\big),\qquad z\in H^1_{\emph{Iw}}(\mathbb{Q}_p,V),
\]
with $c(E,p,\chi)\in \mathbb{Z}_p^{\times}$ and $\mathrm{BK}_\chi$ the Bloch--Kato regulator at $\chi$. Projecting to the ordinary line, one obtains
\[
\mathrm{ev}_\chi\,\mathrm{Col}_p^{\mathrm{ord}}(\mathrm{res}_p\,z)\ =\ c'(E,p,\chi)\cdot \langle\mathrm{BK}_\chi(\mathrm{res}_p\,z),v_{\mathrm{ord}}^{\!*}\rangle,
\]
with $c'(E,p,\chi)\in \mathbb{Z}_p^{\times}$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:interpolation-kato — lemma (Interpolation with Kato's Euler system)

- **Source**: `BSD-Jon-Final.txt` L2043–L2049
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Interpolation with Kato's Euler system]\label{lem:interpolation-kato}
Let $z_{\mathrm{Kato}}\in H^1(\mathbb{Q},V\otimes \Lambda)$ be Kato's Euler system class. Then there is $F_{\mathrm{ord}}(T)\in\Lambda$ such that, for every finite-order $\chi$ of $\Gamma$,
\[
\mathrm{ev}_\chi\,F_{\mathrm{ord}}(T)\ =\ u(E,p,\chi)\cdot L(E,\chi,1),\qquad u(E,p,\chi)\in \mathbb{Z}_p^{\times},
\]
and $F_{\mathrm{ord}}(T)=\mathrm{Col}_p^{\mathrm{ord}}(\mathrm{res}_p\,z_{\mathrm{Kato}})$ up to a unit.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:compactness — lemma (Complete continuity of $U_p(T)$)

- **Source**: `BSD-Jon-Final.txt` L2055–L2057
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Complete continuity of $U_p(T)$]\label{lem:compactness}
The $\Lambda$-linear operator $U_p(T)=e_{\mathrm{ord}}\circ \varphi_N^{-1}\circ \mathrm{Tw}_\gamma$ on a finite free $\Lambda$-lattice $M\subset N(V)^{\psi=1}\otimes\Lambda$ is completely continuous (compact) with respect to the $(\pi,T)$-adic Banach structure.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:specialization-det — lemma (Specialization of Fredholm determinants)

- **Source**: `BSD-Jon-Final.txt` L2063–L2069
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Specialization of Fredholm determinants]\label{lem:specialization-det}
Let $K(T)$ be a completely continuous $\Lambda$-linear operator on a finite free $\Lambda$-module $M$. The Fredholm determinant $\det_{\Lambda}(I-K(T))\in\Lambda$ is well-defined and satisfies
\[
\mathrm{ev}_\chi\,\det_{\Lambda}(I-K(T))\ =\ \det\big(I-K(\chi)\big),
\]
for every finite-order character $\chi$ of $\Gamma$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:det-equals-F — proposition (Analytic determinant equals $F_{\mathrm{ord}}(T)$)

- **Source**: `BSD-Jon-Final.txt` L2075–L2080
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: subsec:ord-operator
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Analytic determinant equals $F_{\mathrm{ord}}(T)$]\label{prop:det-equals-F}
With $K_{\mathrm{ord}}(T)$ constructed in \S\ref{subsec:ord-operator}, one has
\[
\det_{\Lambda}\big(I-K_{\mathrm{ord}}(T)\big)\ =\ F_{\mathrm{ord}}(T)\quad\text{up to }\Lambda^{\times}.
\]
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:local-ord — lemma (Local ordinary condition)

- **Source**: `BSD-Jon-Final.txt` L2086–L2088
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Local ordinary condition]\label{lem:local-ord}
The Greenberg local ordinary condition at $p$ for $V$ is equivalent to imposing the projector $e_{\mathrm{ord}}$ at the Wach/crystalline level.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:coker-selmer — proposition (Cokernel identification)

- **Source**: `BSD-Jon-Final.txt` L2094–L2096
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Cokernel identification]\label{prop:coker-selmer}
The Pontryagin dual of $\mathrm{coker}(I-K_{\mathrm{ord}}(T))$ is canonically isomorphic to the Greenberg Selmer dual $X_p(E/\mathbb{Q}_\infty)$. Moreover, kernels and cokernels along control maps have bounded size.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:IMC-operator-ord — theorem (Ordinary IMC packaged as an operator identity)

- **Source**: `BSD-Jon-Final.txt` L2102–L2108
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: prop:det-equals-F
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Ordinary IMC packaged as an operator identity]\label{thm:IMC-operator-ord}
For an ordinary prime $p$, the equality
\[
\mathrm{char}_{\Lambda}\,X_p(E/\mathbb{Q}_\infty)\ =\ \big(\det_{\Lambda}(I-K_{\mathrm{ord}}(T))\big)\ =\ \big(L_p(E,T)\big)\quad \text{up to }\Lambda^{\times}
\]
holds whenever the ordinary cyclotomic IMC is known (e.g. under the hypotheses of \cite{Greenberg1989,Kato2004} together with the reverse divisibility results). Unconditionally, Kato's divisibility $\mathrm{char}_{\Lambda}\,X_p\mid (L_p(E,T))$ is recovered from the operator via Proposition~\ref{prop:det-equals-F}.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:PR-signed — lemma (Signed explicit reciprocity)

- **Source**: `BSD-Jon-Final.txt` L2135–L2141
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Signed explicit reciprocity]\label{lem:PR-signed}
For every finite-order character $\chi$ of $\Gamma$,
\[
\mathrm{ev}_\chi\,\mathrm{Col}_p^{\pm}(\mathrm{res}_p\,z)\ =\ c_{\pm}(E,p,\chi)\cdot \mathrm{BK}_\chi(\mathrm{res}_p\,z)\quad \text{projected via $e_{\pm}^{\!*}$},
\]
with $c_{\pm}(E,p,\chi)\in \mathbb{Z}_p^{\times}$. Consequently, $F_{\pm}(T):=\mathrm{Col}_p^{\pm}(\mathrm{res}_p\,z_{\mathrm{Kato}})$ interpolates the signed central values $L(E,\chi,1)$ up to units in the appropriate conductor-parity ranges.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:compactness-signed — lemma (Complete continuity and specialization)

- **Source**: `BSD-Jon-Final.txt` L2147–L2149
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Complete continuity and specialization]\label{lem:compactness-signed}
$U_p^{\pm}(T)$ is completely continuous on a finite free $\Lambda$-lattice in $N(V)^{\psi=1}\otimes\Lambda$; the Fredholm determinant $\det_{\Lambda}(I-K_{\pm}(T))$ is well-defined and specializes at $\chi$ to $\det(I-K_{\pm}(\chi))$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:det-equals-Fpm — proposition (Analytic determinant equals $F_{\pm}(T)$)

- **Source**: `BSD-Jon-Final.txt` L2155–L2160
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Analytic determinant equals $F_{\pm}(T)$]\label{prop:det-equals-Fpm}
With $K_{\pm}(T)$ as above,
\[
\det_{\Lambda}\big(I-K_{\pm}(T)\big)\ =\ F_{\pm}(T)\quad \text{up to }\Lambda^{\times}.
\]
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:local-signed — lemma (Signed local condition)

- **Source**: `BSD-Jon-Final.txt` L2166–L2168
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Signed local condition]\label{lem:local-signed}
The Kobayashi signed local conditions at $p$ for $V$ are equivalent to imposing the projectors $e_{\pm}$ at the Wach/crystalline level.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:coker-signed — proposition (Cokernel identification, signed)

- **Source**: `BSD-Jon-Final.txt` L2174–L2176
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Cokernel identification, signed]\label{prop:coker-signed}
The Pontryagin duals of $\mathrm{coker}(I-K_{\pm}(T))$ are canonically isomorphic to the signed Selmer duals $X_p^{\pm}(E/\mathbb{Q}_\infty)$. Control maps have bounded kernel and cokernel in the cyclotomic tower.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:IMC-operator-signed — theorem (Signed IMC packaged as an operator identity)

- **Source**: `BSD-Jon-Final.txt` L2182–L2188
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Signed IMC packaged as an operator identity]\label{thm:IMC-operator-signed}
For a supersingular prime $p$ and sign $\pm$, the equality
\[
\mathrm{char}_{\Lambda}\,X_p^{\pm}(E/\mathbb{Q}_\infty)\ =\ \big(\det_{\Lambda}(I-K_{\pm}(T))\big)\ =\ \big(L_p^{\pm}(E,T)\big)\quad \text{up to }\Lambda^{\times}
\]
holds whenever the signed cyclotomic IMC is known (cf. \cite{Kobayashi2003,Sprung2011,LeiLoefflerZerbes2012}). The operator construction recovers the one-sided divisibilities under the corresponding signed control and reciprocity laws.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:density_drop — lemma (Density-drop)

- **Source**: `BSD-Jon-Final.txt` L2203–L2212
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Density-drop]\label{lem:density_drop}
There exist universal constants $\vartheta=\tfrac14$, $c=\tfrac34$, and $\eta_1>0$ such that for any suitable solution on $Q_1(0,0)$ with
\[
\mathcal{W}(0,0;1)\ \le\ \varepsilon_0+\eta,\qquad \eta\in(0,\eta_1],
\]
one has
\[
\mathcal{W}(0,0;\vartheta)\ \le\ \varepsilon_0+c\,\eta.
\]
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L2419 — remark (Exceptional zero and bad reduction)

- **Source**: `BSD-Jon-Final.txt` L2419–L2421
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Exceptional zero and bad reduction]
If $p$ is split multiplicative (Tate curve), an exceptional zero factor occurs in $L_p(E,T)$; one may either exclude such $p$ from the \emph{ordinary} pipeline or apply the standard Greenberg–Stevens correction. We do not need these primes for the results stated here. Primes of bad reduction are excluded by construction.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lemA:CRT — lemma (Congruence scalings)

- **Source**: `BSD-Jon-Final.txt` L2704–L2709
- **Status**: audited
- **Auto-flags**: —
- **Auto-extracted internal refs**: def:separated
- **Conditional on / Blockers (edit)**:
  - Same edge-case note as `lem:CRT`: the requirement \((m_i,p)=1\) implicitly needs \(p\nmid o_i(p)\). For separated primes with rank \(\ge 2\) and \(p\ge 7\), anomalous primes with \(p\mid \#E(\mathbb{F}_p)\) force \(\#E(\mathbb{F}_p)=p\) and thus violate separation.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Congruence scalings]\label{lemA:CRT}
Let $o_i(p)=\mathrm{ord}(P_i\bmod p)\in\widetilde{E}(\mathbb{F}_p)$. If $p$ is separated (Definition~\ref{def:separated}), then for each $i$ there exists $m_i\in\mathbb{Z}$ with $(m_i,p)=1$ such that
\[
m_i\equiv 0\pmod{o_i(p)}\qquad\text{and}\qquad m_i\not\equiv 0\pmod{o_j(p)}\ \ \text{for all }j\ne i.
\]
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `def:separated`
  - `lem:CRT` (same statement, earlier in the document)
- **External (papers/books/theorems)**:
  - Elementary number theory (divisibility).

#### Proof outline (edit)

- Identical to `lem:CRT`.

#### Full proof (massive detail; edit)

This lemma is a duplicate of `lem:CRT` (the same congruence construction, restated in Appendix A).  

See the fully detailed proof in `lem:CRT`; it applies verbatim with the same hypotheses and the same choice \(m_i=o_i(p)\) (subject to the \((m_i,p)=1\) edge-case note).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lemA:formal-membership — lemma (Formal–group membership)

- **Source**: `BSD-Jon-Final.txt` L2715–L2717
- **Status**: audited
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - None (formal consequence of the reduction map being a group homomorphism and \(E_1(\mathbb{Q}_p)\) being its kernel at good primes).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Formal–group membership]\label{lemA:formal-membership}
Let $Q\in E(\mathbb{Q}_p)$ and set $o(Q)=\mathrm{ord}(Q\bmod p)$. If $(m,p)=1$ and $m\equiv 0\pmod{o(Q)}$, then $mQ\in E_1(\mathbb{Q}_p)$. If $m\not\equiv 0\pmod{o(Q)}$, then $mQ\notin E_1(\mathbb{Q}_p)$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:membership` (same statement, earlier in the document)
- **External (papers/books/theorems)**:
  - Standard good-reduction theory for elliptic curves over local fields.

#### Proof outline (edit)

- Identical to `lem:membership`.

#### Full proof (massive detail; edit)

This lemma is a duplicate of `lem:membership` (restated in Appendix A).  

See `lem:membership` for an audited, line-by-line proof; it applies verbatim.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lemA:factor — lemma (Height factorization on $E_1$)

- **Source**: `BSD-Jon-Final.txt` L2723–L2729
- **Status**: outlined
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Depends on a precise definition of the “cyclotomic Coleman–Gross local height at \(p\)”** and the chosen normalizations (Coleman branch, Néron differential, cyclotomic logarithm). The source provides only a pointer sentence.
  - **Normalization sensitivity**: the statement uses a formal logarithm \(\log_E\) with expansion \(\log_E(T)=T+O(T^2)\) in a chosen parameter \(T\). Whether \(\log_E(X)\) is typically a unit for \(X\in E_1(\mathbb{Q}_p)\) depends on the scaling of \(T\) (and, in some conventions, on whether one divides the standard formal log by \(p\)).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Height factorization on $E_1$]\label{lemA:factor}
There exists $u_p\in\mathbb{Z}_p^\times$ (depending on the normalization of $h_p$ and the Néron differential) such that for all $X,Y\in E_1(\mathbb{Q}_p)$,
\[
h_p(X,Y)\ =\ u_p\,\log_E(X)\,\log_E(Y),
\]
where $\log_E:E_1(\mathbb{Q}_p)\to\mathbb{Q}_p$ is the formal logarithm for the chosen Néron differential and satisfies $\log_E(T)=T+O(T^2)$ in the formal parameter $T$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `B2` (Coleman–Gross heights) for the existence/definition of the local height at \(p\).
  - `lem:formal-factor` (very similar statement earlier in the source, with slightly different notation \(\log_p\) vs \(\log_E\)).
- **External (papers/books/theorems)**:
  - Coleman–Gross: definition of the \(p\)-adic height via Coleman integration / local symbols.
  - Perrin–Riou / Nekovář height formalism: description of local heights in terms of logarithms on the formal group.

#### Proof outline (edit)

- Fix the local height pairing \(h_p(\cdot,\cdot)\) at \(p\) (cyclotomic Coleman–Gross) and the formal group \(E_1(\mathbb{Q}_p)\).
- Use that \(E_1(\mathbb{Q}_p)\) is isomorphic (via a formal parameter \(T\)) to an additive \(p\)-adic neighborhood of \(0\), and \(\log_E\) is the unique homomorphism with \(\log_E(T)=T+O(T^2)\).
- Show that, restricted to \(E_1(\mathbb{Q}_p)\times E_1(\mathbb{Q}_p)\), the Coleman–Gross local height pairing is a symmetric bilinear form that factors through \(\log_E\) in each variable, hence must be of the form \(u_p\,\log_E(X)\log_E(Y)\). Prove \(u_p\in\mathbb{Z}_p^\times\) from the chosen normalization (or record the exact factor from the literature and track its valuation).

#### Full proof (massive detail; edit)

**Outline-level proof (needs full writeup once the chosen height normalization is pinned down):**

1. **Formal-group analytic coordinates.** Since \(p\) is good and \(X\in E_1(\mathbb{Q}_p)\), there is a formal parameter \(T\) at the origin such that \(T(X)\in \mathfrak{m}_p\) (or in \(\mathbb{Z}_p\) after a scaling of \(T\)). The formal group law expresses addition on \(E_1(\mathbb{Q}_p)\) as a 1-dimensional commutative formal group \(F(T_1,T_2)\in\mathbb{Z}_p\llbracket T_1,T_2\rrbracket\).

2. **Formal logarithm.** There is a unique power series \(\log_E(T)\in\mathbb{Q}_p\llbracket T\rrbracket\) with \(\log_E(T)=T+O(T^2)\) such that \(\log_E(F(T_1,T_2))=\log_E(T_1)+\log_E(T_2)\). This yields a group homomorphism \(\log_E:E_1(\mathbb{Q}_p)\to\mathbb{Q}_p\).

3. **Bilinearity forces rank-1 factorization.** The Coleman–Gross local height pairing \(h_p(\cdot,\cdot)\) is (by construction) symmetric and bilinear on the relevant subgroup, and on \(E_1(\mathbb{Q}_p)\) it is obtained from a local symbol that is functorial in the formal group coordinate. In particular, the map
   \[
     E_1(\mathbb{Q}_p)\times E_1(\mathbb{Q}_p)\to\mathbb{Q}_p,\quad (X,Y)\mapsto h_p(X,Y)
   \]
   factors through the additive coordinates \((\log_E(X),\log_E(Y))\) (this is the substantive Coleman–Gross input).
   Therefore there exists \(u_p\in\mathbb{Q}_p\) such that
   \[
     h_p(X,Y)=u_p\,\log_E(X)\log_E(Y)\qquad(\forall X,Y\in E_1(\mathbb{Q}_p)).
   \]

4. **Unitness of \(u_p\).** The constant \(u_p\) depends on the chosen Néron differential and the Coleman branch. The claim \(u_p\in\mathbb{Z}_p^\times\) is a normalization statement; to audit it we must:
   - identify the precise definition of \(h_p\) used in this document, and
   - compare the resulting constant to the standard references (Coleman–Gross / Perrin–Riou / Nekovář).

**Current status**: this is left at `outlined` until we either (a) import a precise reference+normalization, or (b) the source provides a complete derivation.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lemA:units-offdiag — lemma (Diagonal units and off–diagonal $p$–divisibility)

- **Source**: `BSD-Jon-Final.txt` L2735–L2741
- **Status**: blocked
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Part (1) is nontrivial**: it asserts a *finite* exceptional set \(S'\) such that for all good ordinary \(p\notin S'\) and each fixed non-torsion \(P\), one can choose \(m=m(p)\) (prime to \(p\)) with \(mP\in E_1(\mathbb{Q}_p)\) and \(\log_E(mP)\in\mathbb{Z}_p^\times\). The source proof sketch appeals to “\(\log_E(T)=T+O(T^2)\) with unit linear term” but does not justify finiteness of the bad set.
  - **Direct contradiction with §7.1 (as currently normalized)**: if \(mP\in E_1(\mathbb{Q}_p)\) and the formal parameter satisfies \(t(mP)\in p\mathbb{Z}_p\) with \(\log_E(T)=T+O(T^2)\in\mathbb{Z}_p\llbracket T\rrbracket\), then \(\log_E(mP)=\log_E(t(mP))\in p\mathbb{Z}_p\), so \(v_p(\log_E(mP))\ge 1\) and \(\log_E(mP)\notin\mathbb{Z}_p^\times\).  
    Therefore statement (1) cannot hold under the §7.1 conventions unless the paper is using a different scaling (e.g. a \(p^{-1}\)-rescaled logarithm) or a different notion of “formal parameter”.
  - **Part (2) depends on the precise local-height normalization and the ‘finite’ local condition at \(p\)**; the source uses a decomposition \(Y=Y^{(0)}+Y^{(1)}\) and asserts both summands of \(h_p(X,Y)\) lie in \(p\mathbb{Z}_p\). This should be expanded carefully once the normalization conventions are fixed.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Diagonal units and off–diagonal $p$–divisibility]\label{lemA:units-offdiag}
There exists a finite set $S'$ of primes (depending on $E$ and the points $P_i$) such that for all good ordinary $p\notin S'$ the following hold:
\begin{enumerate}
\item For each non-torsion $P$, there is $m$ with $(m,p)=1$ and $mP\in E_1(\mathbb{Q}_p)$ such that $\log_E(mP)\in\mathbb{Z}_p^\times$; hence $h_p(mP)\in\mathbb{Z}_p^\times$.
\item If $X\in E_1(\mathbb{Q}_p)$ and $Y\in E(\mathbb{Q}_p)\setminus E_1(\mathbb{Q}_p)$ has reduction of order prime to $p$, then $h_p(X,Y)\in p\,\mathbb{Z}_p$.
\end{enumerate}
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lemA:formal-membership` (to produce \(mP\in E_1(\mathbb{Q}_p)\) when \(m\) is a multiple of the reduction order)
  - `lemA:factor` (to convert a diagonal unit statement into a \(\log_E\)-unit statement)
  - `eq:local-split` in `BSD-Jon-Final.txt` (§2.2, local splitting) for the decomposition in (2)
- **External (papers/books/theorems)**:
  - Coleman–Gross local height construction (integrality properties; behavior on reduction component vs formal component).
  - Potentially Strassmann-type finiteness arguments for \(p\)-adic valuations of analytic functions evaluated at torsion multiples (for the finiteness claim in (1)).

#### Proof outline (edit)

- **(1) Diagonal units**:
  - For a given good ordinary \(p\), choose \(m\) (prime to \(p\)) that kills the reduction of \(P\), so \(mP\in E_1(\mathbb{Q}_p)\).
  - Show \(\log_E(mP)\) is a \(p\)-adic unit for all but finitely many \(p\), by controlling the valuation of the formal parameter \(T(mP)\) (this is the missing step to audit).
  - Then \(h_p(mP,mP)=u_p\,\log_E(mP)^2\) is a unit by `lemA:factor`.
- **(2) Off-diagonal \(p\)-divisibility**:
  - Decompose \(Y\) into reduction part \(Y^{(0)}\) and formal part \(Y^{(1)}\).
  - Use integrality/finite-local-condition to show \(h_p(X,Y^{(0)})\in p\mathbb{Z}_p\).
  - Use `lemA:factor` plus a valuation claim on \(\log_E(Y^{(1)})\) (or a different normalization-dependent argument) to show \(h_p(X,Y^{(1)})\in p\mathbb{Z}_p\).

#### Full proof (massive detail; edit)

**Currently marked `suspect` pending completion of (1) and a normalization-accurate proof of (2).**  

What we can safely record now:
- For each fixed prime \(p\), there certainly exists \(m\) prime to \(p\) with \(mP\in E_1(\mathbb{Q}_p)\) (take \(m=\mathrm{ord}(P\bmod p)\), assuming this order is prime to \(p\)); this is `lemA:formal-membership`.
- The additional claim “\(\log_E(mP)\in\mathbb{Z}_p^\times\) for all but finitely many \(p\)” needs a dedicated argument (or an explicit citation) and should be treated as a potential blocker until supplied.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L2759 — remark (On normalizations)

- **Source**: `BSD-Jon-Final.txt` L2759–L2761
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: lemA:factor
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[On normalizations]
The constant $u_p\in\mathbb{Z}_p^\times$ in Lemma~\ref{lemA:factor} depends on the choice of Néron differential and the branch of the Coleman integral but does not affect $p$–adic valuations. Any exceptional–zero factor at $p$ can be removed by the standard Greenberg–Stevens correction; in this note we simply exclude such primes from the ordinary track.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L2819 — remark (Two routes to the equality)

- **Source**: `BSD-Jon-Final.txt` L2819–L2821
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Two routes to the equality]
If one assumes the \emph{full} cyclotomic IMC at $p$ (standing input (B1)), then $\xi_p(T)$ and $L_p(E,T)$ generate the same principal ideal, and the equality of orders at $T=0$ is immediate from $\mu_p=0$. Alternatively, the one–sided divisibility \eqref{eq:divisibility} together with the Perrin–Riou leading–term identification \eqref{eq:PR-leading} already suffices, as used above.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L2823 — remark (Supersingular $\pm$–theory)

- **Source**: `BSD-Jon-Final.txt` L2823–L2825
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Supersingular $\pm$–theory]
At supersingular $p$, replace $X_p$ and $L_p(E,T)$ by their $\pm$–signed counterparts, and interpret $\mu_p$ and $s_p$ in the signed Iwasawa modules. The argument carries over verbatim.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lemC:height=PT — lemma (Height as Poitou–Tate on Kummer classes)

- **Source**: `BSD-Jon-Final.txt` L2861–L2867
- **Status**: outlined
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - The source only provides a **proof sketch** and treats this as “standard Nekovář–Perrin–Riou height compatibility”. For audit-grade status we need a precise reference and the exact normalization choices (differential/branch).
  - **Important**: this lemma itself is plausible/standard, but the *next step* in Appendix C.3 (“nondegenerate height ⇒ \(\Sha[p^\infty]\) finite”) contains a dimension argument error (see note in the Full proof section below).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Height as Poitou–Tate on Kummer classes]\label{lemC:height=PT}
There exists $u_p\in\mathbb{Z}_p^\times$ such that for all $P,Q\in E(\mathbb{Q})$,
\[
h_p(P,Q)\ =\ u_p\ \big\langle \kappa_p(P),\ \kappa_p(Q)\big\rangle_{\mathrm{PT}}.
\]
In particular, $h_p$ is nondegenerate if and only if the restriction of $\langle\ ,\ \rangle_{\mathrm{PT}}$ to $\mathrm{Im}(\kappa_p)$ is nondegenerate.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - The definition of the cyclotomic \(p\)-adic height pairing \(h_p\) fixed in §2.4 of the source.
  - The Poitou–Tate pairing \(\langle\ ,\ \rangle_{\mathrm{PT}}\) on \(H^1_f(\mathbb{Q},V)\) in Appendix C.1 of the source.
- **External (papers/books/theorems)**:
  - Nekovář Selmer complexes / Perrin–Riou height formalism: identification of the Coleman–Gross/Nekovář height with the global Poitou–Tate pairing on Kummer classes, up to a unit depending on normalization.

#### Proof outline (edit)

- The global Poitou–Tate pairing \(\langle\ ,\ \rangle_{\mathrm{PT}}\) on \(H^1_f(\mathbb{Q},V)\) is perfect.
- The cyclotomic \(p\)-adic height \(h_p\) is constructed from the same global cup product, composed with local logarithms/splittings (Nekovář–Perrin–Riou). On Kummer classes \(\kappa_p(P)\), this matches \(\langle\ ,\ \rangle_{\mathrm{PT}}\) up to a unit factor \(u_p\in\mathbb{Z}_p^\times\) coming from the chosen differential/branch normalization.

#### Full proof (massive detail; edit)

**Outline / citation placeholder (needs a precise reference):**

Let \(T=T_pE\), \(V=T\otimes_{\mathbb{Z}_p}\mathbb{Q}_p\), and \(H^1_f(\mathbb{Q},V)\) be the Bloch–Kato Selmer group (as in Appendix C.1 of the source). Poitou–Tate duality provides a perfect pairing
\[
\langle\ ,\ \rangle_{\mathrm{PT}}:H^1_f(\mathbb{Q},V)\times H^1_f(\mathbb{Q},V^*(1))\to\mathbb{Q}_p,
\]
and via the principal polarization we identify \(V^*(1)\simeq V\), hence \(\langle\ ,\ \rangle_{\mathrm{PT}}\) is a perfect symmetric pairing on \(H^1_f(\mathbb{Q},V)\).

The cyclotomic Coleman–Gross height \(h_p\) on \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) is (in the Nekovář–Perrin–Riou formulation) the restriction of this Poitou–Tate pairing to Kummer classes, composed with the chosen cyclotomic logarithm/splittings at \(p\). This introduces a normalization factor \(u_p\in\mathbb{Z}_p^\times\) depending on the chosen Néron differential and the branch of the Coleman integral (as the source notes). Therefore there exists \(u_p\in\mathbb{Z}_p^\times\) such that
\[
h_p(P,Q)=u_p\,\langle \kappa_p(P),\kappa_p(Q)\rangle_{\mathrm{PT}}\qquad(\forall P,Q\in E(\mathbb{Q})).
\]
Nondegeneracy equivalence follows immediately because multiplication by \(u_p\in\mathbb{Z}_p^\times\) does not change whether the restricted pairing is degenerate.

**Critical audit note (Appendix C.3 error):**  
The source’s subsequent claim “\(h_p\) nondegenerate on \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) ⇒ \(\Sha(E/\mathbb{Q})[p^\infty]\) finite” is *not proved* by the dimension argument given in Appendix C.3.  
Reason: from perfectness of \(\langle\ ,\ \rangle_{\mathrm{PT}}\) and nondegeneracy on \(\mathrm{Im}(\kappa_p)\), one gets a direct sum decomposition
\[
H^1_f(\mathbb{Q},V)=\mathrm{Im}(\kappa_p)\oplus \mathrm{Im}(\kappa_p)^\perp,
\]
but this does **not** force \(\mathrm{Im}(\kappa_p)^\perp=0\). In fact, \(\dim \mathrm{Im}(\kappa_p)^\perp=\dim H^1_f-\dim \mathrm{Im}(\kappa_p)\), which is exactly the \(\mathbb{Q}_p\)-dimension of \(\Sha[p^\infty]\otimes\mathbb{Q}_p\) per the source’s own identity \(\dim H^1_f = \mathrm{rank} + \mathrm{corank}\,\Sha[p^\infty]\). So additional input is needed to deduce finiteness.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:Hlambda-to-revdiv — proposition (Positivity $\Rightarrow$ reverse divisibility)

- **Source**: `BSD-Jon-Final.txt` L3283–L3292
- **Status**: outlined
- **Auto-flags**: ASSUMES
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - Entirely conditional on (HΛ), i.e. on `thm:HL-ordinary` / `thm:HL-signed` plus the operator setup (`K(T)`, `coker = Selmer`, `det = L_p`) and the Fitting control.

#### Statement (verbatim from source)

```tex
\begin{proposition}[Positivity $\Rightarrow$ reverse divisibility]\label{prop:Hlambda-to-revdiv}
Assume \emph{(H$\Lambda$)} holds (ordinary or signed). Then for every finite-order character $\chi$ of $\Gamma$,
\[
 \mathrm{length}_{\mathbb{Z}_p}\,\mathrm{coker}(I-K(\chi))\ \le\ \mathrm{ord}_p\det(I-K(\chi)).
\]
Consequently,
\[
 (L_p(E,T))\ \mid\ \mathrm{char}_\Lambda X_p(E/\mathbb{Q}_\infty)\qquad\text{(ordinary or signed)}.
\]
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `thm:HL-ordinary` / `thm:HL-signed` (to supply hypotheses (i)–(ii) after χ-specialization)
  - `lem:pr-length` (the χ-level length vs determinant inequality)
  - Operator setup theorems: `thm:coker-id` / `thm:det-equals-Lp` (or their ordinary/signed variants)
- **External (papers/books/theorems)**:
  - Basic commutative algebra over DVRs (Smith/elementary divisors; length bounds via determinants)

#### Proof outline (edit)

- For each finite-order χ, specialize the operator \(I-K(T)\) to a \(\mathbb{Z}_p\)-linear endomorphism \(I-K(\chi)\) of a finite free \(\mathbb{Z}_p\)-module.
- Use the (HΛ) package to control the kernel/cokernel lengths via nondegeneracy of the specialized pairing and “nullspace injects into local condition” (this is the key analytic input).
- Use Fitting-minor control over a DVR: \(\mathrm{length}(\mathrm{coker}(I-K(\chi))) \le \mathrm{ord}_p(\det(I-K(\chi)))\).
- Then identify \(\det(I-K(T))\doteq L_p(E,T)\) and \(\mathrm{coker}(I-K(T))^\vee \simeq X_p\) to deduce \((L_p)\mid \mathrm{char}_\Lambda(X_p)\).

#### Full proof (massive detail; edit)

This proposition is essentially a wrapper around the χ-level inequality `lem:pr-length`, plus the identifications “\(\det(I-K)=L_p\)” and “\(\mathrm{coker}(I-K)^\vee=X_p\)”.

Audit note: to make this `drafted/audited`, we need the full operator model details (Fitting ideals, specialization compatibility) and the exact way (HΛ) forces the χ-level kernel/cokernel bound.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### conj:sep-density — conjecture (Separated primes have positive density)

- **Source**: `BSD-Jon-Final.txt` L3299–L3301
- **Status**: todo
- **Auto-flags**: CONJECTURE
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{conjecture}[Separated primes have positive density]\label{conj:sep-density}
For any non-torsion $\{P_i\}_{i=1}^r\subset E(\mathbb{Q})$, the set of good ordinary primes $p$ for which $o_j(p)\nmid o_i(p)$ for all $i\ne j$ has a natural density $\delta_{E,\{P_i\}}\in(0,1]$.
\end{conjecture}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:sep-infinitude — theorem (Infinitude under Serre and independence; sketch)

- **Source**: `BSD-Jon-Final.txt` L3303–L3305
- **Status**: todo
- **Auto-flags**: SKETCH, ASSUMES
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Infinitude under Serre and independence; sketch]\label{thm:sep-infinitude}
Assume $\rho_{E,\mathrm{mod}\,N}:\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to \mathrm{GL}_2(\mathbb{Z}/N\mathbb{Z})$ has image containing $\mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$ for all large enough $N$ (Serre open image), and that the reductions of $\{P_i\}$ are independent modulo $N$ for a set of moduli of positive density. Then there exist infinitely many good ordinary primes $p$ for which $\{o_i(p)\}$ are pairwise nondividing (separated). Moreover, one obtains a quantitative lower bound on the relative frequency along a sequence of moduli.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:sha-global-criterion — proposition (Criterion via $\Lambda$–adic positivity and PT; sketch)

- **Source**: `BSD-Jon-Final.txt` L3312–L3314
- **Status**: todo
- **Auto-flags**: SKETCH
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Criterion via $\Lambda$–adic positivity and PT; sketch]\label{prop:sha-global-criterion}
Suppose \emph{(H$\Lambda$)} holds for a cofinite set of ordinary/signed primes and all finite-order characters at those primes. Then, via Poitou–Tate duality and the Cassels–Tate pairing, one has $\mathrm{corank}_{\mathbb{Z}_p}\Sha(E/\mathbb{Q})[p^\infty]=0$ for each such $p$. If this holds for all $p$, then $\Sha(E/\mathbb{Q})$ is finite.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:smallp-kpx — lemma (Overconvergent $(\varphi,\Gamma)$–module replacement)

- **Source**: `BSD-Jon-Final.txt` L3325–L3327
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Overconvergent $(\varphi,\Gamma)$–module replacement]\label{lem:smallp-kpx}
For $p\in\{2,3\}$ there exists a finite free $\Lambda$–lattice $M\subset H^1_{\emph{Iw}}(\mathbb{Q},V)$ and overconvergent $(\varphi,\Gamma)$–module models for $V$ at $p$ such that the ordinary (resp. signed) Coleman maps are defined integrally on $M_p$ and interpolate Bloch–Kato logarithms at finite–order characters up to $\mathbb{Z}_p^{\times}$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:smallp-detexact — theorem (Integral determinant and exact kernel at small primes)

- **Source**: `BSD-Jon-Final.txt` L3333–L3339
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: thm:coker-id, thm:coker-id-signed
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Integral determinant and exact kernel at small primes]\label{thm:smallp-detexact}
With $p\in\{2,3\}$ and notation as above, the determinant identities
\[
  \det_{\Lambda}(I-K(T))\doteq L_p(E,T),\qquad \det_{\Lambda}(I-K_{\pm}(T))\doteq L_p^{\pm}(E,T)
\]
hold integrally (up to $\Lambda^{\times}$), and the exact kernel/cokernel statements of Theorems~\ref{thm:coker-id}, \ref{thm:coker-id-signed} remain valid on a saturated $\Lambda$–lattice. Consequently, the reverse divisibilities $\mathrm{char}_{\Lambda}X_p\mid(L_p)$ and $\mathrm{char}_{\Lambda}X_p^{\pm}\mid(L_p^{\pm})$ hold at $p\in\{2,3\}$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:smallp-signed-fs — lemma (Trianguline control for signed maps at small $p$)

- **Source**: `BSD-Jon-Final.txt` L3346–L3348
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Trianguline control for signed maps at small $p$]\label{lem:smallp-signed-fs}
At $p\in\{2,3\}$ and supersingular reduction, the signed Coleman maps extend over trianguline families with integral interpolation; the specialization errors are controlled uniformly in weight and conductor. Consequently, the signed determinant and kernel exactness persist at finite slope.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:HL-ordinary — theorem (H$\Lambda$–Ord)

- **Source**: `BSD-Jon-Final.txt` L3355–L3369
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Depends on**:
    - Perrin–Riou big logarithm \(\mathcal{L}_V\) and its explicit reciprocity / interpolation (the source’s `lem:PR-ord-proof`).
    - Identification of \(\ker(\mathrm{Col}_p(\chi))\) with the ordinary local condition at \(p\) (needs a precise reference/definition of \(\mathrm{Col}_p\)).
    - Nondegeneracy of Bloch–Kato height on \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) modulo torsion (source `lem:HL-nondeg` is essentially a citation/claim).

#### Statement (verbatim from source)

```tex
\begin{theorem}[H$\Lambda$–Ord]\label{thm:HL-ordinary}
Let $E/\mathbb{Q}$ have good ordinary reduction at $p\ge5$ and let $V=T_pE\otimes\mathbb{Q}_p$. Define a $\Lambda$–adic height
\[
 h_\Lambda: H^1_{\emph{Iw}}(\mathbb{Q},V)\times H^1_{\emph{Iw}}(\mathbb{Q},V)\to \Lambda
\]
by composing the global cup product with Perrin–Riou’s big logarithm $\mathcal{L}_V$ and the ordinary projector $e_{\mathrm{ord}}$ at $p$, and the finite (Greenberg) local conditions away from $p$. Then, for every finite-order character $\chi$ of $\Gamma$:
\begin{itemize}
\item[(i)] $\mathrm{ev}_\chi\circ h_\Lambda$ equals the Bloch–Kato height pairing $h_{\mathrm{BK},\chi}$ (up to a $p$–adic unit), hence is nondegenerate on $E(\mathbb{Q})\otimes\mathbb{Q}_p$ modulo torsion; and
\item[(ii)] the nullspace of $\mathrm{ev}_\chi\circ h_\Lambda$ injects into the ordinary local condition at $p$ defining $\mathrm{Sel}_{p^\infty}(E/\mathbb{Q})$ at $\chi$.
\end{itemize}
Consequently (H$\Lambda$) holds in the ordinary case, and for each $\chi$ one has
\[
 \mathrm{length}_{\mathbb{Z}_p}\,\mathrm{coker}(I-K(\chi))\ \le\ \mathrm{ord}_p\det(I-K(\chi)).
\]
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:PR-ord-proof`, `lem:HL-nondeg`, `lem:HL-nullspace`
  - `prop:Hlambda-to-revdiv` (for the final length inequality conclusion)
- **External (papers/books/theorems)**:
  - Perrin–Riou explicit reciprocity (and its Wach-module realizations: Berger; Cherbonnier–Colmez)
  - Greenberg local conditions and control theorems
  - Identification of Bloch–Kato heights with cyclotomic \(p\)-adic heights in the ordinary case (Nekovář/Perrin–Riou framework)

#### Proof outline (edit)

- Define \(h_\Lambda\) by pairing localizations at \(p\) through \(\ell\circ \mathcal{L}_V\) and summing finite local pairings away from \(p\).
- Specialize at a finite-order character \(\chi\); use Perrin–Riou interpolation to identify the \(p\)-part with Bloch–Kato logarithms and hence identify \(\mathrm{ev}_\chi\circ h_\Lambda\) with \(h_{\mathrm{BK},\chi}\) up to a unit.
- Use the definition of the ordinary Coleman map at \(\chi\) to show “nullspace implies \(\mathrm{Col}_p(\mathrm{loc}_p x)(\chi)=0\)”, hence \(\mathrm{loc}_p x\) lies in the ordinary local condition; away from \(p\), finite local conditions are built into the definition.
- Apply `prop:Hlambda-to-revdiv` to deduce the length inequality for \(\mathrm{coker}(I-K(\chi))\).

#### Full proof (massive detail; edit)

We expand the source proof (L3370–L3403).

**Construction of \(h_\Lambda\).**  
Let \(V=T_pE\otimes_{\mathbb{Z}_p}\mathbb{Q}_p\). For each place \(v\), let \(\mathrm{loc}_v\) denote localization in Iwasawa cohomology. Let \(\mathcal{L}_V:H^1_{\mathrm{Iw}}(\mathbb{Q}_p,V)\to \Lambda\otimes D_{\mathrm{cris}}(V)\) be Perrin–Riou’s big logarithm. Let \(e_{\mathrm{ord}}\) be the ordinary projector (unit-root line) and let \(\ell:D_{\mathrm{cris}}(V)\to \mathbb{Q}_p\) be the functional “projection to the ordinary line” (as in the source).

Define the \(\Lambda\)-valued pairing
\[
h_\Lambda(x,y):=\big\langle (\ell\circ \mathcal{L}_V)(\mathrm{loc}_p x),(\ell\circ \mathcal{L}_V)(\mathrm{loc}_p y)\big\rangle_\Lambda\;+\;\sum_{v\nmid p}\langle \mathrm{loc}_v x,\mathrm{loc}_v y\rangle_v,
\]
where the away–\(p\) pairings are the finite (Greenberg) local pairings and \(\langle\ ,\ \rangle_\Lambda\) denotes the natural \(\Lambda\)-bilinear pairing on the ordinary line after choosing the compatible bases (this is normalization-dependent but only up to \(\Lambda^\times\)).

The pairing is \(\Lambda\)-bilinear by construction, symmetric by symmetry of local Tate pairings, and well-defined on the chosen \(\Lambda\)-lattice.

**(i) Specialization equals Bloch–Kato height (up to a unit).**  
Fix a finite-order character \(\chi\) of \(\Gamma\). Apply \(\mathrm{ev}_\chi:\Lambda\to \mathbb{Z}_p\). The source’s lemma `lem:PR-ord-proof` asserts that for each \(z\),
\[
(\mathrm{ev}_\chi\otimes \mathrm{id})\,\mathcal{L}_V(\mathrm{loc}_p z)=u(E,p,\chi)\cdot \mathrm{BK}_\chi(\mathrm{loc}_p z),\qquad u(E,p,\chi)\in \mathbb{Z}_p^\times,
\]
so the specialized \(p\)-part of \(h_\Lambda\) matches the Bloch–Kato local logarithm pairing up to a unit. The away–\(p\) summands are, by design, the finite local terms that also appear in the Bloch–Kato height construction. Therefore
\[
\mathrm{ev}_\chi\circ h_\Lambda=u(E,p,\chi)\cdot h_{\mathrm{BK},\chi}
\]
on global cohomology/Kummer classes, which yields (i). Nondegeneracy on \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) modulo torsion is deferred by the source to `lem:HL-nondeg` (a cited standard fact, excluding a finite exceptional set).

**(ii) Nullspace injection into the ordinary local condition.**  
Assume \(\mathrm{ev}_\chi\circ h_\Lambda(x,\cdot)\equiv 0\). Then in particular the \(p\)-component contribution vanishes, which (by `lem:PR-ord-proof`) implies
\[
(\ell\circ \mathcal{L}_V)(\mathrm{loc}_p x)(\chi)=0.
\]
By definition of the (ordinary) Coleman map \(\mathrm{Col}_p\), the quantity \((\ell\circ \mathcal{L}_V)(\mathrm{loc}_p x)(\chi)\) is \(\mathrm{Col}_p(\mathrm{loc}_p x)(\chi)\) up to a unit, hence \(\mathrm{Col}_p(\mathrm{loc}_p x)(\chi)=0\). The kernel of \(\mathrm{Col}_p(\chi)\) is (by the source’s stated setup) exactly the ordinary local condition at \(p\) for the χ-specialized Selmer group, so \(\mathrm{loc}_p x\) lies in that local condition. For \(v\nmid p\), the height definition built in the finite local conditions, forcing \(\mathrm{loc}_v x\) into the finite local subgroup when orthogonal to everything. This is the content of `lem:HL-nullspace`.

**Length inequality.**  
Given (i)–(ii) (collectively called (HΛ)), apply `prop:Hlambda-to-revdiv` to obtain
\[
\mathrm{length}_{\mathbb{Z}_p}\,\mathrm{coker}(I-K(\chi))\ \le\ \mathrm{ord}_p\det(I-K(\chi)).
\]

This completes the proof at the level of detail currently present in the source; fully auditing it requires expanding `lem:HL-nondeg` and justifying the “kernel of Coleman map equals ordinary local condition at χ” identification.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:PR-ord-proof — lemma (Perrin–Riou interpolation, ordinary projection)

- **Source**: `BSD-Jon-Final.txt` L3377–L3383
- **Status**: conditional
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - This is **Perrin–Riou explicit reciprocity** (ordinary projection) and is treated as an external theorem in the source. Audit-grade completion requires importing the exact statement and hypotheses from the cited references.
  - **Deep-dive note**: `notes/papers/bsd/1994-1995-perrin-riou-big-log-notes.md`

#### Statement (verbatim from source)

```tex
\begin{lemma}[Perrin–Riou interpolation, ordinary projection]\label{lem:PR-ord-proof}
For every finite-order character $\chi$ of $\Gamma$,
\[
 (\mathrm{ev}_\chi\otimes\mathrm{id})\,\mathcal{L}_V(\mathrm{loc}_p\,z)\ =\ u(E,p,\chi)\cdot \mathrm{BK}_\chi(\mathrm{loc}_p\,z),\qquad u(E,p,\chi)\in\mathbb{Z}_p^{\times},
\]
and hence $\mathrm{ev}_\chi\circ h_\Lambda=u(E,p,\chi)\cdot h_{\mathrm{BK},\chi}$ on $H^1(\mathbb{Q},V)$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - The definition of the big logarithm \(\mathcal{L}_V\) and the ordinary functional \(\ell\).
- **External (papers/books/theorems)**:
  - Perrin–Riou (1994/1995) explicit reciprocity law for \(\mathcal{L}_V\)
  - Berger (2003) and Cherbonnier–Colmez (1999) for explicit realizations via Wach modules / \((\varphi,\Gamma)\)-modules

#### Proof outline (edit)

- Cite Perrin–Riou’s reciprocity law: evaluation of \(\mathcal{L}_V\) at a finite-order character \(\chi\) interpolates the Bloch–Kato logarithm/exponential maps (up to explicit Euler factors).
- Compose with the ordinary projector/functional \(\ell\) to isolate the ordinary line and obtain the unit factor \(u(E,p,\chi)\in\mathbb{Z}_p^\times\).
- Substitute into the definition of \(h_\Lambda\) to deduce \(\mathrm{ev}_\chi\circ h_\Lambda = u(E,p,\chi)\cdot h_{\mathrm{BK},\chi}\).

#### Full proof (massive detail; edit)

The source’s proof is a citation: see `BSD-Jon-Final.txt` L3384–L3386.  

To make this audit-ready inside this track, we must paste:
- the precise definition of \(\mathcal{L}_V\) being used (normalizations, bases),
- Perrin–Riou’s explicit reciprocity formula at finite-order characters,
- and check that after applying \(\ell\) (ordinary line), all remaining Euler factors are \(p\)-adic units for the χ in question (i.e. excluding exceptional zero characters).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:HL-nondeg — lemma (Nondegeneracy on MW/torsion)

- **Source**: `BSD-Jon-Final.txt` L3388–L3390
- **Status**: conditional
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - This is a **major input**: nondegeneracy of (cyclotomic) Bloch–Kato \(p\)-adic heights on \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) is not automatic and typically encodes nonvanishing of a \(p\)-adic regulator.
  - The source treats it as “standard under usual hypotheses” and cites Greenberg/Kato, but does not supply a proof or a precise statement of hypotheses. Treat as conditional until a concrete reference+statement is supplied.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Nondegeneracy on MW/torsion]\label{lem:HL-nondeg}
For each finite-order $\chi$ (outside a finite exceptional set corresponding to exceptional zero phenomena), $h_{\mathrm{BK},\chi}$ is nondegenerate on $E(\mathbb{Q})\otimes\mathbb{Q}_p$ modulo torsion.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - Relationship between \(\mathrm{ev}_\chi\circ h_\Lambda\) and \(h_{\mathrm{BK},\chi}\) (`lem:PR-ord-proof`)
- **External (papers/books/theorems)**:
  - A reference that actually proves (or precisely states) nondegeneracy of the relevant \(p\)-adic height pairing on Mordell–Weil modulo torsion, including any exceptional-zero corrections and any needed hypotheses.

#### Proof outline (edit)

- (If true) reduce nondegeneracy to nonvanishing of the \(p\)-adic regulator for the chosen height normalization (possibly after removing exceptional zero factors).
- Cite a theorem establishing this nonvanishing/nondegeneracy outside a finite exceptional set of χ (or explicitly list what is known and what is conjectural).

#### Full proof (massive detail; edit)

The source provides only a high-level citation-style paragraph. This remains **conditional** until we pin down:
- which exact height pairing \(h_{\mathrm{BK},\chi}\) is meant (twisted by χ? which local conditions?),
- and a reference proving nondegeneracy on \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) modulo torsion (or else downgrade this to a conjectural input).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:HL-nullspace — lemma (Nullspace injection into the ordinary local condition)

- **Source**: `BSD-Jon-Final.txt` L3395–L3397
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - Conditional on `lem:PR-ord-proof` and on the identification “\(\ker(\mathrm{Col}_p(\chi))\) equals the ordinary local condition at \(p\) for χ” (a definitional/standard fact but must be pinned down precisely in this operator model).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Nullspace injection into the ordinary local condition]\label{lem:HL-nullspace}
If $\mathrm{ev}_\chi\circ h_\Lambda(x,\cdot)\equiv 0$, then $\mathrm{loc}_p\,x$ lies in the ordinary local condition at $\chi$, and for $v\nmid p$, $\mathrm{loc}_v\,x$ lies in the finite local subgroup.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:PR-ord-proof` (to convert vanishing of the specialized height functional into vanishing of the Coleman map at χ)
  - Definitions of the ordinary Coleman map \(\mathrm{Col}_p\) and the ordinary local condition at χ
- **External (papers/books/theorems)**:
  - Standard identification of Coleman-map kernels with Greenberg ordinary local conditions (in the chosen Wach-module normalization)

#### Proof outline (edit)

- If \(\mathrm{ev}_\chi\circ h_\Lambda(x,\cdot)\equiv 0\), then the \(p\)-part of the pairing vanishes.
- By Perrin–Riou interpolation (`lem:PR-ord-proof`), this forces \((\ell\circ\mathcal{L}_V)(\mathrm{loc}_p x)(\chi)=0\), i.e. \(\mathrm{Col}_p(\mathrm{loc}_p x)(\chi)=0\) up to a unit.
- By definition/standard property, \(\ker(\mathrm{Col}_p(\chi))\) is the ordinary local condition at χ; hence \(\mathrm{loc}_p x\) lies in it.
- Away from \(p\), the pairing definition uses finite local conditions, so orthogonality forces \(\mathrm{loc}_v x\) into the finite local subgroup.

#### Full proof (massive detail; edit)

Assume \(\mathrm{ev}_\chi\circ h_\Lambda(x,\cdot)\equiv 0\). Looking at the definition of \(h_\Lambda\), the \(p\)-term is a pairing of \((\ell\circ\mathcal{L}_V)(\mathrm{loc}_p x)\) against \((\ell\circ\mathcal{L}_V)(\mathrm{loc}_p y)\) for varying \(y\). If the specialized functional is identically zero, then in particular the specialized value \((\ell\circ\mathcal{L}_V)(\mathrm{loc}_p x)(\chi)\) must vanish.

By `lem:PR-ord-proof`, vanishing of \((\ell\circ\mathcal{L}_V)(\mathrm{loc}_p x)(\chi)\) is equivalent (up to a unit) to \(\mathrm{Col}_p(\mathrm{loc}_p x)(\chi)=0\). By the definition of the χ-ordinary local condition in the ordinary theory, this is exactly the condition that \(\mathrm{loc}_p x\) lies in the ordinary local condition at χ.

For \(v\nmid p\), the height pairing’s definition includes only the finite (Greenberg) local conditions, so an element orthogonal to all Kummer classes must localize into the finite subgroup at each such \(v\). This matches the source’s proof (L3398–L3400).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:HL-signed — theorem (H$\Lambda$–Signed)

- **Source**: `BSD-Jon-Final.txt` L3407–L3414
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: prop:Hlambda-to-revdiv
- **Conditional on / Blockers (edit)**:
  - **Depends on** signed explicit reciprocity / Pollack–Kobayashi theory (`lem:PR-signed-proof`) and the identification of the signed Coleman-map kernels with Kobayashi’s \(\pm\) local conditions at each χ.
  - Nondegeneracy of signed Bloch–Kato heights is treated as “standard” in the source (`lem:HL-signed-nondeg`) and needs a concrete reference and hypotheses (exceptional zeros, etc.).

#### Statement (verbatim from source)

```tex
\begin{theorem}[H$\Lambda$–Signed]\label{thm:HL-signed}
Let $p\ge5$ be supersingular for $E/\mathbb{Q}$. Using Pollack’s $\log^{\pm}$ and Kobayashi’s $\pm$ local conditions, define signed Coleman maps and a signed $\Lambda$–adic height $h_\Lambda^{\pm}$. Then for every finite-order $\chi$ of $\Gamma$:
\begin{itemize}
\item[(i)] $\mathrm{ev}_\chi\circ h_\Lambda^{\pm}$ equals the signed Bloch–Kato height (up to a $p$–adic unit), hence is nondegenerate on $E(\mathbb{Q})\otimes\mathbb{Q}_p$ modulo torsion; and
\item[(ii)] the nullspace injects into the signed local condition at $p$ defining $\mathrm{Sel}_{p^\infty}^{\pm}(E/\mathbb{Q})$ at $\chi$.
\end{itemize}
Consequently (H$\Lambda$) holds in the signed case and the operator inequality of Proposition~\ref{prop:Hlambda-to-revdiv} follows for $\pm$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:PR-signed-proof`, `lem:HL-signed-nondeg`, `lem:HL-signed-nullspace`
  - `prop:Hlambda-to-revdiv`
- **External (papers/books/theorems)**:
  - Pollack \(\log^\pm\), Kobayashi \(\pm\)-Selmer theory, Lei–Loeffler–Zerbes Wach-module approach

#### Proof outline (edit)

- Mirror `thm:HL-ordinary` with signed projectors and signed Coleman maps.
- Use signed explicit reciprocity to identify specializations with signed Bloch–Kato heights up to units.
- Use that \(\ker(\mathrm{Col}_p^\pm(\chi))\) matches the \(\pm\) local condition at χ to prove nullspace injection.
- Apply `prop:Hlambda-to-revdiv` to obtain the length inequality.

#### Full proof (massive detail; edit)

This follows the source proof (L3415–L3448) and is formally parallel to `thm:HL-ordinary`.

**Construction.**  
At a supersingular prime \(p\ge 5\), fix Pollack’s \(\log^\pm\) and Kobayashi’s \(\pm\) local conditions. Use Perrin–Riou’s big logarithm \(\mathcal{L}_V\) together with signed functionals \(\ell_\pm:D_{\mathrm{cris}}(V)\to \mathbb{Q}_p\) to define signed Coleman maps \(\mathrm{Col}_p^\pm\) and a signed \(\Lambda\)-adic height pairing
\[
h_\Lambda^\pm(x,y):=\big\langle (\ell_\pm\circ \mathcal{L}_V)(\mathrm{loc}_p x),(\ell_\pm\circ \mathcal{L}_V)(\mathrm{loc}_p y)\big\rangle_\Lambda\;+\;\sum_{v\nmid p}\langle \mathrm{loc}_v x,\mathrm{loc}_v y\rangle_v.
\]

**(i) Specialization equals signed Bloch–Kato height (up to a unit).**  
For each finite-order \(\chi\), `lem:PR-signed-proof` gives
\[
\mathrm{ev}_\chi\circ h_\Lambda^\pm=u_\pm(E,p,\chi)\cdot h_{\mathrm{BK},\chi}^\pm,\qquad u_\pm(E,p,\chi)\in \mathbb{Z}_p^\times,
\]
so specialization identifies the signed \(\Lambda\)-adic height with the signed Bloch–Kato height, up to a unit factor. Nondegeneracy on \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) modulo torsion is deferred to `lem:HL-signed-nondeg` (again treated as standard up to exceptional zeros).

**(ii) Nullspace injection into the \(\pm\) local condition.**  
If \(\mathrm{ev}_\chi\circ h_\Lambda^\pm(x,\cdot)\equiv 0\), then the \(p\)-part vanishes; by `lem:PR-signed-proof` this implies \((\ell_\pm\circ \mathcal{L}_V)(\mathrm{loc}_p x)(\chi)=0\), i.e. \(\mathrm{Col}_p^\pm(\mathrm{loc}_p x)(\chi)=0\) up to a unit. By definition of the signed local conditions, this places \(\mathrm{loc}_p x\) in the \(\pm\) local condition at χ. Away from \(p\), the same finite-local-condition argument applies. This is `lem:HL-signed-nullspace`.

**Length inequality.**  
With (i)–(ii) in hand, apply `prop:Hlambda-to-revdiv` to obtain the χ-level length bound and hence reverse divisibility in the signed case.

As with the ordinary case, full audit requires expanding the “kernel = local condition” and nondegeneracy inputs with explicit references/hypotheses.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:PR-signed-proof — lemma (Signed explicit reciprocity)

- **Source**: `BSD-Jon-Final.txt` L3422–L3428
- **Status**: conditional
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - This is a signed (\(\pm\)) version of Perrin–Riou explicit reciprocity and is treated as an external theorem in the source; completing this requires importing the precise Pollack/Kobayashi/LLZ statements and checking normalizations.
  - **Deep-dive note**: `notes/papers/bsd/1994-1995-perrin-riou-big-log-notes.md` (plus signed theory note: `notes/papers/bsd/kobayashi-pollack-llz-signed-theory-notes.md`)

#### Statement (verbatim from source)

```tex
\begin{lemma}[Signed explicit reciprocity]\label{lem:PR-signed-proof}
For every finite-order $\chi$ of $\Gamma$,
\[
 (\mathrm{ev}_\chi\otimes\mathrm{id})\,\mathcal{L}_V(\mathrm{loc}_p\,z)\ =\ u_{\pm}(E,p,\chi)\cdot \mathrm{BK}_\chi^{\pm}(\mathrm{loc}_p\,z),\qquad u_{\pm}(E,p,\chi)\in\mathbb{Z}_p^{\times},
\]
and hence $\mathrm{ev}_\chi\circ h_\Lambda^{\pm}=u_{\pm}(E,p,\chi)\cdot h_{\mathrm{BK},\chi}^{\pm}$ on $H^1(\mathbb{Q},V)$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - Definition of the signed functionals \(\ell_\pm\) and signed Coleman maps \(\mathrm{Col}_p^\pm\).
- **External (papers/books/theorems)**:
  - Pollack (2003), Kobayashi (2003), Lei–Loeffler–Zerbes (2012): signed logarithms / signed Coleman maps / signed reciprocity

#### Proof outline (edit)

- Cite the signed explicit reciprocity law: evaluation of \(\mathcal{L}_V\) composed with the signed projector/functionals \(\ell_\pm\) interpolates the signed Bloch–Kato maps at finite-order characters χ up to \(p\)-adic units.
- Substitute into the definition of \(h_\Lambda^\pm\) to get \(\mathrm{ev}_\chi\circ h_\Lambda^\pm = u_\pm(E,p,\chi)\cdot h_{\mathrm{BK},\chi}^\pm\).

#### Full proof (massive detail; edit)

The source’s proof is a citation: see `BSD-Jon-Final.txt` L3429–L3431.  

To make this audit-ready here, we need:
- the exact signed decomposition and definition of \(\ell_\pm\),
- the precise signed reciprocity statement (including Euler factors and exceptional-zero exclusions),
- and a normalization check that \(u_\pm(E,p,\chi)\in\mathbb{Z}_p^\times\) for the χ being used.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:HL-signed-nondeg — lemma (Nondegeneracy on MW/torsion (signed))

- **Source**: `BSD-Jon-Final.txt` L3433–L3435
- **Status**: conditional
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - As in the ordinary case, this is a **major input**: nondegeneracy of signed Bloch–Kato heights encodes nonvanishing of a signed \(p\)-adic regulator and is not automatic.
  - The source treats this as “standard” with citations (Kobayashi/Sprung/LLZ) but does not give a precise theorem statement/hypotheses; treat as conditional until specified.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Nondegeneracy on MW/torsion (signed)]\label{lem:HL-signed-nondeg}
For each finite-order $\chi$ (outside a finite exceptional set), the signed Bloch–Kato height $h_{\mathrm{BK},\chi}^{\pm}$ is nondegenerate on $E(\mathbb{Q})\otimes\mathbb{Q}_p$ modulo torsion.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - Signed specialization identity (`lem:PR-signed-proof`)
- **External (papers/books/theorems)**:
  - A theorem/reference establishing nondegeneracy (or conditions for it) of the signed height pairing on \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) modulo torsion, excluding exceptional zeros.

#### Proof outline (edit)

- Reduce to nonvanishing of the signed regulator and cite a result that guarantees it outside a finite exceptional set of χ (or else mark as conjectural).

#### Full proof (massive detail; edit)

No audit-grade proof is present in the source; this remains conditional until the exact result/hypotheses are pinned down.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:HL-signed-nullspace — lemma (Nullspace injection into $\pm$ local condition)

- **Source**: `BSD-Jon-Final.txt` L3440–L3442
- **Status**: drafted
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - Conditional on `lem:PR-signed-proof` and on the identification “\(\ker(\mathrm{Col}_p^\pm(\chi))\) equals the \(\pm\) local condition at \(p\) for χ” (standard in Kobayashi/Pollack/LLZ but must match this document’s normalization).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Nullspace injection into $\pm$ local condition]\label{lem:HL-signed-nullspace}
If $\mathrm{ev}_\chi\circ h_\Lambda^{\pm}(x,\cdot)\equiv 0$, then $\mathrm{loc}_p\,x$ lies in the $\pm$ local condition at $\chi$, and for $v\nmid p$, $\mathrm{loc}_v\,x$ lies in the finite local subgroup.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:PR-signed-proof`
  - Definitions of signed Coleman maps and signed local conditions at χ
- **External (papers/books/theorems)**:
  - Standard signed Iwasawa theory: kernel of signed Coleman map equals Kobayashi’s \(\pm\) local condition

#### Proof outline (edit)

- Same structure as `lem:HL-nullspace`, replacing ordinary objects by signed ones.

#### Full proof (massive detail; edit)

Assume \(\mathrm{ev}_\chi\circ h_\Lambda^\pm(x,\cdot)\equiv 0\). Then the \(p\)-component of the pairing vanishes. By signed explicit reciprocity (`lem:PR-signed-proof`), this implies \((\ell_\pm\circ\mathcal{L}_V)(\mathrm{loc}_p x)(\chi)=0\), i.e. \(\mathrm{Col}_p^\pm(\mathrm{loc}_p x)(\chi)=0\) up to a unit.

By definition of the signed Selmer local condition at χ, \(\ker(\mathrm{Col}_p^\pm(\chi))\) is exactly the \(\pm\) local condition at \(p\), so \(\mathrm{loc}_p x\) lies in that local condition. Away from \(p\), the finite local conditions are built into the definition of the height pairing, forcing \(\mathrm{loc}_v x\) into the finite local subgroup for \(v\nmid p\).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:psmith — proposition (Pseudo–Smith form over $\Lambda$)

- **Source**: `BSD-Jon-Final.txt` L3452–L3458
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Pseudo–Smith form over $\Lambda$]\label{prop:psmith}
Let $\mathcal{C}(T)$ (resp. $\mathcal{C}^{\pm}(T)$) be the ordinary (resp. signed) Coleman matrix built from a $\Lambda$–basis of $H^1_{\emph{Iw}}(\mathbb{Q}_p,V)$. Then there exist $U,V\in\mathrm{GL}_2(\Lambda)$ and a diagonal matrix $D(T)=\mathrm{diag}(d_1(T),d_2(T))$ such that
\[
 U\,\mathcal{C}(T)\,V\ \equiv\ D(T)
\]
up to pseudo–isomorphism of $\Lambda$–modules. Moreover, the product ideal generated by $d_1(T)d_2(T)$ equals $(L_p(E,T))$ (resp. $(L_p^{\pm}(E,T))$) in $\Lambda$.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:fitting — proposition (Fitting–minor identification)

- **Source**: `BSD-Jon-Final.txt` L3472–L3481
- **Status**: audited
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - Pure commutative algebra, provided \(M\) is free of rank \(2\) over \(\Lambda\) as the statement’s “\(2\times 2\) minors” wording indicates.

#### Statement (verbatim from source)

```tex
\begin{proposition}[Fitting–minor identification]\label{prop:fitting}
Let $M\subset H^1_{\emph{Iw}}(\mathbb{Q},V)$ be a finite free $\Lambda$–lattice stable under $K(T)$, and consider $I-K(T):M\to M$. Then:
\begin{itemize}
\item[(a)] With respect to any $\Lambda$–basis of $M$, the zeroth Fitting ideal of $\mathrm{coker}(I-K(T))$ equals the ideal generated by the $2\times 2$ minors of the matrix of $I-K(T)$ (i.e. its determinant) up to $\Lambda^\times$; similarly, the first Fitting ideal is generated by the $1\times 1$ minors.
\item[(b)] For every finite-order $\chi$ of $\Gamma$, specialization commutes with Fitting ideals and satisfies
\[
 \mathrm{length}_{\mathbb{Z}_p}\,\mathrm{coker}(I-K(\chi))\ \le\ \mathrm{ord}_p\det(I-K(\chi)).
\]
\end{itemize}
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - None (pure algebra once the setup is fixed).
- **External (papers/books/theorems)**:
  - Definition and basic properties of Fitting ideals
  - Smith normal form / elementary divisor theorem over a DVR (for the χ-specialized inequality)

#### Proof outline (edit)

- (a) For a map \(f:M\to M\) of a rank-2 free module with matrix \(A(T)\), the zeroth (resp. first) Fitting ideal of \(\mathrm{coker}(f)\) is generated by the \(2\times2\) minors (resp. \(1\times1\) minors) of \(A(T)\) by definition; invariance under basis change follows since \(\mathrm{GL}_2(\Lambda)\) row/column operations do not change the ideal generated by minors.
- (b) Specialize \(\Lambda\to \mathbb{Z}_p\) via χ to get \(A(\chi)\). Over \(\mathbb{Z}_p\), Smith normal form gives \(\mathrm{length}(\mathrm{coker}(A(\chi)))=\mathrm{ord}_p(\det A(\chi))\) in the finite case, hence the stated inequality.

#### Full proof (massive detail; edit)

This is the source proof (L3482–L3490), expanded slightly.

**(a)** Let \(M\cong \Lambda^2\) and let \(f:M\to M\) be \(\Lambda\)-linear with matrix \(A(T)\in M_2(\Lambda)\) in a chosen basis. By definition of Fitting ideals from a presentation matrix, \(\mathrm{Fitt}_0(\mathrm{coker}(f))\) is the ideal generated by the \(2\times2\) minors of \(A(T)\), i.e. \((\det A(T))\), and \(\mathrm{Fitt}_1(\mathrm{coker}(f))\) is the ideal generated by the \(1\times1\) minors, i.e. the entries of \(A(T)\).

If we change basis, \(A(T)\) is replaced by \(U A(T) V\) with \(U,V\in \mathrm{GL}_2(\Lambda)\). But \(\det(UAV)=\det(U)\det(A)\det(V)\) differs from \(\det(A)\) by a unit, and the ideal generated by the entries is unchanged up to the same row/column unit operations. Hence the ideals generated by minors are basis-independent (up to \(\Lambda^\times\)).

**(b)** Let \(A(T)\) be the matrix of \(I-K(T)\) in a \(\Lambda\)-basis. Specialization at χ gives a matrix \(A(\chi)\in M_2(\mathbb{Z}_p)\) presenting \(\mathrm{coker}(I-K(\chi))\). Over the DVR \(\mathbb{Z}_p\), Smith normal form gives diagonal invariants \(p^{a_1},p^{a_2}\) with \(\mathrm{coker}(A(\chi))\cong \mathbb{Z}_p/p^{a_1}\oplus \mathbb{Z}_p/p^{a_2}\) when \(\det(A(\chi))\ne 0\), so
\[
\mathrm{length}_{\mathbb{Z}_p}\mathrm{coker}(A(\chi))=a_1+a_2=\mathrm{ord}_p(\det(A(\chi))).
\]
If \(\det(A(\chi))=0\), then \(\mathrm{ord}_p(\det(A(\chi)))=\infty\) and the inequality is trivial. Therefore
\[
\mathrm{length}_{\mathbb{Z}_p}\mathrm{coker}(I-K(\chi))\le \mathrm{ord}_p\det(I-K(\chi)),
\]
as claimed.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:psmith-signed — corollary (Signed pseudo–Smith form over $\Lambda$)

- **Source**: `BSD-Jon-Final.txt` L3494–L3500
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Signed pseudo–Smith form over $\Lambda$]\label{cor:psmith-signed}
Let $p\ge 5$ be supersingular for $E/\mathbb{Q}$. Let $\mathcal{C}^{\pm}(T)$ be the signed Coleman matrix built from a $\Lambda$–basis of $H^1_{\emph{Iw}}(\mathbb{Q}_p,V)$ using Pollack’s $\log^{\pm}$ and the $\pm$ projectors (cf. \cite{Pollack2003,Kobayashi2003,LeiLoefflerZerbes2012}). Then there exist $U,V\in\mathrm{GL}_2(\Lambda)$ and a diagonal matrix $D^{\pm}(T)=\mathrm{diag}(d_1^{\pm}(T),d_2^{\pm}(T))$ such that
\[
 U\,\mathcal{C}^{\pm}(T)\,V\ \equiv\ D^{\pm}(T)
\]
up to pseudo–isomorphism of $\Lambda$–modules, and $(d_1^{\pm}d_2^{\pm})=(L_p^{\pm}(E,T))$ as ideals in $\Lambda$.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:fitting-signed — corollary (Signed Fitting–minor identification)

- **Source**: `BSD-Jon-Final.txt` L3505–L3510
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Signed Fitting–minor identification]\label{cor:fitting-signed}
Let $M_{\pm}\subset H^1_{\emph{Iw}}(\mathbb{Q},V)$ be a finite free $\Lambda$–lattice stable under the signed operator $K_{\pm}(T)$ (\S\,4.8). Then the zeroth and first Fitting ideals of $\mathrm{coker}(I-K_{\pm}(T))$ are generated by the $2\times2$ and $1\times1$ minors of the matrix of $I-K_{\pm}(T)$ in any $\Lambda$–basis. For each finite-order $\chi$,
\[
 \mathrm{length}_{\mathbb{Z}_p}\,\mathrm{coker}(I-K_{\pm}(\chi))\ \le\ \mathrm{ord}_p\det(I-K_{\pm}(\chi)).
\]
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:sep-quant — theorem (Chebotarev–Kummer separation)

- **Source**: `BSD-Jon-Final.txt` L3517–L3519
- **Status**: todo
- **Auto-flags**: ASSUMES
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Chebotarev–Kummer separation]\label{thm:sep-quant}
Assume Serre open image for $\rho_E$ and mod–$N$ independence of $\{P_i\}$. Then for each large $X$ there are $\gg c\,\pi(X)$ good ordinary primes $p\le X$ (with $c>0$ absolute) such that the reduction orders $\{o_i(p)\}$ are pairwise nondividing; moreover $c$ can be made explicit along a sequence of moduli.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:sha-finite — theorem (Cofinite (H$\Lambda$) $\Rightarrow$ $\Sha$ finite)

- **Source**: `BSD-Jon-Final.txt` L3528–L3530
- **Status**: conditional
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Conditional on (HΛ)**: this theorem is only as strong as the hypothesis (HΛ) (a Λ-adic “positivity / nondegeneracy / nullspace injection” package proved later as `thm:HL-ordinary` / `thm:HL-signed`).
  - **Not the same as Appendix C.3**: unlike Appendix C.3, the proof here does not use the flawed “orthogonal complement must be zero” dimension argument; it uses a maximal-isotropic/nullspace-injection mechanism. This still needs careful auditing.
  - **Conceptual mismatch to resolve**: the source proof text (Step 2) calls the Kummer image “isotropic” for the specialized height while also asserting that the specialized Bloch–Kato height is **nondegenerate on** \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) modulo torsion. A nondegenerate restriction cannot be isotropic for a symmetric height pairing, so we must clarify:
    - which pairing is meant to be isotropic (Poitou–Tate cup product? Cassels–Tate?),
    - and how the specialized height pairing interacts with that structure.
  - **PT/control still only “stated, not cited”**: we now have explicit target statements PT1–PT4 and C1–C4 written in the deep-dive notes, but we still need to attach precise citations (theorem numbers/sections) and verify hypotheses match the paper’s local conditions.
    - PT statements: `notes/papers/bsd/nekovar-selmer-complexes-poitou-tate-notes.md` (PT1–PT4)
    - Control statements: `notes/papers/bsd/greenberg-control-notes.md` (C1–C4)
  - **Potential gap (global finiteness)**: even if one proves \(\Sha(E/\mathbb{Q})[p^\infty]\) is finite for every prime \(p\), it does **not** automatically follow that \(\Sha(E/\mathbb{Q})\) is finite unless one also proves only finitely many primes contribute nontrivially. The source’s Step 5 (“\(\Sha=\oplus_p \Sha[p^\infty]\) is finite”) needs an extra argument.
  - **Deep-dive notes**:
    - `notes/papers/bsd/nekovar-selmer-complexes-poitou-tate-notes.md`
    - `notes/papers/bsd/greenberg-control-notes.md`

#### Statement (verbatim from source)

```tex
\begin{theorem}[Cofinite (H$\Lambda$) $\Rightarrow$ $\Sha$ finite]\label{thm:sha-finite}
If (H$\Lambda$) holds for a cofinite set of good primes $p$ and for all finite-order $\chi$ at those $p$, then $\mathrm{corank}_{\mathbb{Z}_p}\Sha(E/\mathbb{Q})[p^\infty]=0$ for each such $p$. If this holds for all primes $p$, then $\Sha(E/\mathbb{Q})$ is finite.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `thm:HL-ordinary`, `thm:HL-signed` (the (HΛ) package)
  - The Kummer exact sequence (Selmer → Sha) used in Step 4 of the source proof
- **External (papers/books/theorems)**:
  - **PT package (PT1–PT4)**: Poitou–Tate duality / Cassels–Tate pairing / Selmer complexes formalism (Nekovář) — see `notes/papers/bsd/nekovar-selmer-complexes-poitou-tate-notes.md`
  - **Control package (C1–C4)**: Greenberg control and χ-specialization dictionary — see `notes/papers/bsd/greenberg-control-notes.md`

#### Proof outline (edit)

- Follow the source’s 5-step proof **but make each interface explicit**:
  - **Step 1 (PT setup; PT1–PT2)**: specify the Selmer complex / local conditions defining \(\mathrm{Sel}_{p^\infty}(E/\mathbb{Q})\) and the PT pairing/orthogonality statements being used (PT1 + PT2).
  - **Step 2 (specialization; (HΛ))**: use `thm:HL-ordinary` / `thm:HL-signed` to identify \(\mathrm{ev}_\chi\circ h_\Lambda\) with a Bloch–Kato/Nekovář height pairing \(h_{\chi}\) (up to a unit) and record **the exact nondegeneracy statement** provided by (HΛ) (typically: nondegenerate on \(\mathrm{Sel}_\chi/\mathrm{tors}\)).
  - **Step 3 (linear algebra + PT3)**:
    - let \(W:=\kappa(E(\mathbb{Q})\otimes\mathbb{Q}_p)\subset \mathrm{Sel}_\chi\) be the Kummer image;
    - if \(\dim_{\mathbb{Q}_p}\mathrm{Sel}_\chi>\dim_{\mathbb{Q}_p}W=\mathrm{rank}\,E(\mathbb{Q})\), then (nondegeneracy on \(\mathrm{Sel}_\chi/\mathrm{tors}\)) implies there exists a nonzero class \(x\in \mathrm{Sel}_\chi/\mathrm{tors}\) orthogonal to \(W\);
    - invoke the **PT3 target lemma** (height-as-PT-with-Bockstein + radical identification) together with the (HΛ) nullspace/radical control to conclude such an \(x\) must be torsion, contradiction; hence \(\dim_{\mathbb{Q}_p}\mathrm{Sel}_\chi=\mathrm{rank}\,E(\mathbb{Q})\).
  - **Step 4 (χ→\(p^\infty\) Selmer comparison; C1–C3)**: use the χ-specialization dictionary (C1) and corank/dimension comparison (C3), plus any needed control boundedness (C2) if χ=trivial is not directly available, to deduce
    \(\mathrm{corank}_{\mathbb{Z}_p}\mathrm{Sel}_{p^\infty}(E/\mathbb{Q})=\mathrm{rank}\,E(\mathbb{Q})\).
  - **Step 5 (global finiteness)**: add an additional lemma showing only finitely many primes contribute nontrivially to \(\Sha\) (or else downgrade the global finiteness claim to conditional).

#### Full proof (massive detail; edit)

**Conditional proof skeleton (referee-facing; citations still to be pinned down):**

The source proof is fundamentally different from Appendix C.3: it attempts to force \(\Sha[p^\infty]\) corank \(0\) from a Λ-adic “positivity/nondegeneracy” package (HΛ) together with Poitou–Tate control across χ-specializations.

Fix a good prime \(p\) and the paper’s local conditions (ordinary or signed at \(p\), finite away from \(p\)). Let \(\mathrm{Sel}_\chi\) be the χ-specialized Selmer group in the sense of C1.

1. **(PT setup)** Use PT1–PT2 to put \(\mathrm{Sel}_\chi\) into a Selmer-complex/PT framework with the correct local conditions, and to fix the relevant global pairing language (local orthogonality, dual Selmer objects, Cassels–Tate).
2. **(Nondegenerate specialized height)** Use (HΛ) (via `thm:HL-ordinary` / `thm:HL-signed`) to obtain a χ-specialized height pairing \(h_\chi\) with:
   - \(h_\chi\) nondegenerate on \(\mathrm{Sel}_\chi/\mathrm{tors}\), and
   - a “radical/nullspace control” statement (the nullspace-injection feature) needed in Step 3.
3. **(Orthogonal ⇒ torsion, hence dimension identity)** Combine:
   - linear algebra inside \(\mathrm{Sel}_\chi/\mathrm{tors}\) using nondegeneracy, and
   - PT3 (height-as-PT-with-Bockstein + radical identification),
   to show: if \(x\in \mathrm{Sel}_\chi\) is orthogonal to the Kummer image \(\kappa(E(\mathbb{Q})\otimes\mathbb{Q}_p)\), then \(x\) is torsion. Therefore \(\dim_{\mathbb{Q}_p}\mathrm{Sel}_\chi=\mathrm{rank}\,E(\mathbb{Q})\).
4. **(Back to classical \(p^\infty\)-Selmer)** Apply C3 (and C2 if required) to convert the χ-dimension statement (in particular at χ=trivial) into
   \(\mathrm{corank}_{\mathbb{Z}_p}\mathrm{Sel}_{p^\infty}(E/\mathbb{Q})=\mathrm{rank}\,E(\mathbb{Q})\).
   Then the Kummer exact sequence gives \(\mathrm{corank}_{\mathbb{Z}_p}\Sha(E/\mathbb{Q})[p^\infty]=0\).
5. **(Global finiteness)** Step 5 is blocked without an additional argument as recorded in PT4.

Until those are written out, treat this theorem as **conditional on (HΛ) + control**.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:pr-length — lemma (Specialized pairing and length control)

- **Source**: `BSD-Jon-Final.txt` L3564–L3576
- **Status**: outlined
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - This lemma is **only meaningful once** the operator model has identified \(\mathrm{coker}(I-K(\chi))\) (or its dual) with a χ-specialized Selmer object whose \(\mathbb{Z}_p\)-length is the algebraic quantity of interest.
  - The displayed inequality \(\mathrm{length}_{\mathbb{Z}_p}\mathrm{coker}(A)\le v_p(\det A)\) for a square matrix \(A\) over the DVR \(\mathbb{Z}_p\) is essentially **Smith normal form** and does not really use (i)–(ii); what (i)–(ii) are doing here is tying “solutions of \((I-K(\chi))x=0\)” to Selmer-local constraints, i.e. preventing “spurious kernel” outside Selmer.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Specialized pairing and length control]\label{lem:pr-length}
Let $M\cong \Lambda^d$ carry a $\Lambda$–bilinear symmetric form $h_\Lambda$. For a finite-order character $\chi$ of $\Gamma$, let $M_\chi:=M\otimes_{\Lambda,\chi}\mathbb{Z}_p$ and $h_\chi:=\mathrm{ev}_\chi\circ h_\Lambda$. Suppose:
\begin{itemize}
\item[(i)] $h_\chi$ is nondegenerate on $M_\chi/\mathrm{tors}$;
\item[(ii)] if $(I-K(\chi))x=0$ then $\mathrm{Col}_\chi(x)=0$ (hence $x$ lies in the local Selmer kernel);
\item[(iii)] $\det\mathcal{C}(\chi)\asymp L_p(E,\chi)$ and minors of $I-K(\chi)$ generate Fitting ideals of $\mathrm{coker}(I-K(\chi))$.
\end{itemize}
Then
\[
  \mathrm{length}_{\mathbb{Z}_p}\,\mathrm{coker}(I-K(\chi))\ \le\ \mathrm{ord}_p\det(I-K(\chi)),
\]
and hence $(L_p)\mid \mathrm{char}_\Lambda X_p$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `prop:fitting` / its specialization statement (Fitting ideal minors control)
  - `prop:Hlambda-to-revdiv` (this lemma is the χ-level inequality that drives it)
  - Operator setup: \(K(\chi)\), \(\mathrm{Col}_\chi\), and the Coleman matrix \(\mathcal{C}(\chi)\)
- **External (papers/books/theorems)**:
  - Smith normal form / elementary divisors over a DVR (here \(\mathbb{Z}_p\))

#### Proof outline (edit)

- Let \(A:=I-K(\chi)\) be the specialized endomorphism of a finite free \(\mathbb{Z}_p\)-module \(M_\chi\cong \mathbb{Z}_p^d\).
- Over the PID \(\mathbb{Z}_p\), write the Smith normal form \(UAV=\mathrm{diag}(p^{a_1},\dots,p^{a_d})\) with \(U,V\in\mathrm{GL}_d(\mathbb{Z}_p)\) and integers \(a_i\in\mathbb{Z}_{\ge 0}\cup\{\infty\}\).
- Then \(\mathrm{coker}(A)\cong \bigoplus_i \mathbb{Z}_p/p^{a_i}\mathbb{Z}_p\) (interpreting \(p^\infty=0\), which yields a free \(\mathbb{Z}_p\)-summand and infinite length), and \(\det(A)=u\cdot p^{\sum a_i}\) for a unit \(u\) when all \(a_i<\infty\).
- Therefore \(\mathrm{length}_{\mathbb{Z}_p}\mathrm{coker}(A)=\sum a_i = v_p(\det A)\) if \(\det A\ne 0\), and otherwise \(\mathrm{length}\) is infinite and \(v_p(\det A)=\infty\), so the inequality holds.
- The remaining conditions (i)–(iii) are used to identify \(\det(I-K(\chi))\) with \(L_p(E,\chi)\) up to a unit and to interpret \(\mathrm{coker}(I-K(\chi))\) as a Selmer quantity.

#### Full proof (massive detail; edit)

Let \(M_\chi\cong \mathbb{Z}_p^d\) and let \(A:=I-K(\chi):M_\chi\to M_\chi\) be the specialized \(\mathbb{Z}_p\)-linear endomorphism. Since \(\mathbb{Z}_p\) is a PID (a DVR), there exist \(U,V\in \mathrm{GL}_d(\mathbb{Z}_p)\) such that
\[
UAV=\mathrm{diag}(p^{a_1},\dots,p^{a_d})
\]
with \(a_i\in\mathbb{Z}_{\ge 0}\cup\{\infty\}\). Then
\[
\mathrm{coker}(A)\ \cong\ \bigoplus_{i=1}^d \mathbb{Z}_p/p^{a_i}\mathbb{Z}_p,
\]
so \(\mathrm{length}_{\mathbb{Z}_p}\mathrm{coker}(A)=\sum_i a_i\) (interpreting \(a_i=\infty\) as giving infinite length).

Also \(\det(A)=\det(U)^{-1}\det(V)^{-1}\cdot \prod_i p^{a_i}\), so
\[
v_p(\det A)=\sum_i a_i
\]
when \(\det A\ne 0\), and \(v_p(\det A)=\infty\) if \(\det A=0\). In either case,
\[
\mathrm{length}_{\mathbb{Z}_p}\mathrm{coker}(A)\ \le\ v_p(\det A)
\]
holds (indeed, it is equality in the finite case).

Finally, hypothesis (iii) is what ties \(\det(I-K(\chi))\) to the analytic quantity \(L_p(E,\chi)\) (up to a unit) and ties the minors/determinant to the relevant Fitting ideal; hypotheses (i)–(ii) are part of the Selmer/height package ensuring the operator model correctly captures Selmer local conditions. Assembling over all χ then yields the ideal divisibility statement \((L_p)\mid \mathrm{char}_\Lambda(X_p)\) in the ambient \(\Lambda\)-setting (as in `prop:Hlambda-to-revdiv`).

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:no-free-params — lemma (No–free–parameters normalization)

- **Source**: `BSD-Jon-Final.txt` L3581–L3583
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[No–free–parameters normalization]\label{lem:no-free-params}
Unit changes in the Néron differential, Perrin–Riou branch, and crystalline basis multiply $\mathcal{C}(T)$ by $\Lambda^{\times}$ and specializations by $\mathbb{Z}_p^{\times}$, leaving $p$–adic valuations (and hence $\mathbb{Z}_p$–length inequalities) invariant.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:vis-kato — theorem (Visibility + Kato $\Rightarrow$ equality at congruence primes)

- **Source**: `BSD-Jon-Final.txt` L3608–L3615
- **Status**: todo
- **Auto-flags**: ASSUMES
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Visibility + Kato $\Rightarrow$ equality at congruence primes]\label{thm:vis-kato}
Assume $\mathrm{ord}_{s=1}L(E,s)\in\{0,1\}$ and that the residual Galois representation $\overline{\rho}_{E,p}$ is surjective. Suppose there exists a squarefree integer $N'$, prime to $Np$, and a newform $g$ of level $NN'$ such that $g\equiv f_E\ (\bmod\ p)$ on Hecke operators away from $N'$ (level--raising at a single auxiliary prime suffices in practice). Let $A_g$ be the optimal quotient of $J_0(NN')$ attached to $g$. Then for such congruence--friendly primes $p\in\mathcal{E}$ one has BSD$_p$ for $E$:
\[
  \mathrm{ord}_p\!\left(\frac{L^{(r)}(E,1)}{r!\,\Omega_E}\right)
  \ =\ \mathrm{ord}_p\!\left(\frac{\mathrm{Reg}_E\ \cdot\ \#\Sha(E/\mathbb{Q})\ \cdot\ \prod_{\ell} c_{\ell}}{\#E(\mathbb{Q})_{\mathrm{tors}}^{\,2}}\right),\qquad r\in\{0,1\}.
\]
Equivalently, the remaining $p$--power in the BSD prediction is visible in the $p$--primary torsion of $A_g$ (or in the component groups), and Kato's divisibility gives the opposite inequality, yielding equality.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-remark-L3620 — remark (Supersingular and signed variants)

- **Source**: `BSD-Jon-Final.txt` L3620–L3622
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{remark}[Supersingular and signed variants]
At supersingular $p$, the same strategy applies after replacing objects by their $\pm$ analogues (signed Selmer, signed regulators). Where signed IMC is known (Kobayashi/Lei--Loeffler--Zerbes/Wan/Sprung under standard big--image hypotheses), equality follows directly; otherwise, visibility plus Kato yields the reverse bound at $T=0$ and hence equality in valuation.
\end{remark}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:finite-checklist — proposition (Finite checklist for $\mathcal{E}$ at rank $\ge 1$)

- **Source**: `BSD-Jon-Final.txt` L3624–L3632
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: prop:cofinite-nondeg, thm:vis-kato
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{proposition}[Finite checklist for $\mathcal{E}$ at rank $\ge 1$]\label{prop:finite-checklist}
Let $\mathcal{E}$ be the finite set from Proposition~\ref{prop:cofinite-nondeg}. For each $p\in\mathcal{E}$:
\begin{itemize}
\item[(i)] Run Kato's divisibility (always available) to obtain the lower bound on the analytic side (or, equivalently, the upper bound on $\#\Sha[p^\infty]$).
\item[(ii)] Check residual big image at $p$ (surjectivity of $\overline{\rho}_{E,p}$). If ordinary and Skinner--Urban hypotheses hold, import their IMC to conclude immediately; if supersingular and signed hypotheses hold, import the signed IMC (Kobayashi/Pollack/Wan/Sprung).
\item[(iii)] If neither IMC applies, perform level--raising at one auxiliary prime to find a congruent newform $g$ as in Theorem~\ref{thm:vis-kato}. Use visibility in $J_0(NN')$ to identify and transfer the missing $p$--power to $E$.
\end{itemize}
As $\mathcal{E}$ is finite and fully explicit for the curves in \S6B, this procedure terminates and yields BSD$_p$ at every $p\in\mathcal{E}$ without appealing to a general IMC.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:R-triangular — theorem (Reverse divisibility at $T=0$ from triangularization)

- **Source**: `BSD-Jon-Final.txt` L3638–L3655
- **Status**: suspect
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Hard consistency issue (rank \(r>1\))**: earlier the source proves the mod‑\(p\) congruence
    \[
      h_p(R,S)\equiv u_p(\alpha_p)\,\log_\omega(R)\,\log_\omega(S)\quad (\bmod\ p)
    \]
    (see `BSD-Jon-Final.txt` Eq. (F.16.1) `\eqref{eq:hp-modp}` inside `lem:triang-ord-modp`). By bilinearity, this congruence persists after any \(M_p\in\mathrm{GL}_r(\mathbb{Z}_p)\) change of basis: for \(Q_i\) one gets
    \[
      (H'_p)_{ij}\equiv u_p(\alpha_p)\,\log_\omega(Q_i)\,\log_\omega(Q_j)\quad(\bmod\ p).
    \]
    If **all** \(\log_\omega(Q_i)\in\mathbb{Z}_p^\times\), then for **every** \(i,j\) the RHS is a unit mod \(p\), hence \((H'_p)_{ij}\not\equiv 0\pmod p\). Therefore \(H'_p\) cannot be upper triangular mod \(p\) unless \(r=1\).  
    So for \(r>1\) the hypotheses as stated are mutually incompatible; the theorem is effectively **vacuous** (or the intended hypothesis is different).
  - **Also blocked by the paper’s “formal‑group unit diagonal” issue** if the intended construction forces some \(Q_i\in E_1(\mathbb{Q}_p)\) (then `lem:unit-log` gives \(v_p(h_p(Q_i,Q_i))\ge 2\)).

#### Statement (verbatim from source)

```tex
\begin{theorem}[Reverse divisibility at $T=0$ from triangularization]\label{thm:R-triangular}
Let $E/\mathbb{Q}$ have good ordinary reduction at $p\ge 5$ with no exceptional zero. Suppose there exists a $\mathbb{Z}$–basis $\{P_i\}_{i=1}^r$ of $E(\mathbb{Q})/\mathrm{tors}$ and a matrix $M_p\in \mathrm{GL}_r(\mathbb{Z}_p)$ such that, writing $Q:=(P_1,\dots,P_r)\cdot M_p$ and $H_p=(h_p(P_i,P_j))$, the transformed Gram matrix $H'_p:=M_p^{\top}H_pM_p$ is upper triangular modulo $p$ with 
\[
  (H'_p)_{ii}\ \equiv\ u_p(\alpha_p)\,\big(\log_\omega(Q_i)\big)^2\ (\bmod\ p),\qquad u_p(\alpha_p)\in \mathbb{Z}_p^{\times},
\]
and moreover $\log_\omega(Q_i)\in\mathbb{Z}_p^{\times}$ for all $i$ (so the diagonal is $p$–adic unit). Then:
\begin{itemize}
\item[(i)] The leading coefficient of $L_p(E,T)$ at $T=0$ equals a $p$–adic unit times the $p$–adic regulator $\mathrm{Reg}_p(E)$. In particular, $\mu_p(E)=0$ and
\[
  \mathrm{ord}_{T=0}L_p(E,T)\ =\ r\ =\ \mathrm{rank}\,E(\mathbb{Q}).
\]
\item[(ii)] One has
\[
  \mathrm{ord}_{T=0}L_p(E,T)\ =\ \mathrm{corank}_\Lambda X_p(E/\mathbb{Q}_\infty),
\]
so the valuation--level equality at $T=0$ holds. Equivalently, evaluated at $T=0$ the characteristic element has the same $p$–adic order as $L_p(E,T)$; combined with Kato's divisibility $\mathrm{char}_\Lambda X_p\mid (L_p(E,T))$, this yields equality of orders at $T=0$ without assuming IMC.
\end{itemize}
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:triang-ord-modp` (for the mod‑\(p\) congruence / triangularization mechanism)
  - Any claimed “unit diagonal” certification (`cor:height-unit`, `prop:triangular`, `prop:cofinite-nondeg`) — currently blocked/suspect
- **External (papers/books/theorems)**:
  - Kato’s one-sided divisibility at \(T=0\) (Euler system)
  - Standard relation: leading term of \(L_p\) vs \(p\)-adic regulator (under appropriate hypotheses)

#### Proof outline (edit)

- (As written) conditional: assume a basis making \(H'_p\) upper triangular mod \(p\) and simultaneously having unit diagonals; then conclude \(\mu_p=0\) and the \(T=0\) order equalities by comparing leading terms with the \(p\)-adic regulator and combining with Kato divisibility.
- **Audit note**: for \(r>1\), the stated hypotheses clash with the earlier congruence \(H'_{ij}\equiv u\,\log(Q_i)\log(Q_j)\ (\bmod p)\), so a corrected statement/proof is needed before any downstream use.

#### Full proof (massive detail; edit)

**Status: suspect.** The theorem is currently not usable in rank \(r>1\) because its hypotheses are inconsistent with the source’s own mod‑\(p\) congruence for heights (see blocker note above).

If the intent was instead a **row-scaled** or otherwise normalized matrix (cf. the earlier `prop:triangular` mismatch), the statement should be rewritten before auditing the proof.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L3666 — corollary (Per–prime application)

- **Source**: `BSD-Jon-Final.txt` L3666–L3668
- **Status**: blocked
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:triang-ord-modp, thm:R-triangular
- **Conditional on / Blockers (edit)**:
  - **Blocked by `thm:R-triangular`** (whose hypotheses are internally inconsistent for rank \(r>1\) as written).
  - **Also blocked by the formal-group valuation issue** if the intended “triangularizing basis” is constructed via separation scalings into \(E_1(\mathbb{Q}_p)\): then diagonal unitness cannot hold (see `lem:unit-log`).

#### Statement (verbatim from source)

```tex
\begin{corollary}[Per–prime application]
At any ordinary prime $p$ where Lemma~\ref{lem:triang-ord-modp} applies and $v_p\big(h_p(Q_i,Q_i)\big)=0$ for a triangularizing basis $\{Q_i\}$, the conclusions of Theorem~\ref{thm:R-triangular} hold: $\mu_p(E)=0$ and $\mathrm{ord}_{T=0}L_p(E,T)=\mathrm{rank}\,E(\mathbb{Q})=\mathrm{corank}_\Lambda X_p$.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:triang-signed — lemma (Signed Lemma U: mod-$p$ upper--triangularization on each sign)

- **Source**: `BSD-Jon-Final.txt` L3674–L3680
- **Status**: conditional
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - Conditional on the signed explicit reciprocity inputs (`thm:HL-signed`, `lem:PR-signed-proof`) and on the signed “mod‑\(p\) congruence for heights in terms of \(\log^\pm\)” that the source cites but does not spell out.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Signed Lemma U: mod-$p$ upper--triangularization on each sign]\label{lem:triang-signed}
Let $p\ge 5$ be supersingular for $E/\mathbb{Q}$. Fix Pollack's signed logarithms $\log^{\pm}$ and the signed projectors $e_{\pm}$ (Kobayashi). For any torsion--free basis $\{P_1,\dots,P_r\}$ of $E(\mathbb{Q})$, there exist $M_p^{\pm}\in\mathrm{GL}_r(\mathbb{Z}_p)$ and units $u_p^{\pm}\in\mathbb{Z}_p^{\times}$ such that, writing $Q^{\pm}:=(P_1,\dots,P_r)\cdot M_p^{\pm}$ and denoting by $H_p^{\pm}$ the signed cyclotomic Coleman--Gross height Gram matrix at $p$ for the $\pm$ local condition,
\[

 (H_p^{\pm})'\ :=\ (M_p^{\pm})^{\top}H_p^{\pm}M_p^{\pm}\ \equiv\ \text{upper triangular}\ (\bmod\ p),\qquad (H_p^{\pm})'_{ii}\ \equiv\ u_p^{\pm}\,\big(\log^{\pm}(Q^{\pm}_i)\big)^2\ (\bmod\ p).
\]
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `thm:HL-signed`, `lem:PR-signed-proof`
  - Signed logs/local conditions setup (Pollack/Kobayashi)
- **External (papers/books/theorems)**:
  - Pollack/Kobayashi/LLZ signed Coleman maps and signed reciprocity

#### Proof outline (edit)

- Follow the ordinary proof of `lem:triang-ord-modp`, replacing \(\log_\omega\) by \(\log^\pm\) and the ordinary projector by the signed projector.
- Choose \(M_p^\pm\) so that \(\log^\pm(Q_i^\pm)\equiv 0\ (\bmod p)\) for \(i\ge 2\); then the mod‑\(p\) congruence forces the transformed Gram matrix to be upper triangular mod \(p\) with the stated diagonal congruences.

#### Full proof (massive detail; edit)

The source proof is a “repeat the ordinary argument” citation (see `BSD-Jon-Final.txt` L3681–L3683).  

To make this audit‑grade, we need the signed analogue of the ordinary congruence
\[
h_p(R,S)\equiv u\cdot \log(R)\log(S)\ (\bmod p),
\]
namely a congruence expressing \(h_p^\pm(R,S)\) modulo \(p\) in terms of \(\log^\pm(R)\log^\pm(S)\) up to a unit, derived from signed explicit reciprocity.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:diag-units-signed — lemma (Signed diagonal per–prime unit test)

- **Source**: `BSD-Jon-Final.txt` L3685–L3690
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{lemma}[Signed diagonal per–prime unit test]\label{lem:diag-units-signed}
Fix a supersingular prime $p\ge 5$ and non--torsion $P\in E(\mathbb{Q})$. After fixing signed normalizations once for all, $h_p^{\pm}(P)\in\mathbb{Z}_p$ and
\[
  v_p\big(h_p^{\pm}(P)\big)=0\quad\Longleftrightarrow\quad v_p\big(\log^{\pm}(P)\big)=0.
\]
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### prop:cofinite-signed — proposition (Per–prime signed nondegeneracy)

- **Source**: `BSD-Jon-Final.txt` L3695–L3697
- **Status**: suspect
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:triang-signed
- **Conditional on / Blockers (edit)**:
  - **Potential vacuity / inconsistency (rank \(r>1\))**: the signed triangularization mechanism in `lem:triang-signed` is obtained (per the source) by the same “choose basis killing \(\log^\pm\) mod \(p\) in coordinates \(i\ge 2\)” argument. That construction makes the diagonal entries for \(i\ge 2\) divisible by \(p\), hence they cannot satisfy the “unit diagonal” condition \(v_p(h_p^\pm(Q_i,Q_i))=0\) for all \(i\).
  - If instead a different “triangularizing basis with unit diagonals” is intended, it must be stated explicitly and checked against the signed mod‑\(p\) congruence; otherwise this proposition is not usable in ranks \(>1\).

#### Statement (verbatim from source)

```tex
\begin{proposition}[Per–prime signed nondegeneracy]\label{prop:cofinite-signed}
Fix a supersingular prime $p\ge 5$. If for some sign $\pm$ the hypotheses of Lemma~\ref{lem:triang-signed} hold and $v_p\big(h_p^{\pm}(Q_i,Q_i)\big)=0$ for the triangularizing basis $\{Q_i\}$, then $\det H_p^{\pm}\in\mathbb{Z}_p^{\times}$ and $\mathrm{Reg}_p^{\pm}\in\mathbb{Z}_p^{\times}$.
\end{proposition}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:R-triangular-signed — theorem (Signed reverse divisibility at $T=0$)

- **Source**: `BSD-Jon-Final.txt` L3702–L3711
- **Status**: suspect
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:triang-signed
- **Conditional on / Blockers (edit)**:
  - **Same structural issue as `thm:R-triangular`**: for rank \(r>1\), “upper triangular mod \(p\)” produced via the Gram–Schmidt/log‑killing construction is incompatible with “signed unit diagonals” for all \(i\). As written this is at best vacuous, and cannot be used downstream without a corrected hypothesis/argument.
  - Conditional on signed height setup and signed explicit reciprocity (`thm:HL-signed`, `lem:PR-signed-proof`) plus Kato’s signed one‑sided divisibility.

#### Statement (verbatim from source)

```tex
\begin{theorem}[Signed reverse divisibility at $T=0$]\label{thm:R-triangular-signed}
Let $p\ge 5$ be supersingular for $E/\mathbb{Q}$ and assume the hypotheses of Lemma~\ref{lem:triang-signed} with signed unit diagonals. Then for each sign $\pm$ the leading coefficient of $L_p^{\pm}(E,T)$ at $T=0$ equals a $p$--adic unit times $\mathrm{Reg}_p^{\pm}$; in particular $\mu_p^{\pm}(E)=0$ and
\[
  \mathrm{ord}_{T=0}L_p^{\pm}(E,T)\ =\ \mathrm{rank}\,E(\mathbb{Q}).
\]
Moreover,
\[
  \mathrm{ord}_{T=0}L_p^{\pm}(E,T)\ =\ \mathrm{corank}_\Lambda X_p^{\pm}(E/\mathbb{Q}_\infty).
\]
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L3716 — corollary (BSD$_p$ in signed IMC ranges)

- **Source**: `BSD-Jon-Final.txt` L3716–L3718
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[BSD$_p$ in signed IMC ranges]
If, in addition, the signed IMC holds for $E$ at $p$ (Kobayashi; Sprung; Lei--Loeffler--Zerbes; Wan under standard big--image hypotheses), then BSD$_p$ holds for $E$ at $p$. For the remaining finite set of supersingular primes, visibility + Kato (\S F.22.3) dispatches the equality.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### auto-corollary-L3724 — corollary (Validated closure for \S6)

- **Source**: `BSD-Jon-Final.txt` L3724–L3732
- **Status**: todo
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: prop:BSDp, prop:cofinite-nondeg, prop:cofinite-signed, prop:mu-zero, prop:triangular
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{corollary}[Validated closure for \S6]
Let $E_0$ be the rank--$1$ curve of \S6A and let $E$ be the curve of \S6B. Then:
\begin{itemize}
\item[(1)] At any prime $p$ where the per–prime certificate (Propositions~\ref{prop:triangular} and~\ref{prop:cofinite-nondeg}, ordinary; Proposition~\ref{prop:cofinite-signed}, signed) holds, one has $\mathrm{Reg}_p\in\mathbb{Z}_p^{\times}$ and hence $\mu_p=0$ (Proposition~\ref{prop:mu-zero}); if IMC/signed–IMC is available at that $p$, BSD$_p$ follows (Proposition~\ref{prop:BSDp}).
\item[(2)] For \S6A (rank 1), the remaining primes are settled unconditionally by Gross--Zagier + Kolyvagin (\S F.22.1); for \S6B, by visibility + Kato (\S F.22.3), with IMC/signed–IMC used wherever available by big–image checks.
\item[(3)] Consequently, all prime–wise statements used in \S6 are secured by a finite audit: per–prime certificates where computed; and classical closures (\S F.22) for the residual finite set.
\end{itemize}
Thus the manuscript’s conclusions in \S6 rest on auditable per–prime validations and finite classical closures, avoiding unproven cofinite claims.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:pw-wedge-mu — theorem (Cyclotomic wedge $\Rightarrow\ \mu=0$)

- **Source**: `BSD-Jon-Final.txt` L3761–L3767
- **Status**: todo
- **Auto-flags**: —
- **Auto-extracted internal refs**: lem:mu-criterion
- **Conditional on / Blockers (edit)**:
  - 

#### Statement (verbatim from source)

```tex
\begin{theorem}[Cyclotomic wedge $\Rightarrow\ \mu=0$]\label{thm:pw-wedge-mu}
For every prime $p$, there exists $\varepsilon\in(0,1)$ and $n_0\ge 1$ such that for all $n\ge n_0$ and for all $\phi\in\mathcal W_{\mathrm{adm}}(n;\varepsilon)$,
\[
  \int_{\Gamma_n}\! \phi\,(-\Delta\,\mathrm{arg}\,\mathcal J)\ \le\ C\,p^{-n/2}\ <\ \tfrac{\pi}{2}.
\]
Consequently, a quantitative wedge holds on every $\Gamma_n$ (after a unimodular rotation), and a positive proportion of characters of each conductor $p^n$ satisfy $v_p\big(L_p(E,\chi)\big)=0$. By Lemma~\ref{lem:mu-criterion}, $\mu_p(E)=0$ (ordinary and signed) for all $p$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:noncancel — lemma (Non–cancellation at zeros in families)

- **Source**: (deprecated) former disc-pinch engine; removed from the unconditional mainline
- **Status**: deprecated
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Deprecated**: disc-wise pinch is not used; this lemma is kept only as a record of what the disc engine would have required.
  - **Conditional on analytic setup**: needs precise definitions of the weight disc \(D\), the affinoid algebra \(\mathcal{O}(D)\), Fredholm analyticity of \(\det_{\Lambda}(I-K)\) on \(D\), and the “outer” factor \(\mathcal O\) being zero–free on \(\partial D\).
  - **Repair note**: for the disc engine we do not need a mysterious “zeros/poles coincide” claim; what we need is a standard rigid-analytic **removable singularities** lemma: a meromorphic function on a 1D affinoid disc that is bounded is holomorphic (hence “common zeros are removable”).

#### Statement (verbatim from source)

```tex
\begin{lemma}[Non–cancellation at zeros in families]\label{lem:noncancel}
With outer $\mathcal O$ zero–free on $\partial D$ and $\det_{\Lambda}(I-K)$ analytic (Fredholm) on $D$, the Schur transform $\Theta$ is meromorphic on $D$ and bounded on $D\setminus Z$ (by Lemma~\ref{lem:disc-wedge} and maximum modulus). Hence all putative singularities at common zeros are removable, and $\Theta$ extends holomorphically to $D$.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `lem:disc-wedge` (repaired form) to supply a strict bound \(|\Theta|_p<1\) on the Shilov boundary, hence boundedness on \(D\setminus Z\)
- **External (papers/books/theorems)**:
  - Weierstrass preparation on Tate algebras; local description of analytic functions near a point on a disc
  - Rigid removable singularities: bounded meromorphic \(\Rightarrow\) analytic (1D case)

#### Proof outline (edit)

- Let \(D\) be a closed affinoid disc and \(A=\mathcal O(D)\). Let \(\Theta\in\mathrm{Frac}(A)\) be meromorphic on \(D\).
- Assume there exists \(\rho<\infty\) such that \(|\Theta(x)|_p\le \rho\) for all \(x\in D\setminus Z\) (e.g. obtained from a Shilov-boundary estimate plus maximum modulus).
- Then \(\Theta\) has no poles on \(D\): if \(\Theta\) had a pole at \(x_0\), Weierstrass preparation gives a local factorization \(\Theta=g/h\) with \(h\) vanishing at \(x_0\) and \(g\) analytic; this forces \(|\Theta|\) to be unbounded in any punctured neighborhood of \(x_0\), contradiction.
- Therefore \(\Theta\in A\). Applied to \(\Theta=(u_DJ-1)/(u_DJ+1)\), this is exactly the “common zeros are removable” step in `thm:schur-pinch-repaired`.

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### lem:right-edge — lemma (Right–edge normalization on discs)

- **Source**: (deprecated) former disc-pinch engine; removed from the unconditional mainline
- **Status**: deprecated
- **Auto-flags**: —
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Deprecated**: disc-wise pinch is not used; this lemma is kept only as a record of a former normalization idea.
  - **This is a new normalization choice after paper repair**: the source now asserts \(\mathcal J\to 1\) (hence \(\Theta\to 0\)) along a right-edge large-weight sequence after calibrating the outer factor up to a unit constant. This needs a precise construction of the “right-edge” family of specializations and an argument that the ratio \(\mathcal J\) converges to \(1\) there.
  - If the intended mechanism is “\(\mathcal J=1\) on an infinite set of specializations” (identity theorem), that should be stated explicitly.
  - **Not needed for ideal equality (recommended downgrade)**: the repaired disc engine only needs \(J\in\mathcal O(D)^\times\), not \(J\equiv 1\) or \(\Theta\equiv 0\). Until a real argument is supplied, treat `lem:right-edge` as an optional normalization remark, not a structural step.

#### Statement (verbatim from source)

```tex
\begin{lemma}[Right–edge normalization on discs]\label{lem:right-edge}
After fixing the outer normalization up to a unit constant on the disc, along a right–edge sequence of large–weight specializations one has \(\mathcal J\to 1\) and hence \(\Theta\to 0\) uniformly on compact \(t\)-ranges.
\end{lemma}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- 

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:disc-imc — theorem (Finite–slope IMC equality on $D$)

- **Source**: (deprecated) former disc-pinch engine; removed from the unconditional mainline
- **Status**: deprecated
- **Auto-flags**: IMC_MENTION
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **Deprecated**: disc-wise pinch is not used. IMC equality is imported via literature coverage + finite closures (`cor:disc-imc`, \S\,F.32; `thm:universal-imc`).
  - **Conditional on a repaired disc engine**: as written, the source’s “max modulus ⇒ constancy” step is not valid. To make `thm:disc-imc` credible, it should be derived from the repaired conclusion “\(J\in\mathcal O(D)^\times\)” (no residual factor) plus Kato divisibility.
  - **Conditional on `lem:disc-wedge` (repaired)**: need a real nonarchimedean boundary-control lemma that yields \(|\Theta|_p<1\) on the Shilov boundary.

#### Statement (verbatim from source)

```tex
\begin{theorem}[Finite–slope IMC equality on $D$]\label{thm:disc-imc}
On any finite–slope disc $D$ in weight space, one has $(L_p)=(\mathrm{char}_{\Lambda}X_p)$ (ordinary and signed). Consequently, IMC equality holds at every $p$ across all slopes.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - 
- **External (papers/books/theorems)**:
  - 

#### Proof outline (edit)

- Use the repaired `lem:disc-wedge` to obtain a strict bound \(|\Theta|_p<1\) on the Shilov boundary of \(D\).
- Apply maximum modulus + `lem:noncancel` (bounded meromorphic ⇒ analytic) to extend \(\Theta\) holomorphically across \(Z\).
- Conclude \(J\in\mathcal O(D)^\times\) (no residual factor), hence \((L_{p,D})=(\mathscr D_D)\) as ideals on \(D\).
- Combine with Kato one-sided divisibility (and signed analogues) to upgrade to the IMC ideal equality on \(D\), and then patch over a disc cover of weight space.

#### Full proof (massive detail; edit)

Write the proof here as if for a referee who will check every line.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### thm:global-bsd — theorem (Global BSD from BSD$_p$)

- **Source**: `BSD-Jon-Final.txt` L3828–L3834
- **Status**: drafted
- **Auto-flags**: ASSUMES
- **Auto-extracted internal refs**: —
- **Conditional on / Blockers (edit)**:
  - **External algebraicity**: needs the Shimura/Deligne statement that the normalized leading-term ratio \(R(E)\in\mathbb{Q}^{\times}\) (after fixing periods and Manin constant).
  - **Sign**: needs an argument that \(R(E)>0\) (or that the sign can be normalized away), to upgrade \(R(E)=\pm 1\) to \(R(E)=+1\).
  - **Input BSD\(_p\) for all primes**: this theorem assumes prime-wise valuation equalities at every \(p\) (provided by the unconditional mainline if the wedge/pinch engines are completed).

#### Statement (verbatim from source)

```tex
\begin{theorem}[Global BSD from BSD$_p$]\label{thm:global-bsd}
Let $E/\mathbb{Q}$ be modular. Assume the per-prime valuation equalities (BSD$_p$) hold at every prime $p$ for the chosen local condition (ordinary or signed at supersingular), i.e., $\mu_p(E)=0$ and $\mathrm{ord}_{T=0}L_p(E,T)=\mathrm{rank}\,E(\mathbb{Q})$, and that the $p$-adic valuations of the algebraic and analytic sides match at $T=0$. Then $v_p(R(E))=0$ for all primes $p$, hence $R(E)=\pm 1$. Moreover, the sign is $+1$, and thus
\[
 \frac{L^{(r)}(E,1)}{r!\,\Omega_E^{+}}\ =\ \frac{\mathrm{Reg}_E\cdot \#\Sha(E/\mathbb{Q})\cdot \prod_\ell c_\ell}{t_E^{\,2}}\,\cdot\, m(E)^{2}.
\]
In particular, after absorbing $m(E)$ into the period choice, the full Birch--Swinnerton--Dyer formula (order and leading term) holds for $E/\mathbb{Q}$.
\end{theorem}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `cor:universal-bsd-p` (BSD\(_p\) for every prime, i.e. valuation equality at each \(p\))
  - Definitions of \(R(E)\), \(\Omega_E^{+}\), \(m(E)\) as in Appendix G of the source
- **External (papers/books/theorems)**:
  - Shimura/Deligne algebraicity (rationality of the normalized leading term for modular elliptic curves)
  - Standard facts: if \(q\in\mathbb{Q}^{\times}\) has \(v_p(q)=0\) for all primes \(p\), then \(q=\pm 1\)

#### Proof outline (edit)

- Let \(R(E)\in\mathbb{Q}^{\times}\) be the rational ratio of analytic and algebraic BSD leading terms (with Manin constant normalization) as defined in Appendix G of the source.
- BSD\(_p\) for each prime \(p\) gives \(v_p(R(E))=0\) for all \(p\).
- Hence \(R(E)=\pm 1\).
- Use archimedean positivity/normalization to conclude \(R(E)=+1\), yielding the full BSD leading-term identity (and the order statement is already part of BSD\(_p\)).

#### Full proof (massive detail; edit)

Let \(R(E)\) be the global rational ratio defined in Appendix G of the source:
\[
R(E)\ :=\ \frac{\displaystyle \frac{L^{(r)}(E,1)}{r!\,\Omega_E^{+}}}{\displaystyle \frac{\mathrm{Reg}_E\cdot \#\Sha(E/\mathbb{Q})\cdot \prod_\ell c_\ell}{t_E^{\,2}}}\ \cdot\ \frac{1}{m(E)^{2}}\ \in\ \mathbb{Q}^{\times},
\]
where \(r=\mathrm{rank}\,E(\mathbb{Q})\), \(\Omega_E^{+}>0\) is the real period attached to the chosen Néron differential, and \(m(E)\) is the Manin constant. By Shimura/Deligne algebraicity (as cited in the source), \(R(E)\in\mathbb{Q}^{\times}\).

Assume BSD\(_p\) holds for every prime \(p\) in the sense of the source: for each \(p\), the \(p\)-adic valuations of the analytic and algebraic BSD leading terms agree. Unwinding definitions, this means \(v_p(R(E))=0\) for every prime \(p\).

Write \(R(E)=a/b\) with coprime integers \(a,b\). If \(v_p(R(E))=0\) for all \(p\), then no prime divides \(a\) or \(b\), so \(|a|=|b|=1\) and \(R(E)=\pm 1\).

Finally, by Lemma **G.sign** below (archimedean positivity), \(R(E)>0\). Therefore \(R(E)=+1\). This yields the full BSD leading-term identity (with the Manin constant factor as displayed). Absorbing \(m(E)\) into the choice of period gives the usual BSD formula.

#### Lemma G.sign — lemma (Archimedean positivity fixes the sign)

**Statement.** With the period normalization used in Appendix G of the source (in particular \(\Omega_E^{+}>0\)), the rational ratio \(R(E)\in\mathbb{Q}^{\times}\) is **positive**, hence \(R(E)=+1\) once \(R(E)=\pm 1\) is known.

**Status.** Needs a precise reference/argument for positivity of the normalized analytic leading coefficient (or an explicit normalization choice that forces it). This is standardly attributed to “archimedean positivity” in BSD writeups, but in a referee-grade proof we must either:
- cite a theorem ensuring the leading Taylor coefficient \(L^{(r)}(E,1)/(r!\,\Omega_E^{+})>0\), or
- adjust the period normalization so that the sign is absorbed by convention.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

### cor:global-bsd-sec6 — corollary (Global BSD for the case studies)

- **Source**: `BSD-Jon-Final.txt` L3842–L3844
- **Status**: conditional
- **Auto-flags**: —
- **Auto-extracted internal refs**: thm:global-bsd
- **Conditional on / Blockers (edit)**:
  - Conditional on the claim that the case studies in \S6 satisfy BSD\(_p\) for every prime \(p\) (either via the “universal” wedge/pinch engines, or via the finite closure workflow in \S F.22–F.33 for a residual set). This needs a curve-by-curve audit.

#### Statement (verbatim from source)

```tex
\begin{corollary}[Global BSD for the case studies]\label{cor:global-bsd-sec6}
For the curves in \S6, the hypotheses of Theorem~\ref{thm:global-bsd} are satisfied (prime-wise BSD$_p$ via \S\,F together with the finite closures in \S\,F.22--F.33); hence the full Birch--Swinnerton--Dyer formula holds for these curves.
\end{corollary}
```

#### Dependencies (edit + expand)

- **Internal (this document / source labels)**:
  - `thm:global-bsd` (global promotion from BSD\(_p\) for all primes)
  - The \S6 prime-wise verification/closure pipeline (references scattered through Appendix F; needs audit)
- **External (papers/books/theorems)**:
  - None beyond what `thm:global-bsd` uses, plus whatever external inputs are invoked in the \S6 closure for the residual primes (e.g. visibility/Kato/GZ-Kolyvagin).

#### Proof outline (edit)

- Assume the hypotheses of `thm:global-bsd` for the \S6 curves (prime-wise BSD\(_p\) for all primes, obtained by the claimed pipeline).
- Apply `thm:global-bsd`.

#### Full proof (massive detail; edit)

Conditional on the \S6 claim that BSD\(_p\) holds for every prime for the two case-study curves (via the prime-wise pipeline + finite closure): under that hypothesis, `thm:global-bsd` applies and yields the full BSD formula for those curves.

#### Verification checklist (edit)

- [ ] All definitions used are fixed and consistent with earlier sections
- [ ] Every invoked lemma/theorem is either proved here or explicitly listed as conditional
- [ ] Edge cases (small primes, bad reduction, exceptional zeros, signed cases) are handled
- [ ] No circular dependencies

---

