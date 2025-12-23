## \(\mu=0\) Closure (Cyclotomic Iwasawa) — Dream Theorems + Execution Doc

This document is an **actionable spec** for closing the cyclotomic \(\mu=0\) gap **classically** (i.e. in standard mathematics, not assuming Recognition/RS).

It is written to be executed against: each section ends in a **checklist** of concrete deliverables (citations, lemmas, definitions, or computations) that either closes a sub-goal or proves it is currently out of reach.

---

## Context: what is blocked, exactly?

In the BSD proof-track, the \(\mu=0\) pivot was refactored to the correct criterion:

- \(\mu_p(E)=0\) for a fixed prime \(p\) is equivalent to **primitivity** of the relevant analytic \(p\)-adic \(L\)-function:
  \[
    p\nmid L_p(E,T)\ \text{ in }\ \Lambda=\mathbb{Z}_p\llbracket T\rrbracket
    \quad\Longleftrightarrow\quad
    L_p(E,T)\not\equiv 0 \pmod p.
  \]

The hard part is not the criterion, but the **all-\(p\)** existence of a primitivity witness for a fixed non-CM curve \(E/\mathbb{Q}\):

- **Blocked node (Fpμ-2)**: produce, for each good ordinary \(p\), some cyclotomic character \(\chi\) such that
  \[
    v_p(L_p(E,\chi))<1,
  \]
  or equivalently \(L_p(E,T)\not\equiv 0 \pmod p\).

Known literature (GV00/EPW06) mostly uses \(\mu=0\) as an **input** to propagate invariants, not as a general **output**.

---

## The goal: a new theorem with the right “shape”

To close \(\mu=0\) classically, we need a theorem that turns “\(p\mid L_p(E,T)\)” into “\(p\mid C(E)\)” for some **fixed integer** \(C(E)\neq 0\) depending only on \(E\). Then finiteness across \(p\) is immediate.

There are two viable “dream shapes”:

1) **Congruence/period ideal controls μ** (Dream Theorem A)
2) **Uniform mod-\(p\) nonvanishing among cyclotomic twists** (Dream Theorem B)

These are not mutually exclusive; B can imply A in some formulations.

---

## Execution status (current)

This doc is being “executed” against what we can actually fetch and cite in this repo.

- **Working choice of \(C(E)\)**: the **(Wiles) congruence ideal / congruence number** attached to the weight‑2 newform \(f\) of \(E\). This is the cleanest “single integer” candidate that plausibly controls all period/congruence denominators.
- **Local sources already pulled into this repo**:
  - `tmp/arxiv/2111.14304/sym-square-rms-v6.tex` (Ray–Sujatha–Vatsal, `arXiv:2111.14304`): explicit “canonical period = Petersson / congruence number” normalization (see Eq. `\eqref{canonical period def}` in that source, and their definition \(\eta_f=(f,f)_N\)).
  - `tmp/numdam/diamond1989.pdf` + `tmp/numdam/diamond1989.txt` (Diamond, Compositio 1989): foundational congruence-module technology for \(\Lambda\)-adic forms (open Numdam scan).
- **Current missing bridge (Dream A core)**: a theorem (or internal proof) that genuinely connects
  \[
    p \mid L_p(E,T)\quad\Rightarrow\quad p \mid C(E)
  \]
  for the *cyclotomic* \(L_p\) of \(E\). The literature strongly suggests this should be true via “integral modular symbols + congruence modules”, but we do **not** yet have a theorem-number citation proving it in the cyclotomic setting.

## Dream Theorem A — “\(\mu\) is supported on primes dividing a fixed congruence/period integer”

### Statement (target)

Let \(E/\mathbb{Q}\) be a modular elliptic curve of conductor \(N\), and let \(f\) be the associated weight‑2 newform.

There exists an integer \(C(E)\in\mathbb{Z}\setminus\{0\}\) (explicitly definable from the modular parametrization / congruence module / canonical periods) such that:

- For every good ordinary prime \(p\nmid C(E)\),
  \[
    \mu^{\mathrm{an}}_p(E)=0
    \quad\text{(equivalently } p\nmid L_p(E,T)\text{ in }\mathbb{Z}_p\llbracket T\rrbracket\text{).}
  \]

Equivalently,
\[
  p\mid L_p(E,T)\ \Longrightarrow\ p\mid C(E).
\]

### Why this would close the game

Since \(C(E)\) has finitely many prime divisors, this gives **all-but-finitely-many \(p\)** cyclotomic \(\mu=0\) for the fixed curve \(E\).

Combined with the fixed-\(p\) certificate (\(L_p\not\equiv 0\bmod p\)), one reduces the global issue to a **finite set** of primes.

### Candidate definitions for \(C(E)\)

We need a definition that is:

- **Intrinsic** (independent of choices up to units),
- **Integral** (lives in \(\mathbb{Z}\) or in a number field with a canonical \(\mathbb{Z}\)-model),
- **Linked to \(p\)-adic \(L\)-function integrality**.

Concrete candidates to try (ordered by “likely to exist in the literature”):

1. **Congruence number / congruence ideal**
   - \(C(E)\) = (a generator of) the congruence ideal of the Hecke algebra at \(f\).
   - Often written via the module of congruences between \(f\) and the orthogonal complement.

2. **Canonical periods / integral periods**
   - \(C(E)\) built from ratios of “canonical” vs “Néron” periods, or denominators of modular symbols after integral normalization.
   - Vatsal-style canonical periods: relate \(p\)-adic integrality to congruence modules.

3. **Manin constant and modular degree**
   - \(C(E)\) involving \(m(E)\) and \(\deg(\phi)\).
   - (Caution: this may be too small/weak; still worth tracking.)

4. **Tamagawa/torsion denominators in algebraic \(L\)-values**
   - \(C(E)\) capturing primes dividing the algebraic special values \(L^{\mathrm{alg}}\) (but beware: this is usually *not* uniform in \(p\) without deeper congruence control).

### Chosen working definition for execution (current)

We will execute Dream A with candidate (1): **congruence ideal / congruence number**.

Let \(f=\sum a_n q^n\) be the weight‑2 newform of level \(N\) attached to \(E\) (so \(a_n\in\mathbb Z\)). Let \(\mathbf T_{\mathbb Z}\) be the (commutative) Hecke algebra generated by the Hecke operators acting on the integral cuspform lattice \(S_2(\Gamma_0(N),\mathbb Z)\).

Let \(\lambda_f:\mathbf T_{\mathbb Z}\to \mathbb Z\) be the eigencharacter \(t\mapsto\) (eigenvalue of \(t\) on \(f\)), and let \(I_f=\ker(\lambda_f)\).

Define the **(Wiles) congruence ideal** by
\[
  \mathfrak c(f)\ :=\ \lambda_f\!\big(\mathrm{Ann}_{\mathbf T_{\mathbb Z}}(I_f)\big)\ \subseteq\ \mathbb Z,
\]
and define \(C(E)\in\mathbb Z_{>0}\) to be the positive generator of \(\mathfrak c(f)\).

Heuristic meaning: \(p\mid C(E)\) iff there are nontrivial congruences modulo \(p\) between \(f\) and other eigenforms inside the relevant integral Hecke module.

### Expected proof architecture

Goal: prove \(p\mid L_p(E,T)\Rightarrow p\mid C(E)\).

Typical chain:

- Express \(L_p(E,T)\) as a \(\mathbb{Z}_p\)-valued measure built from **integral modular symbols**.
- Show that “all moments divisible by \(p\)” forces the underlying symbol/measure to vanish mod \(p\).
- Identify “vanishing mod \(p\)” with “\(f\) is congruent mod \(p\) to something Eisenstein/old/another form,” i.e. \(p\) divides a congruence module.
- Conclude \(p\mid C(E)\).

This is the most classical-looking path to a genuine finiteness theorem.

### What is actually missing (to make Dream A a theorem)

To make the above chain referee-tight, we still need a clean, citable (or internally proved) statement of the form:

- **Missing Lemma A\*** (mod‑\(p\) vanishing \(\Rightarrow\) congruence prime):  
  If the cyclotomic modular‑symbol measure defining \(L_p(E,\cdot)\) is \(0\) modulo \(p\) (equivalently \(L_p(E,T)\in p\Lambda\)), then \(p\mid \mathfrak c(f)\) (equivalently \(p\mid C(E)\)).

This is the single “Dream A core” implication we are currently hunting in the Vatsal/Diamond/Hida tradition.

### Fallback internal proof plan for “Missing Lemma A\*” (if no citation exists)

If we cannot locate a clean theorem-number citation, the internal-proof route naturally decomposes as follows.

- **Lemma A\*.1 (integral modular-symbol measure exists)**  
  Construct the cyclotomic measure \(\mu_{f,p}\) valued in \(\mathbb Z_p\) (after canonical-period normalization) whose Mellin transform is \(L_p(E,T)\) up to \(\Lambda^\times\). Concretely, this is the Mazur–Tate–Teitelbaum / Stevens modular-symbol construction of the cyclotomic \(p\)-adic \(L\)-function.
  - **External inputs**: integral modular symbols / integral cohomology realization; precise comparison of our \(L_p(E,T)\) normalization with modular-symbol normalization (period dictionary).

- **Lemma A\*.2 (divisibility in \(\Lambda\) \(\Leftrightarrow\) mod-\(p\) vanishing of the measure)**  
  Show \(L_p(E,T)\in p\Lambda\) iff the mod-\(p\) reduction of \(\mu_{f,p}\) is the zero measure (equivalently all character values are \(0\bmod p\)).  
  - **Status**: this is essentially the already-audited “Fp\(\mu\)-0” criterion (Weierstrass/measure theory).

- **Lemma A\*.3 (mod-\(p\) vanishing \(\Rightarrow\) congruence prime)**  
  Show \(\mu_{f,p}\equiv 0\pmod p\) forces \(p\mid \mathfrak c(f)\). A workable route is:
  - identify \(\mu_{f,p}\) with a specific integral modular-symbol class in the \(f\)-eigenspace of integral cohomology;
  - prove “\(\mu_{f,p}\equiv 0\bmod p\)” implies that eigenclass is \(0\) in mod-\(p\) cohomology;
  - translate “eigenclass dies mod \(p\)” into “\(f\) is not isolated mod \(p\)”, i.e. \(p\) divides the congruence module/ideal.
  - **External inputs**: mod-\(p\) multiplicity one for the Hecke action on cohomology, an Ihara-lemma style control of old/new at level \(Np\) as needed, and the dictionary equating the congruence ideal with annihilators/Fitting ideals of the relevant Hecke/cohomology congruence module.

### Analogy checkpoint (sanity target)

There are settings where “congruence ideal is generated by a \(p\)-adic \(L\)-function” is genuinely provable (e.g. Eisenstein settings leading to Ferrero–Washington type conclusions). Any successful proof of Lemma A\*.3 for general cuspforms will likely resemble those arguments structurally: identify the *mod-\(p\)* vanishing locus of a \(p\)-adic \(L\)-function with an Eisenstein/congruence locus in a Hecke algebra.

### Execution checklist (Dream A)

- **A.1 Define \(C(E)\) in the manuscript notation**
  - Pick one candidate definition and write it down precisely.
  - Deliverable: a short definition block + “choice independence” lemma statement.

- **A.2 Find/derive the key bridge**
  - Target lemma: \(p\mid L_p(E,T)\Rightarrow p\mid C(E)\).
  - Deliverable: either (i) exact theorem-number citation, or (ii) a proof outline with named sublemmas and required hypotheses.

- **A.3 Verify integrality normalizations**
  - Deliverable: a “normalization dictionary” between our \(L_p(E,T)\) and the paper’s \(L_p\), including period choices.

- **A.4 Produce an explicit “finite exceptional set” corollary**
  - Deliverable: corollary statement: \(\{p:\mu_p(E)>0\}\subseteq \{p: p\mid C(E)\}\cup S_{\text{bad}}\).

---

## Dream Theorem B — “uniform mod-\(p\) nonvanishing in a cyclotomic family”

### Statement (target)

Let \(E/\mathbb{Q}\) be a fixed non‑CM modular elliptic curve.

There exists a nonzero integer \(C(E)\) such that for every good ordinary prime \(p\nmid C(E)\), there exists a finite order cyclotomic character \(\chi\) of conductor \(p^n\) (for some \(n\ge 1\)) such that:

\[
  \frac{L(E,\chi,1)}{\Omega_E^{\pm}} \not\equiv 0 \pmod p,
\]
in the appropriate integral model (precise algebraicity ring to be specified).

Consequences:

- The corresponding interpolation gives \(L_p(E,\chi)\not\equiv 0\pmod p\).
- Hence \(L_p(E,T)\not\equiv 0\pmod p\), hence \(\mu_p(E)=0\).

### Why this is hard (and why it’s still the right dream)

For a **fixed prime \(p\)**, there are many results proving existence of infinitely many cyclotomic twists \(\chi\) with \(L(E,\chi,1)\neq 0\) (complex nonvanishing).  
What we need here is strictly stronger:

- **mod-\(p\) nonvanishing** (integral nondivisibility), not just nonzero in \(\mathbb{C}\);
- and **uniformity as \(p\) varies**, i.e. “for all \(p\nmid C(E)\)” for a fixed \(E\).

This is exactly the missing classical mechanism that would turn \(\mu=0\) from an open conjecture into a theorem.

### Relationship to Dream Theorem A

Dream B is the “character witness” form; Dream A is the “congruence ideal controls \(\mu\)” form.

In practice:

- **A \(\Rightarrow\) B**: if \(p\nmid L_p(E,T)\) in \(\Lambda\), then by the character-level criterion (Fp\(\mu\)-0 / Weierstrass preparation) there exist deep cyclotomic \(\chi\) with \(v_p(L_p(E,\chi))<1\), i.e. a witness.
- **B \(\Rightarrow\) A**: if there exists \(\chi\) with \(v_p(L_p(E,\chi))<1\), then \(p\nmid L_p(E,T)\), hence \(\mu_p(E)=0\).

So the hard content of both dreams is the same: rule out “\(p\mid L_p(E,T)\)” for almost all \(p\), by tying it to a fixed integer \(C(E)\).

### Expected proof architecture (Dream B)

There are two realistic ways to attack B:

1) **Reduce B to A (congruence ideal route)**  
Show that the mod-\(p\) reduction of the \(\mathbb{Z}_p\)-valued measure defining \(L_p(E,\cdot)\) is nonzero unless \(p\) divides a congruence/period ideal.  
This is essentially Dream A in disguise.

2) **Direct mod-\(p\) nonvanishing among twists (distribution route)**  
Prove that among the (many) cyclotomic characters of conductor \(p^n\), at least one has algebraic \(L\)-value not divisible by \(p\), uniformly for all \(p\nmid C(E)\).  
This would be a new “uniform mod-\(p\)” nonvanishing theorem.

### Execution checklist (Dream B)

- **B.1 Fix the integral algebraic \(L\)-value normalization**
  - Define \(L^{\mathrm{alg}}(E,\chi)\) and the precise integrality ring.
  - Deliverable: definition + lemma “\(L^{\mathrm{alg}}(E,\chi)\) is \(p\)-integral for good ordinary \(p\) after canonical period normalization.”

- **B.2 Tie mod-\(p\) nonvanishing to \(L_p(E,T)\notin p\Lambda\)**
  - Deliverable: lemma “\(p\mid L_p(E,T)\) iff \(v_p(L_p(E,\chi))\ge 1\) for all sufficiently deep \(\chi\)” (our Fp\(\mu\)-0 language).

- **B.3 Choose an attack route**
  - **Congruence route**: prove “\(p\mid L_p(E,T)\Rightarrow p\mid C(E)\)” (Dream A core).
  - **Distribution route**: prove “for each \(p\nmid C(E)\), \(\exists\chi\) with \(L^{\mathrm{alg}}(E,\chi)\not\equiv 0\pmod p\)”.

- **B.4 Convert to a finiteness statement**
  - Deliverable: corollary: \(\{p:\mu_p(E)>0\}\subseteq \{p:p\mid C(E)\}\cup S_{\text{bad}}\).

---

## Extensions we will need (after Dream A/B)

### Supersingular primes (signed \(\mu^\pm\))

If we want an “all primes” conclusion, we need a signed analogue:

- Replace \(L_p\) by \(L_p^\pm\) (Pollack/Kobayashi/LLZ setup).
- Replace “ordinary congruence module” by the signed/congruent \(p\)-adic \(L\)-function integrality package.

**Execution stub**: once Dream A is proved in the ordinary setting, write the signed analogue as Dream A\(^\pm\) and identify what changes (period normalization, signed measures, plus/minus Coleman maps).

### Split multiplicative primes (improved \(L_p^{\!*}\))

At split multiplicative primes, \(L_p\) has a trivial zero and one works with an improved \(L_p^{\!*}\).
The \(\mu\)-criterion and primitivity formulation still apply, but the normalization/correction factors must be tracked.

---

## Where this plugs into the BSD proof-track

Once either Dream A or Dream B is proved (with explicit hypotheses), update:

- `BSD_Jon_Final_PROOF_TRACK.md`
  - upgrade **Fpμ-2** from **blocked** to **done** (or to “done outside primes dividing \(C(E)\)” + “finite closure list”),
  - record the precise theorem-number citation(s) and the definition of \(C(E)\),
  - add the resulting “finite exceptional set” statement as a new node if desired (Fpμ-2c).

- `BSD-Jon-Final.txt`
  - in Appendix `F.pmu`, replace the “BLOCKED” status paragraph with the proved theorem statement,
  - add the \(C(E)\) definition and the corollary “\(\mu_p(E)=0\) for all but finitely many \(p\).”

---

## Starting corpus (known seeds and adjacent tools)

- **Ferrero–Washington** (abelian setting): \(\mu=0\) for cyclotomic \(\mathbb{Z}_p\)-extensions of abelian number fields.
- **Oukhaba–Viguié** (`arXiv:1311.3565`, Theorem `theomu`): \(\mu=0\) for Katz \(p\)-adic \(L\)-functions (CM ordinary/split setting).
- **Greenberg–Vatsal** (`arXiv:math/9906215`, Thm (1.3)): rational \(p\)-isogeny \(\mu=0\) seed (fixed \(p\)).
- **EPW06** (`arXiv:math/0404484`): propagation of \(\mu=0\) in a fixed Hida family (fixed \(p\)).
- **Vatsal / Diamond / Ohta / Hida**: canonical periods + congruence modules (the likely place Dream A lives, if it lives anywhere).
- **Diamond** (Compositio Math. 71 (1989), 49–83): congruence modules for \(\Lambda\)-adic forms (local copy: `tmp/numdam/diamond1989.pdf`).
- **Ray–Sujatha–Vatsal** (`arXiv:2111.14304`): explicit canonical-period normalization in terms of congruence numbers (local copy: `tmp/arxiv/2111.14304/`).

---

## Decision log (fill as we execute)

- **Chosen \(C(E)\)**: \(C(E)=\) generator of the **Wiles congruence ideal** \(\mathfrak c(f)=\lambda_f(\mathrm{Ann}_{\mathbf T_{\mathbb Z}}(I_f))\subset\mathbb Z\) (see “Chosen working definition” in Dream A).
- **Exact theorem/citation that gives Dream A**: **NOT YET FOUND**.
  - Candidates to mine next: Vatsal (Duke 1999), Hida (Amer J Math 1988), Greenberg–Stevens (Invent 1993).
- **Search log (what we already checked)**:
  - Diamond (Compositio 1989; `tmp/numdam/diamond1989.*`): develops \(\Lambda\)-adic congruence modules / level-raising technology, but **does not** state a cyclotomic “\(p\mid L_p \Rightarrow p\mid C(E)\)” bridge.
  - Ray–Sujatha–Vatsal (`arXiv:2111.14304`; `tmp/arxiv/2111.14304/`): provides an explicit **canonical-period vs congruence-number** normalization and an integrality proof in that setting, but **does not** give the Dream‑A mod-\(p\) primitivity bridge for cyclotomic \(L_p(E,T)\).
  - Kim–Lee–Ponsinet (`arXiv:1909.01764`; `tmp/arxiv/1909.01764/`): uses Vatsal-style integral period comparisons in the *zeta element* setting; it explicitly warns that mod-\(p\) nonvanishing is **not** obviously preserved under the Coleman/localization maps to \(p\)-adic \(L\)-functions.
  - Maksoud (`arXiv:2312.16706`; `tmp/arxiv/2312.16706/`): **does** prove an integral “congruence module is generated by a \(p\)-adic \(L\)-function” statement (Proposition `prop:congruence_module_and_p_adic_L_functions`, via an adjoint \(p\)-adic \(L\)-function \(L_p(\ad F)\)), but this is for **Hida-family congruence / adjoint \(p\)-adic \(L\)**, not the **cyclotomic \(L_p(E,T)\)**.
  - Kim–Ota (`arXiv:1905.02926`; `tmp/arxiv/1905.02926/`): develops quantitative relations among congruence ideals and (anti)cyclotomic \(p\)-adic \(L\)-functions/periods; it cites Vatsal 1999 explicitly (`vatsal-cong`) and contains formulas where period/congruence ratios appear, but it does **not** directly state Dream‑A’s cyclotomic primitivity bridge.
  - Hida (Ann. Sci. ENS **19** (1986), 231–273; local copy `tmp/numdam/hida1986_ens.pdf`): constructs an “Iwasawa module of congruences” over the **weight-variable** Iwasawa algebra \(A=\mathbb Z_p[[X]]\) and relates congruence modules to characteristic power series / (weight-variable) \(p\)-adic measures. This is powerful congruence-module technology, but it is **not** (as far as we can see from the text) a theorem about the **cyclotomic** \(L_p(E,T)\) being primitive mod \(p\) outside primes dividing a fixed \(C(E)\).
- **If no citation exists**: prove “Missing Lemma A\*” internally, decomposed as:
  - (L1) integral modular-symbol construction of cyclotomic \(L_p(E,T)\) with an explicit \(\mathbb Z\)-lattice;
  - (L2) \(L_p(E,T)\in p\Lambda\iff\) modular-symbol measure \(\equiv 0\pmod p\) (Weierstrass/measure criterion; this is our Fp\(\mu\)-0 package);
  - (L3) modular-symbol measure \(\equiv 0\pmod p\Rightarrow p\mid\mathfrak c(f)\) (the genuine missing step).
