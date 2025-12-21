### Burungale–Castella–Skinner (2024) — base change & Iwasawa main conjectures for GL\(_2\)

#### Reference
- **Authors**: Ashay Burungale, Francesc Castella, Christopher Skinner
- **Title**: “Base change and Iwasawa Main Conjectures for \({\rm GL}_2\)”
- **arXiv**: `2405.00270` (accepted version; to appear in IMRN)

#### Why this matters for the BSD proof track
This is a strong **replacement candidate** for any “disc-wise pinch” step on ordinary primes: it aims to prove cyclotomic (and related) IMC equalities via **base change + zeta elements**, rather than new rigid-analytic boundary arguments.

#### What we need to extract (exact statements)
- **Cyclotomic IMC equality over \(\mathbb Q\)**:
  - Precisely: \(\mathrm{char}_\Lambda X_p(E/\mathbb Q_\infty)=(L_p)\) up to units (or equivalent).
  - Exact hypotheses (good ordinary, residual irreducibility, local conditions).
- **Anticyclotomic / two-variable variants**:
  - Whether these are used as intermediate steps only, or yield additional BSD\(_p\) consequences.
- **BSD consequences**:
  - Any theorem/corollary giving BSD\(_p\) (valuation equality / Sha finiteness / leading term) in certain ranks.

#### Mapping into the proof track
- **Primary impacted labels**:
  - `cor:disc-imc`, `thm:universal-imc` (ordinary branch)
  - Downstream: `cor:universal-bsd-p`
- **Likely role**: replace disc-engine equality by citing a proved IMC equality theorem in the ordinary case, leaving only finitely many “exceptional primes” to close separately (Eisenstein/reducible/small primes).

#### Audit checklist (to fill)
- [ ] Extract theorems for cyclotomic IMC equality (exact numbering).
- [ ] Translate hypotheses into BSD-Jon notation.
- [ ] Identify which inputs are used (e.g. Wan divisibility, 2-variable zeta elements).
- [ ] Confirm what is unconditional vs conditional on earlier divisibilities.
- [ ] Identify any explicit treatment of exceptional primes (Eisenstein, split multiplicative, \(p=2,3\)).

#### Status
- **todo**


