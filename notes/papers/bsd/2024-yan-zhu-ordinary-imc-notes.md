### Yan–Zhu (2024) — ordinary cyclotomic main conjecture (non-CM elliptic curves)

#### Reference
- **Authors**: Xiaojun Yan, Xiuwu Zhu
- **Title**: “Main conjectures for non-CM elliptic curves at good ordinary primes”
- **arXiv**: `2412.20078` (v1 announced 2024-12; check latest version)

#### Why this matters for the BSD proof track
This is a **top candidate to replace the disc pinch engine** on *ordinary* primes by importing an unconditional IMC equality theorem from the literature.

If it proves cyclotomic IMC **equality** (not just divisibility) under mild hypotheses, then we can:
- Drop `lem:disc-wedge` / `thm:schur-pinch` as an internal universal engine (or keep them as optional conjectural heuristics).
- Rebase `cor:disc-imc` / `thm:universal-imc` on a citeable theorem in the ordinary setting.

#### What we need to extract (exact statements)
- **IMC equality (ordinary cyclotomic)**:
  - A theorem of the form \(\mathrm{char}_\Lambda X_p(E/\mathbb Q_\infty) = (L_p(E,T))\) up to \(\Lambda^\times\),
  - with explicit hypotheses (good ordinary \(p>2\), residual irreducibility, local conditions, etc.).
- **Any leading-term / BSD\(_p\) corollaries**:
  - Whether the paper gives the \(p\)-part of BSD (rank/order and leading coefficient) under additional hypotheses.
- **Exceptional prime handling**:
  - What happens for reducible residual (Eisenstein) primes, CM curves, and small primes.

#### Mapping into the proof track
- **Primary impacted labels**:
  - `cor:disc-imc`, `thm:universal-imc` (ordinary branch)
  - Downstream: `cor:universal-bsd-p`, Appendix G (`thm:global-bsd`) via the “IMC equality at all p” promise.
- **Replacement plan**:
  - Replace the “disc-wise pinch ⇒ equality” claim on the ordinary branch by citing Yan–Zhu for IMC equality at ordinary primes.

#### Audit checklist (to fill)
- [ ] Identify the main theorem number(s) giving IMC equality.
- [ ] Write the exact hypotheses in BSD-Jon notation (ordinary local condition, \(p\nmid N\)?, etc.).
- [ ] Confirm whether it is unconditional or conditional on external divisibilities (e.g. Wan/Hsieh/SU).
- [ ] Confirm whether the result is cyclotomic-only or includes base-change/two-variable variants.
- [ ] Note which parts overlap with Skinner–Urban (SU14) and what new coverage is gained.

#### Status
- **todo** (needs full extraction and compatibility check)


