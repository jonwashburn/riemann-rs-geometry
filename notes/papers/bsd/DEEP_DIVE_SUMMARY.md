### BSD external deep-dive summary (paper → proof-track dependencies)

This file is the **index** for the BSD proof-track external inputs.

Each row links:
- a **reference** (paper/book),
- what it supplies (precise theorem),
- which proof-track labels depend on it,
- and the current audit status.

#### Index

| Ref | What we need from it | Proof-track labels impacted | Status |
|---|---|---|---|
| Perrin–Riou (1994/1995) + Berger (2003) + Cherbonnier–Colmez (1999) | Big logarithm \(\mathcal{L}_V\) and explicit reciprocity / χ-interpolation (ordinary + signed variants) | `lem:PR-ord-proof`, `lem:PR-signed-proof`, `thm:HL-ordinary`, `thm:HL-signed`, `lem:triang-ord-modp`, `lem:triang-signed` | todo |
| Coleman–Gross (heights) + Nekovář | Definition/normalization of cyclotomic \(p\)-adic height; formal-group factorization; integrality | `B2`, `lem:formal-factor`, `lem:unit-log`, `lem:diag-units`, `lemC:height=PT` | **blocked (internal contradiction in §7.1 / Lemma `lem:unit-log` usage)** |
| Greenberg (1989) | Ordinary local conditions; control theorems; PT framework references | `B4`, `thm:sha-finite`, `thm:HL-ordinary`, operator model (`thm:coker-id`) | todo |
| Kato (2004) | One-sided divisibility / Euler system input (B1′) | `B1'`, `prop:mu-zero`, `prop:BSDp` | todo |
| Kobayashi (2003) + Pollack (2003) + LLZ (2012) | Signed local conditions, signed Coleman maps, signed heights/reciprocity | `thm:HL-signed`, `lem:PR-signed-proof`, `lem:triang-signed`, `lem:diag-units-signed` | todo |
| Nekovář (Selmer complexes) | Precise PT/Cassels–Tate pairing formalism, orthogonality statements | `B3`, `lemC:height=PT`, `thm:sha-finite` | todo |
| Yan–Zhu (2024, arXiv:2412.20078) | Ordinary cyclotomic IMC **equality** for non-CM \(E/\mathbb Q\) at good ordinary \(p>2\) under irreducibility of \(E[p]\); includes BSD\(_p\)/\(p\)-converse applications | **Replacement candidate** for the disc engine on ordinary primes: `cor:disc-imc`, `thm:universal-imc`, downstream `cor:universal-bsd-p` | todo |
| Burungale–Castella–Skinner (2024, arXiv:2405.00270; IMRN) | Cyclotomic + anticyclotomic main conjectures in broad ordinary settings via base change + 2-variable zeta elements; reduces to Wan-type divisibilities | **Replacement candidate** for disc engine (ordinary primes); also informs the “finite closures” package | todo |
| Burungale–Skinner–Tian–Wan (2024, arXiv:2409.01350) | “Zeta elements for elliptic curves and applications” (supersedes Wan’s older supersingular preprint); candidate source for **supersingular** IMC/BSD inputs | Potential replacement for the disc engine / signed IMC citations at supersingular primes | todo |
| Sprung (2024, Adv. Math.; ScienceDirect `S0001870824002561`) | Supersingular Iwasawa main conjectures “beyond the case \(a_p=0\)” (relevant for small \(p\) / general nonordinary settings) | Signed/small-prime coverage for `thm:universal-imc` without disc pinch | todo |
| Castella (2025, arXiv:2502.19618) | Perrin–Riou formula; characteristic power series of signed Selmer groups (ties to \(p\)-adic BSD at supersingular primes) | Signed theory / leading-term interfaces; may replace internal signed computations | todo |
| Keller–Yin (2024, arXiv:2410.23241) | \(p\)-converse theorem at Eisenstein primes (rational \(p\)-isogeny / reducible residual cases) | Exceptional-prime closures in the “IMC equality for all \(p\)” story | todo |


