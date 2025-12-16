### Route‑3 Identity Part (No Positivity): Precise Classical Theorem + Proof Checklist

This document isolates the **identity/bookkeeping** component of Route‑3: converting the symmetric zero‑sum functional into a boundary pairing. **No positivity assumptions are used** anywhere here.

The output of this document should be a single reusable “analysis lemma checklist” that can be formalized independently of RH.

---

### Objects (as used in the Route‑3 skeleton)

- **Completed ξ-function**: \(\xi(s)\) is the standard completed Riemann ξ, entire of order 1, with functional equation \(\xi(1-s)=\xi(s)\) and reality \(\xi(\overline{s})=\overline{\xi(s)}\).
- **Test transforms**: for an admissible test function \(f\), write \(F_f(s)\) for its Mellin/Laplace/Fourier-side transform (depending on the concrete model). On the critical line:
  - \(F_f(t) := F_f\!\left(\tfrac12+it\right)\).
- **Pair**: the sesquilinear test expression is
  - \(\mathrm{pair}(f,g) := g ⋆ \widetilde{(\overline{f})}\) (order-swapped so that on \(\Re(s)=\tfrac12\), \(F_{\mathrm{pair}(f,g)} = \overline{F_f}\,F_g\)).
- **Symmetric zero-sum functional**: \(W^{(1)}(h)\) is the symmetric sum over nontrivial zeros \(\rho\) of \(\xi\):
  - \(W^{(1)}(h) := \sum_{\rho} F_h(\rho)\) (symmetric truncation in \(\Im\rho\)).

---

### Finish-line identity statement (distribution / measure form)

The right “weight” for ξ on \(\Re(s)=\tfrac12\) is **not** a pointwise Lebesgue density: \(\Re(\xi'/\xi)\) vanishes a.e. on the critical line away from zeros. The correct identity statement is therefore **measure/distribution**-valued.

#### Theorem (identity part; no positivity)
Let \(f,g\) lie in a test class such that:

- **(H1) Holomorphy**: \(F_f(s),F_g(s)\) extend to entire functions (or at least holomorphic on a half-plane containing the standard explicit-formula contour shifts).
- **(H2) Vertical-strip decay**: for every strip \(a \le \Re(s) \le b\) and every \(N\ge0\),
  - \(\sup_{a\le\sigma\le b}(1+|t|)^N |F_f(\sigma+it)| < \infty\) and similarly for \(F_g\).
- **(H3) Pair boundary factorization** on the critical line:
  - \(F_{\mathrm{pair}(f,g)}(\tfrac12+it) = \overline{F_f(t)}\,F_g(t)\).
- **(H4) Contour bookkeeping admissibility**: \(s \mapsto F_{\mathrm{pair}(f,g)}(s)\,\xi'(s)/\xi(s)\) is integrable on the truncation contours used below (this is automatic for compactly supported smooth Mellin tests; for Schwartz/log‑Fourier tests it holds on the strip actually used).

Define \(W^{(1)}(h)\) by the contour integral (see below) so it equals the symmetric zero sum.

Then there exists a **tempered distribution** \(\nu\in\mathcal S'(\mathbb R)\) (equivalently: a complex Borel measure of polynomial growth) such that for all admissible \(f,g\),

\[
W^{(1)}(\mathrm{pair}(f,g)) \;=\; \langle \nu,\; t\mapsto \overline{F_f(t)}\,F_g(t)\rangle.
\]

Moreover, one canonical choice of \(\nu\) is the boundary value (in the distribution sense) of the logarithmic derivative:

\[
\nu \;:=\; \mathrm{b.v.}\left(t \mapsto -\frac{1}{2\pi}\,\frac{\xi'}{\xi}\!\left(\tfrac12+it\right)\right),
\]

with principal-value/indentation conventions exactly matching the symmetric truncation of the zero sum.

**Important:** this theorem produces a *signed/complex* spectral distribution \(\nu\). Turning \(\nu\) into a **positive** measure \(\mu\ge0\) is the RH‑equivalent step and is *not* part of this identity theorem.

---

### Definition of the symmetric zero-sum via contour integrals (preferred “precise” definition)

Fix \(c>1\). For \(T>0\), let \(R_{c,T}\) be the rectangle with vertices
\(c\pm iT\) and \(1-c\pm iT\), oriented positively.

If the contour meets a zero of \(\xi\), modify it by small semicircle indentations; equivalently, interpret the integral as a **principal value** with symmetric excisions around poles.

Define the truncated functional:

\[
W^{(1)}_T(h) \;:=\; \frac{1}{2\pi i}\int_{\partial R_{c,T}} F_h(s)\,\frac{\xi'(s)}{\xi(s)}\,ds.
\]

Then set:

\[
W^{(1)}(h) \;:=\; \lim_{T\to\infty} W^{(1)}_T(h),
\]

provided the limit exists (it does under (H2)).

By the residue theorem, \(W^{(1)}_T(h)\) equals the sum of \(F_h(\rho)\) over zeros \(\rho\) with \(|\Im\rho|<T\), with the chosen indentation convention matching symmetric summation.

---

### Proof outline checklist (what must be shown; all “standard analysis”)

- **(P0) Residue theorem / argument principle**:
  - show \(W^{(1)}_T(h)\) equals the truncated zero sum.
- **(P1) Horizontal edges vanish**:
  - use (H2) plus the standard bound \(\xi'/\xi(\sigma+iT)=O(\log(2+|T|))\) on fixed strips.
- **(P2) Limit \(T\to\infty\)**:
  - justify \(\lim_{T\to\infty} W^{(1)}_T(h)\) exists for the admissible class.
- **(P3) Move contour to \(\Re(s)=\tfrac12\)** (or \(\tfrac12+\varepsilon\) then \(\varepsilon\downarrow0\)):
  - keep explicit track of poles crossed (zeros of ξ) using indentation.
- **(P4) Convert line integral to a boundary distribution**:
  - parameterize \(s=\tfrac12+it\) and define the distributional boundary value \(\nu\).
- **(P5) Plug in \(h=\mathrm{pair}(f,g)\)**:
  - use (H3) to rewrite the boundary test function as \(\overline{F_f}F_g\).

None of (P0)–(P5) requires RH or any positivity condition.

---

### Where RH-equivalence begins (not part of this file)

Once you have \(W^{(1)}(\mathrm{pair}(f,g))=\langle\nu,\overline{F_f}F_g\rangle\),
the Route‑3 “finish line” is to show the representing object is **positive**:

- **Target (RH‑equivalent):** \(\nu\) is a positive measure \(\mu\ge0\), so \(W^{(1)}(\mathrm{quad}(f))\ge0\) for all \(f\).

That step is the passivity/Carathéodory/Herglotz bridge and is documented separately in `ROUTE3_POSITIVITY_BRIDGE.md` (to be written).


