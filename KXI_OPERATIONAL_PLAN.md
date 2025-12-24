## KXI (Whitney Carleson Energy for \(U_\xi=\Re\log\xi\)) — Operational Plan

**Date**: 2025-12-24  
**Purpose**: Identify a single, sharply stated *classical* theorem that would close the PSC / boundary‑wedge route to RH (as written in `Riemann-active.txt`), and decompose it into a small set of checkable sublemmas with an explicit “where the literature stops” boundary.

---

## Executive summary

The PSC route is “RH from a boundary wedge (P+)”. In the active writeup (`Riemann-active.txt`), the only deep analytic payload needed to force (P+) is a **Whitney‑scale Carleson/Dirichlet‑energy bound** for the harmonic field
\[
U_\xi(\sigma,t)=\Re\log\xi\!\left(\tfrac12+\sigma+it\right)\qquad(\sigma>0).
\]

Call this payload **KXI**: a uniform constant \(K_\xi<\infty\) such that
\[
\iint_{Q(\alpha I)}|\nabla U_\xi|^2\,\sigma\,d\sigma\,dt\ \le\ K_\xi\,|I|
\]
on **Whitney intervals** \(I=[T-L,T+L]\) with \(L=c/\log\langle T\rangle\).

If **KXI** were proved unconditionally (with explicit constants), the PSC chain would claim to deliver RH.

Operationally, this plan:
- pins down the exact theorem statement;
- identifies the minimal analytic sublemmas needed;
- and flags the *precise place* where current arguments appear to require a genuinely new theorem (or contain an arithmetic/log error).

---

## Current status in this repo (PSC route)

- **Active writeup**: `Riemann-active.txt` (also present as `Riemann-active.tex/.pdf`).
- **Where KXI is used**: `prop:Kxi-finite` and the “Boxed \(K_\xi\) audit” immediately below it.
- **Where KXI is claimed**: `lem:carleson-xi` + Appendix `app:vk-annuli-kxi`.

### Immediate red flag to resolve before any further work

In `Riemann-active.txt`, the sketch bound
\[
\nu_k\ \le\ a_1\cdot 2^k L\log\langle T\rangle\ +\ a_2\cdot \log\langle T\rangle
\]
is then inserted into
\[
\sum_{k\ge 1}4^{-k}\nu_k,
\]
and the text concludes this is \(\ll L\log\langle T\rangle + 1\), hence \(O(1)\) on Whitney scale \(L=c/\log\langle T\rangle\).

But mechanically,
\[
\sum_{k\ge1}4^{-k}\cdot \log\langle T\rangle\ =\ \tfrac13\,\log\langle T\rangle,
\]
which is **not** \(O(1)\). So either:
- the stated \(\nu_k\) bound is missing a factor of \(L\), or
- the annular weight is stronger than \(4^{-k}\), or
- the energy estimate is actually for a *weighted* zero count (e.g. weights involving \(\beta-1/2\)), or
- the KXI step as written is incorrect.

This is the first thing KXI must settle.

---

## Target theorem (KXI) — exact statement to prove

Fix an aperture \(\alpha\in[1,2]\). Define for an interval \(I=[T-L,T+L]\):
- the Carleson box \(Q(\alpha I):=(0,\alpha L]\times [T-\alpha L,\,T+\alpha L]\);
- the Whitney scale \(L=L(T):=c/\log\langle T\rangle\) with \(\langle T\rangle=\sqrt{1+T^2}\);
- the harmonic field \(U_\xi(\sigma,t):=\Re\log\xi(\tfrac12+\sigma+it)\) for \(\sigma>0\).

> **Theorem KXI (Whitney Carleson energy for \(\Re\log\xi\)).**  
> There exist constants \(c\in(0,1]\) and \(K_\xi<\infty\) such that for all \(T\in\mathbb R\) and Whitney intervals \(I=[T-L,T+L]\) with \(L=c/\log\langle T\rangle\),
> \[
> \iint_{Q(\alpha I)}|\nabla U_\xi(\sigma,t)|^2\,\sigma\,d\sigma\,dt\ \le\ K_\xi\,|I|.
> \]

### Why this closes the PSC proof (as written)

`Riemann-active.txt` uses \(K_\xi\) to build a uniform box‑energy constant
\[
C_{\rm box}^{(\zeta)}:=K_0+K_\xi,
\]
which feeds:
- CR–Green pairing bounds (window test vs boundary phase derivative),
- closure of the boundary wedge (P+),
- and finally the Schur–Herglotz “pinch” to exclude off‑critical zeros.

So **KXI is the single classical theorem to close the PSC route**, modulo cleaning up any hidden circularity.

---

## Proof decomposition: 5 sublemmas (each a crisp failure point)

### KXI‑A — Energy/derivative equivalence for harmonic \(U\)

**Goal**: reduce \(\iint |\nabla U|^2\,\sigma\) to an \(L^2(\sigma\,d\sigma\,dt)\) bound for \(\partial_\sigma U\) on \(Q(\alpha I)\):
\[
|\nabla U|^2 \asymp |\partial_\sigma U|^2 \quad\text{(since \(U\) is harmonic)}.
\]

This is classical harmonic analysis on the half‑plane; should be fully unconditional.

### KXI‑B — Neutralization of the near field (local Blaschke product)

**Goal**: define a half‑plane Blaschke product \(B_I\) removing zeros in a dilated box \(Q(\alpha' I)\), and show:
- \(\widetilde U_\xi := \Re\log(\xi\cdot B_I)\) is harmonic on \(Q(\alpha I)\),
- the energy difference between \(U_\xi\) and \(\widetilde U_\xi\) is \(O_\alpha(|I|)\),
- so it suffices to bound the neutralized far field.

This is classical complex analysis; delicate but standard in Hardy/BMO technology.

### KXI‑C — Annular \(L^2\) aggregation (Poisson kernel Schur bound)

**Goal**: if \(\mathcal A_k\) is the annulus of zeros at vertical distance \(\Delta\asymp 2^k L\), define
\[
V_k(\sigma,t)=\sum_{\rho\in\mathcal A_k} \frac{\sigma}{(t-\gamma)^2+\sigma^2}
\]
(or the correct shifted kernel depending on \(\beta\)), and prove an estimate of the form:
\[
\iint_{Q(\alpha I)} V_k(\sigma,t)^2\,\sigma\,d\sigma\,dt\ \le\ C_\alpha\,|I|\,w_k\cdot \nu_k,
\]
where:
- \(\nu_k\) is an annular zero count (possibly weighted), and
- \(w_k\) is the geometric decay factor (in the writeup: \(w_k=4^{-k}\)).

This is plausibly unconditional and “analysis only”.

### KXI‑D — The *real* number‑theory payload: a uniform bound on the weighted annular sum

Let \(\nu_k\) be whatever zero statistic appears after the correct kernel algebra (this must be fixed explicitly!). The needed conclusion is:
\[
\sum_{k\ge 1} w_k\,\nu_k\ \le\ C\quad\text{uniformly in }T.
\]

This is the part that must be either:
- a known theorem (unlikely), or
- the genuinely **new theorem** one must create.

**Key diagnostic**: if \(\nu_k\) is an *unweighted* count of all zeros in the annulus, any use of Riemann–von Mangoldt only gives
\[
\nu_k \ll 2^k L\log T + O(\log T),
\]
and the \(O(\log T)\) error destroys uniformity when \(L\sim 1/\log T\).

So to make KXI work, you need one of:
- a stronger kernel weight than \(w_k=4^{-k}\),
- cancellation/neutralization that removes the \(O(\log T)\) term,
- a theorem giving **short‑interval zero count with \(O(1)\) error**, e.g.
  \[
  N(T+H)-N(T-H)\ \le\ C\,H\log T + C'
  \quad\text{for }H\asymp 2^k/\log T,
  \]
  uniformly in \(T\) and \(k\ge 1\);
- or a formulation where \(\nu_k\) counts only zeros with \(\beta\ge 1/2+\eta\) and comes with extra \((\beta-1/2)\) weights (so that zero‑density bounds plausibly control it).

### KXI‑E — Close the PSC chain from KXI

Once KXI holds:
- combine with the already “analysis‑only” prime‑tail bound \(K_0\),
- feed CR–Green pairing to produce the window certificate,
- deduce (P+),
- then use the Schur–Herglotz pinch to rule out off‑critical zeros.

This is largely complex analysis + bookkeeping; hard but conceptually “standard once the constants exist”.

---

## Where existing literature stops (most likely)

The place KXI seems to demand new math is **KXI‑D**: it implicitly asks for **uniform control of zeros of \(\xi\) on extremely short vertical scales** (Whitney scale \(L\sim 1/\log T\)) in a way that beats the standard \(O(\log T)\) fluctuations coming from the argument term \(S(T)\).

Known unconditional tools:
- global zero counts (Riemann–von Mangoldt) with \(O(\log T)\) error,
- bounds on \(S(T)\) itself (e.g. \(S(T)=O(\log T)\), and refinements),
- classical zero‑density estimates \(N(\sigma,T)\) for \(\sigma>1/2\),
do **not** directly give the kind of \(O(1)\) control in short intervals that the Whitney‑scale sum needs, unless the kernel weighting/neutralization is stronger than currently written.

---

## Recommendation (PSC route)

If you want to seriously pursue PSC classically, the first “make‑or‑break” step is:

> **Fix the exact definition of \(\nu_k\) and the weight \(w_k\)** emerging from the kernel/energy identity, and re‑derive the summation bound with no hand‑waving.

If that still demands a short‑interval bound beating \(O(\log T)\), then **that short‑interval bound is the new theorem**—and it is extremely likely to be at least as hard as RH itself.


