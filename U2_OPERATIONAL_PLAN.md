### Purpose

This operational plan isolates the **only remaining RG‑grade blocker** for the AF‑free continuum package in `Yang-Mills.tex`: discharging **Assumption `assump:U2b`** (graph‑defect \(O(a)\) + low‑energy projector control) via the in‑text **Bridge Lemma target** `lem:bridge-U2b-target`.

This file is *internal workflow tooling* (not part of the manuscript). It exists so future sessions can restart quickly without re‑deriving what the bridge needs.

---

### What is already proved in the manuscript (comparison side)

On a fixed bounded Lipschitz slab / region \(R\):

- **Comparison discretization defect**: Proposition `lem:graph-defect-Oa` proves an energy‑weighted defect bound for a concrete discretization \(J_a\).
- **Comparison low‑energy projector stability**: Lemma `lem:low-energy-proj` proves contour/Davis–Kahan stability for \(J_a E_H([0,\Lambda]) J_a^*\).
- **Comparison “cell average is ~ identity on low energies”**: Lemma `lem:cell-avg-lowenergy` proves \(\|(I-J_a^*J_a)E_H([0,\Lambda])\|\lesssim a\).

These are **analogues only**; they do not by themselves imply OS/GNS embedding‑side `assump:U2b`.

---

### The missing content (bridge side)

To discharge `assump:U2b` one needs to build and estimate a **canonical unitary identification**

\[
V_{a,L}:\ \mathcal H_{a,L}\to\mathcal H_a^{\rm cmp}
\]

on the *time‑zero local* subspace supported in \(R\), such that the OS/GNS embedding data \((I_{a,L},H_{a,L})\) is **quantitatively quasi‑unitarily equivalent** to the comparison model \((J_a^*,H_a^{\rm cmp})\) in the sense of `lem:bridge-U2b-target`:

- **(B1) Embedding match (energy/graph weighted; includes the $H^{1/2}$ graph control needed for the two-sided defect bound)**:
  \[
  \|(I_{a,L}-J_a^*V_{a,L})(H_{a,L}+1)^{-1/2}\|\ \lesssim\ a,\qquad
  \|(H+1)^{1/2}(I_{a,L}-J_a^*V_{a,L})(H_{a,L}+1)^{-1/2}\|\ \lesssim\ a,
  \]
  \[
  \|(I_{a,L}^*-V_{a,L}^*J_a)(H+1)^{-1/2}\|\ \lesssim\ a,\qquad
  \|(H_{a,L}+1)^{1/2}(I_{a,L}^*-V_{a,L}^*J_a)(H+1)^{-1/2}\|\ \lesssim\ a.
  \]
- **(B2) Generator match + graph-norm stability (graph weighted)**:
  \[
  \|(V_{a,L}H_{a,L}-H_a^{\rm cmp}V_{a,L})(H_{a,L}+1)^{-1/2}\|\ \lesssim\ a.
  \]
  In addition, one needs uniform boundedness between graph norms:
  \[
  \|(H_a^{\rm cmp}+1)^{1/2}V_{a,L}(H_{a,L}+1)^{-1/2}\|\ \lesssim\ 1,\qquad
  \|(H_{a,L}+1)^{1/2}V_{a,L}^*(H_a^{\rm cmp}+1)^{-1/2}\|\ \lesssim\ 1.
  \]

Finally, for the low-energy projector part of the bridge one uses that the comparison injection is graph-bounded (standard for cell averaging / FE injections):
\[
\|(H_a^{\rm cmp}+1)^{1/2}J_a(H+1)^{-1/2}\|\ \lesssim\ 1,\qquad
\|(H+1)^{1/2}J_a^*(H_a^{\rm cmp}+1)^{-1/2}\|\ \lesssim\ 1.
\]

Concrete “density-isometry” bridge template: if after tree gauge both the OS/GNS local space and the comparison space admit $L^2$ realizations on the same chord-variable manifold $G^{m(R,a)}$ with absolutely continuous measures $\mu_{a,L}$ and $\mu^{\rm cmp}_a$, then a canonical unitary is $f\mapsto f\sqrt{d\mu_{a,L}/d\mu^{\rm cmp}_a}$. This is recorded in `Yang-Mills.tex` as the target lemma `lem:bridge-density-isometry-target`.

Once (B1)–(B2) hold, `lem:bridge-U2b-target` shows `assump:U2b` follows.

---

### Practical routes to constructing \(V_{a,L}\) (choose the easiest that actually matches objects)

The bridge is not about existence of some abstract unitary; it is about a **canonical identification compatible with time‑zero local observables**.

Practical functional-analytic tool: once you have a *candidate* identification map \(T\) that is a near-isometry on the local core (i.e. \(T^*T=\mathbf 1+O(a)\)), you can replace it by an actual unitary via polar decomposition with controlled error; see `Yang-Mills.tex` Lemma `lem:bridge-polar-unitary`.
In the bridge setting, the typical flow is:
- build \(T_{a,L}\) on the time-zero local cylinder core (tree gauge / explicit discretization map),
- prove near-isometry \(T_{a,L}^*T_{a,L}=\mathbf 1+O(a)\) and graph-boundedness,
- define \(V_{a,L}:=T_{a,L}(T_{a,L}^*T_{a,L})^{-1/2}\),
- reduce (B1) to estimates for \(T_{a,L}\) (plus graph-boundedness of the comparison injection), and treat (B2) separately (polar correction generally introduces a commutator term unless one has extra regularity on the local core, so (B2) is usually verified for the final \(V_{a,L}\) directly).

#### Route 1 (preferred when available): “same generator algebra” OS/GNS identification

If both \(\mathcal H_{a,L}\) and \(\mathcal H_a^{\rm cmp}\) arise as OS/GNS completions of the *same* time‑zero local *‑algebra on \(R\)* (with different inner products/forms), then:

- Define \(V_{a,L}\) on the algebraic core by matching generators \( [O]_{a,L}\mapsto [O]_{a}^{\rm cmp}\).
- Prove the quantitative content by bounding the induced **inner‑product defect** and **form defect** on that core in the relevant graph norms.

This route typically turns (B1)–(B2) into explicit bilinear inequalities on cylinder functions.

#### Route 2: Tree‑gauge coordinate model → Schrödinger comparison

If one uses a **tree‑gauge coordinate map** (local gauge fixing on \(R\)) that identifies the time‑zero lattice degrees of freedom with a vector space chart (Lie algebra variables) on which the generator becomes a Schrödinger‑type operator:

- Set \(\mathcal H_a^{\rm cmp}=L^2(\mathbb R^{m(R,a)},dx)\) with a Schrödinger generator \(H_a^{\rm cmp}\).
- Let \(V_{a,L}\) be the unitary induced by the coordinate map and density (Jacobian) change.
- Then (B1) is essentially a deterministic approximation of the polygonal/smoothed embedding by piecewise‑constant extension in these coordinates; (B2) is a form‑level estimate for the pulled‑back generators.

This route aligns with the “form approximation” NRC machinery (`NRC:form` / `NRC:form-thm`), but requires careful bookkeeping of Jacobians and boundary collars.

#### Route 3: Density‑isometry comparison on fixed slabs (calibrator space)

When a reference product heat‑kernel measure \(\nu\) is used (as in the optional calibrated slab template), a natural unitary is the **density isometry**

\[
U:\ L^2(\mu)\to L^2(\nu),\quad (Uf)=f\,\sqrt{d\mu/d\nu}.
\]

This can be used to define \(V_{a,L}\) when \(\mathcal H_{a,L}\) admits an \(L^2\) realization on the same configuration space; the remaining work is controlling the induced generator conjugations in graph norms.

---

### What to prove next (concrete “next lemmas”)

1. **Define the comparison triple \((\mathcal H_a^{\rm cmp},H_a^{\rm cmp},J_a)\)** explicitly in a way that shares a generator algebra with the OS/GNS time‑zero local algebra on \(R\).
2. **Construct \(V_{a,L}\) on the time‑zero local core**, and prove it extends to a unitary on the local completion.
3. Prove **(B1)** (embedding match) as a deterministic approximation statement between the chosen embeddings on the core.
4. Prove **(B2)** (generator match) via a **bilinear form estimate** on a common operator core (as spelled out in the remark after `lem:bridge-U2b-target`).

---

### Non-goals (do not spend time here)

- Do *not* attempt to derive (B2) from abstract form convergence alone; we need an explicit core estimate.
- Do *not* refactor global notation in the manuscript to “make the bridge nicer”; the bridge should adapt to the existing `I_{a,L}` framework.


