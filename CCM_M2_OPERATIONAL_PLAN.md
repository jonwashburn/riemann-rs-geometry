## CCM Route‑3′ (Lean) — M2 via spectral perturbation (Davis–Kahan / min–max) — Operational Plan

**Date**: 2025-12-24  
**Purpose**: Define the *single* classical/analytic theorem‑shape that would discharge CCM “missing step M2” in the Lean Route‑3′ pipeline, and reduce it to a concrete \(\delta/g\to 0\) checklist (perturbation size vs spectral gap).

---

## Where we are in the Lean repo (facts, not hopes)

### The typed “missing steps” already exist

In `RiemannRecognitionGeometry/ExplicitFormula/ConnesConvergenceBundle.lean`:

- **M1** is typed as `ConnesMissingStepSimpleEven`
  - existence + evenness + normalization + uniqueness (simple eigenvalue), via an opaque predicate `IsWeilGroundState`.

- **M2** is typed as `ConnesMissingStep_kLam_approximates_xiLam`
  - uniform approximation on the semilocal interval \([λ^{-1},λ]\):
    \[
      |k_\lambda(u) - c_\lambda\,\xi_\lambda(u)| \le \varepsilon(\lambda),\qquad \varepsilon(\lambda)\to 0.
    \]

### Section‑7 scaffolding exists for “window + tail ⇒ uniform-on-\([λ^{-1},λ]\)” bounds

In `RiemannRecognitionGeometry/ExplicitFormula/ConnesSection7.lean` we already have:

- a clean *shape* lemma to turn a **sup approximation on \([-λ,λ]\)** plus a **tail envelope** into a **uniform semilocal** bound for the E‑map (and thus for `kLamOf`).
- this is exactly the kind of quantitative interface M2 needs later, but **it does not prove M2** by itself (because M2 compares \(k_\lambda\) to the *true ground state* \(\xi_\lambda\)).

### Play A (bridge lemma) is already isolated

In `RiemannRecognitionGeometry/ExplicitFormula/ConnesApproximantsCCM.lean`:

- `tendstoXi_of_exists_intermediate` is the topological glue:
  if we can produce an intermediate \(G_n\to \Xi\) and uniform compact closeness \(F_n\approx G_n\),
  then `CCM.tendstoXi` follows.

So: the Lean side is structurally ready to accept a classical theorem delivering M2.

---

## The new theorem we actually need (the “Davis–Kahan bridge”)

M2 is an eigenvector‑stability statement. The standard closure tool is:

> **Davis–Kahan / sin‑θ theorem (ground‑state version).**  
> If a self‑adjoint operator \(A\) has a simple ground state with spectral gap \(g>0\), and \(B\) is a perturbation with \(\|A-B\|\le \delta\), then the ground states are close:
> \[
>   \operatorname{dist}(u_A,\,u_B)\ \lesssim\ \delta/g.
> \]

### Target statement (usable for M2)

We want a lemma of the following form, with explicit constants:

> **Theorem DK‑GS (explicit ground‑state perturbation).**  
> Let \(H\) be a complex Hilbert space. Let \(A,B : H\to H\) be bounded self‑adjoint operators.
> Assume:
> - \(A\) has a lowest eigenvalue \(\lambda_1\) with a **unit** eigenvector \(u\),
> - the next spectral value satisfies \(\lambda_2(A)\ge \lambda_1+g\) for some \(g>0\) (a gap),
> - \(\|A-B\|\le \delta\) with \(\delta<g/4\).
>
> Then \(B\) has a ground‑state eigenvector \(v\) (unit) and
> \[
>   \|u - e^{i\theta}v\|\ \le\ C\,\frac{\delta}{g}
> \]
> for some universal constant \(C\) (e.g. \(C=2\) or \(4\)), and some phase \(\theta\).

This is the exact *mathematical mechanism* needed to turn “good approximate operator / matrix” into M2.

---

## How DK‑GS turns into M2 (the \(\delta/g\to 0\) checklist)

To instantiate DK‑GS for CCM, we need to identify three objects:

1. **True operator/quadratic form** (paper’s \(Q_{W,\lambda}\))  
   - ground state: \(\xi_\lambda\).

2. **Approximate / computable operator** (finite‑rank / truncated / windowed model)  
   - ground state: \(k_\lambda\) (or a simple transform of it).

3. **Comparison bounds**:
   - **spectral gap** \(g(\lambda)\) for the true object,
   - **perturbation size** \(\delta(\lambda)\) between true and approximate objects,
   - and a regime where \(\delta(\lambda)/g(\lambda)\to 0\).

### What M1 supplies

M1 is exactly: “\(\xi_\lambda\) exists, is normalized/even, and the ground state is simple”.
In DK terms, M1 gives the *existence of a gap* (at least nonzero) — but we still need a **quantitative** lower bound \(g(\lambda)\).

### What M2 becomes under DK‑GS

Assuming:
- \(\|A_\lambda - B_\lambda\|\le \delta(\lambda)\),
- \(A_\lambda\) has gap \(g(\lambda)\),
we get an \(L^2\)-type eigenvector closeness
\[
\|k_\lambda - c_\lambda\,\xi_\lambda\|_{L^2}\ \lesssim\ \delta(\lambda)/g(\lambda).
\]

But M2 is a **sup norm on \([λ^{-1},λ]\)**, so we need one additional analytic upgrade:

> **Regularity upgrade**: an inequality of the form  
> \[
> \|f\|_{L^\infty([λ^{-1},λ])}\ \le\ C_{\rm emb}(\lambda)\,\|f\|_{H^1([λ^{-1},λ])}
> \]
> plus a bound that converts operator‑norm / eigenvector error into \(H^1\) (or a smoothing kernel bound).

So the *full* checklist is:

- **(GAP)**: \(g(\lambda)\) lower bound (quantitative).
- **(PERT)**: \(\delta(\lambda)\) upper bound (quantitative).
- **(RATIO)**: \(\delta(\lambda)/g(\lambda)\to 0\).
- **(REG)**: upgrade the eigenvector error from \(L^2\) to the sup‑norm required by M2.

---

## What we can do immediately (Lean work that is not speculative)

### Step 1 — Formalize DK‑GS in Lean (finite-dimensional first)

The fastest Lean path is a **Hermitian matrix** version:
- For \(A,B\in \mathbb{C}^{n\times n}\) Hermitian,
- with eigenvalues \(\lambda_1\le\lambda_2\le\cdots\),
- prove a bound on the angle between the \(\lambda_1\)-eigenspaces under \(\|A-B\|\).

This can likely be done using:
- min–max characterization of eigenvalues,
- Rayleigh quotient estimates,
- and a projection‑distance bound.

Deliverable: a lemma that outputs \(\|P_A - P_B\|\le C\,\delta/g\) for rank‑1 spectral projections.

### Step 2 — Package a “DK ⇒ M2” helper lemma at the level of `ConnesMissingStep_kLam_approximates_xiLam`

Even if \(A_\lambda\) is not implemented yet, we can prove a **generic wrapper**:

> If there exist \(g(\lambda)\), \(\delta(\lambda)\), and a DK‑type bound producing  
> \(\sup_{u\in[λ^{-1},λ]}|k_\lambda(u)-c_\lambda\xi_\lambda(u)|\le \varepsilon(\lambda)\)  
> with \(\varepsilon(\lambda)\to 0\), then `ConnesMissingStep_kLam_approximates_xiLam` holds.

This is 100% consistent with the repo’s philosophy: keep the “bridge” pure, and isolate the hard analysis into named estimates.

---

## Where the classical difficulty really is

Proving DK‑GS itself is standard. The genuinely new content is supplying:

- a **quantitative spectral gap** \(g(\lambda)\) for the semilocal Weil form,
- a **quantitative perturbation bound** \(\delta(\lambda)\) between the true form and the tractable model,
- and an \(L^2\to L^\infty\) / regularity upgrade on \([λ^{-1},λ]\).

This is the “\(\delta/g\to 0\) or bust” decision procedure:
- if your best plausible bounds give \(\delta(\lambda)/g(\lambda)\not\to 0\), the CCM M2 route fails cleanly;
- if they do give \(\to 0\), you have a concrete, classical program to prove those bounds.

---

## Recommendation (CCM route)

Compared to PSC/KXI, the CCM route has a decisive advantage:

- **The new theorem you must create is a standard‑shape spectral perturbation statement**, and the remaining unknowns are explicit numerical/analytic estimates (\(g(\lambda)\), \(\delta(\lambda)\), regularity).
- This aligns with the existing Lean scaffolding (`ConnesSection7` + Play A bridge), and gives a crisp kill‑switch via \(\delta/g\).


