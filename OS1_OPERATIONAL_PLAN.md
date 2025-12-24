## OS1 (Euclidean Invariance on Fixed Regions) — Operational Plan

**Date**: 2025-12-24  
**Purpose**: Define the next *single, sharply stated classical theorem* needed to close the OS1 blocker in `Yang-Mills.tex`: restoring full Euclidean invariance of the continuum Schwinger functions from lattice hypercubic symmetry, in a way compatible with the AF–free fixed-region NRC spine.

This is the OS1 analogue of `UCIS_OPERATIONAL_PLAN.md` (interface smoothing) and `U1_OPERATIONAL_PLAN.md` (UEI/tightness).

---

## Current status (in this repo)

- **In the manuscript**:
  - `thm:os1-unconditional` exists in `Yang-Mills.tex` and is presented as the primary OS1 route.
  - Two routes are recorded:
    - **Calibrator route (primary)**: `prop:hk-calibrators-constructed` ⇒ `thm:os1-calibrator-route` ⇒ `thm:os1-unconditional`.
    - **Commutator route (cross-check)**: `lem:local-commutator-Oa2` ⇒ `prop:resolvent-from-commutator` ⇒ `thm:emergent-sym` (invokes `TS:sandwich_main`, currently outline-only).
- **What is now explicit (good)**:
  - `YANG_MILLS_PROOF_TRACK.md` now records that the commutator route invokes `TS:sandwich_main`, which is currently only an outline.
- **What remains open (core blocker)**:
  - A referee-grade proof of the required local \(O(a^2)\) commutator control, or a complete calibrator-route argument with hypotheses checked and constants/uniformities recorded.

---

## Goal (“DONE”)

- **DONE means**:
  - OS1 is proved on each fixed region \(R\Subset\mathbb R^4\) along the scaling window, in a way that cleanly composes with U1 tightness and U2 NRC uniqueness.
  - All “outline-only” inputs used by OS1 are either fully proved in-text or replaced by precise external citations with hypotheses matched.
  - The proof tracker OS1 checklist (`YANG_MILLS_PROOF_TRACK.md`, OS1 block) has all subclaims either checked off or cleanly reduced.

---

## Target theorem (OS1 closure target)

> **OS1 (fixed-region Euclidean invariance; closure target).**  
> For every fixed bounded region \(R\Subset\mathbb R^4\), the continuum Schwinger functions \(S_n\) obtained as van Hove limits satisfy
> \[
>   S_n(G\Gamma_1,\dots,G\Gamma_n)\ =\ S_n(\Gamma_1,\dots,\Gamma_n)
> \]
> for all rigid motions \(G\in E(4)\) and loop families \(\{\Gamma_i\}\subset R\).

Operationally, the manuscript implements this via commutation of the continuum generator \(H\) with the Euclidean action \(U(G)\) on the OS/GNS space (resolvent conjugation).

---

## Proof decomposition (crisp failure points)

### OS1-A — Define the lattice action \(U_a(G)\) and its compatibility (STD but must be written)

- **Deliverable**:
  - a concrete definition of how rigid motions act on lattice cylinders/loops/clover fields,
  - proof \(U_a(G)\) is unitary on the OS/GNS quotient,
  - and that it is compatible with the embeddings used in U2.

### OS1-B — Route decision (meta; current choice)

- **Mainline closure**: calibrator route (avoids `TS:sandwich_main`).
- **Cross-check**: commutator route (requires upgrading `TS:sandwich_main` and auditing the finite-stencil Taylor controls it invokes).

### RS correspondence (why the calibrator route is “the right shape”)

RS highlights two structural ingredients that map cleanly to the calibrator approach:

- **8-tick / Q₃ coverage (T6/T7)**: dynamics are organized in blocks of length 8 (a Gray-code walk on the cube), and the 8-step aggregate acts like a *projection onto invariant content* of the cycle.
- **Hyperoctahedral symmetry (B₃, order 48)**: the discrete symmetry of the 3-cube (axis permutations + reflections) is the “finite shadow” of rotational invariance.

Classically, the calibrator route is exactly “project by averaging + let the approximation scale go to 0”:

- **Heat-kernel smoothing** supplies isotropic, class-function regularization on \(G\),
- **Hypercubic averaging** enforces the discrete symmetry at each \(a\),
- and the \(\epsilon\downarrow 0\) limit promotes discrete invariance to full \(SO(4)\) invariance on fixed regions, provided U1 tightness/equicontinuity is real.

### OS1-C (Commutator route) — Local semigroup commutator \(O(a^2 t)\) (RG/LEAP)

Goal: prove a bound of the form
\[
  \|[U_a(G),e^{-tH_{a,L}}]\|_{\mathcal V^{\rm loc}_{0,a,L}(R)}\ \le\ C(R,G)\,a^2\,t\qquad(t\in[0,t_0]).
\]

This route currently depends on:

- **OS1-C1**: a real proof of `TS:sandwich_main` (Strang/sandwich envelope with an \(O(a^2)\) remainder on local cores).
- **OS1-C2**: a real finite-stencil Taylor control for the magnetic part under rigid relabelings (the manuscript references `DEC:plaquette-F2`).
- **OS1-C3**: a clean “local-to-resolvent” upgrade (`prop:resolvent-from-commutator`) and the NRC limit argument (`thm:emergent-sym` / `thm:os1-unconditional`).

### OS1-D (Calibrator route) — Isotropic smoothing + equicontinuity (RG but often cleaner)

Goal: construct isotropic “calibrators” \(\mathcal C_\epsilon\) (heat-kernel smoothing + hypercubic averaging) and show:

- **OS1-D1**: uniform isotropy defect \(O(\epsilon^2)\) for calibrated observables at each lattice \((a,L)\),
- **OS1-D2**: pass \(a\downarrow 0\) using U1 tightness/equicontinuity,
- **OS1-D3**: remove calibration by letting \(\epsilon\downarrow 0\) using the uniform approximation \(\|\mathcal C_\epsilon F-F\|\to 0\).

This route avoids `TS:sandwich_main` but still depends on having a real U1 package (tightness/equicontinuity).

---

## Repo integration checklist (operational)

- [ ] Decide and record the **primary OS1 route** for the main chain (commutator vs calibrator).
- [ ] If commutator route is primary:
  - [ ] Upgrade `TS:sandwich_main` from outline to a full proof block (or mark it as an explicit external input with citation + hypothesis match).
  - [ ] Audit and repair the `DEC:plaquette-F2` dependency so it is a correct finite-stencil/Taylor statement (not a placeholder).
- [ ] If calibrator route is primary:
  - [ ] Audit `prop:hk-calibrators-constructed` / `thm:os1-calibrator-route` for correct uniformities and ensure they only rely on U1 + hypercubic symmetry.
- [ ] Update `YANG_MILLS_PROOF_TRACK.md`:
  - mark OS1 checklist items accordingly,
  - keep the unused route as a clearly labeled cross-check.

---

## Acceptance criteria (non-negotiable)

- **Uniformities**: OS1 must be stated on fixed \(R\) with constants uniform in the van Hove volume and boundary outside \(R\), and must specify exactly what dependence on the scaling schedule is assumed (via U1).
- **No outline-only dependencies** in the chosen mainline route.


