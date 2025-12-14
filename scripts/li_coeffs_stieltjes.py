#!/usr/bin/env python3
"""Compute Li coefficients λ_n via Stieltjes/polygamma series.

We use the standard definition:

  λ_n = (1/(n-1)!) * d^n/ds^n [ s^(n-1) * log ξ(s) ] at s = 1,

with Lagarias' normalization

  ξ(s) = (1/2) * s * (s-1) * π^(-s/2) * Γ(s/2) * ζ(s).

Numerically, we expand log ξ(1+ε) = Σ_{m≥0} a_m ε^m to order N, then

  λ_n = n * [ε^n] ((1+ε)^(n-1) * log ξ(1+ε))
      = n * Σ_{k=1..n} binom(n-1, k-1) * a_k.

The only delicate piece is the ζ(s) pole at s=1. We cancel it analytically by writing

  ζ(1+ε) = 1/ε + analytic,
  g(ε) := ε ζ(1+ε) = 1 + analytic,
  log ζ(1+ε) + log ε = log g(ε).

So log ξ(1+ε) is analytic and computable from:
- log(1+ε)
- log Γ((1+ε)/2) via polygamma derivatives
- log g(ε) via Stieltjes constants

Requires: mpmath.
"""

from __future__ import annotations

import argparse
import math
from typing import List

from mpmath import mp


def _log_series_of_g_from_stieltjes(N: int) -> List[mp.mpf]:
    """Return coefficients c[0..N] for log g(ε), where g(ε) = ε ζ(1+ε) = 1 + O(ε)."""
    # g(ε) = 1 + Σ_{m>=1} b_m ε^m, with b_m = (-1)^(m-1) * γ_{m-1} / (m-1)!
    b: List[mp.mpf] = [mp.mpf(0)] * (N + 1)
    b[0] = mp.mpf(1)
    for m in range(1, N + 1):
        k = m - 1
        b[m] = (mp.mpf(-1) ** k) * mp.stieltjes(k) / mp.factorial(k)

    # g'(ε)
    gp: List[mp.mpf] = [mp.mpf(0)] * N
    for m in range(0, N):
        gp[m] = mp.mpf(m + 1) * b[m + 1]

    # invg = 1/g (since b[0]=1)
    invg: List[mp.mpf] = [mp.mpf(0)] * (N + 1)
    invg[0] = mp.mpf(1)
    for m in range(1, N + 1):
        s = mp.mpf(0)
        for k in range(1, m + 1):
            s += b[k] * invg[m - k]
        invg[m] = -s

    # h = g'/g
    h: List[mp.mpf] = [mp.mpf(0)] * N
    for m in range(0, N):
        s = mp.mpf(0)
        for k in range(0, m + 1):
            s += gp[k] * invg[m - k]
        h[m] = s

    # integrate h to get log g
    c: List[mp.mpf] = [mp.mpf(0)] * (N + 1)
    c[0] = mp.mpf(0)
    for m in range(0, N):
        c[m + 1] = h[m] / mp.mpf(m + 1)

    return c


def log_xi_series_at_one(N: int) -> List[mp.mpf]:
    """Return coefficients a[0..N] for log ξ(1+ε) = Σ a_m ε^m."""
    logg = _log_series_of_g_from_stieltjes(N)

    a: List[mp.mpf] = [mp.mpf(0)] * (N + 1)
    a[0] = mp.log(mp.mpf(1) / 2)  # cancellation makes other constants vanish

    log_pi = mp.log(mp.pi)
    half = mp.mpf(1) / 2
    x0 = half

    for m in range(1, N + 1):
        # log(1+ε)
        log1p = (mp.mpf(-1) ** (m - 1)) / mp.mpf(m)

        # -(1+ε)/2 * log π contributes only at order 1
        pi_term = -half * log_pi if m == 1 else mp.mpf(0)

        # log Γ((1+ε)/2)
        # d^m/dε^m log Γ((1+ε)/2) at 0 is (1/2)^m * ψ^{(m-1)}(1/2)
        gamma_term = (half**m) * mp.polygamma(m - 1, x0) / mp.factorial(m)

        a[m] = log1p + pi_term + gamma_term + logg[m]

    return a


def li_coeffs(N: int, dps: int) -> List[mp.mpf]:
    """Compute λ_1..λ_N at precision `dps` using the series method."""
    mp.dps = dps
    a = log_xi_series_at_one(N)
    out: List[mp.mpf] = []

    for n in range(1, N + 1):
        s = mp.mpf(0)
        for k in range(1, n + 1):
            s += mp.mpf(math.comb(n - 1, k - 1)) * a[k]
        out.append(mp.mpf(n) * s)

    return out


def main() -> int:
    p = argparse.ArgumentParser(description="Compute Li coefficients via Stieltjes/polygamma series")
    p.add_argument("-N", "--N", type=int, default=50, help="Compute λ_1..λ_N")
    p.add_argument("--dps", type=int, default=80, help="mpmath decimal digits of precision")
    p.add_argument("--show-all", action="store_true", help="Print all λ_n values")
    args = p.parse_args()

    N = args.N
    if N < 1:
        raise SystemExit("N must be ≥ 1")

    lambdas = li_coeffs(N=N, dps=args.dps)

    # Report summary
    mn = min(lambdas)
    mn_n = 1 + min(range(len(lambdas)), key=lambda i: lambdas[i])
    print(f"computed λ_1..λ_{N} at dps={args.dps}")
    print(f"min λ_n over n≤{N}: λ_{mn_n} = {mn}")

    if args.show_all:
        for i, v in enumerate(lambdas, start=1):
            print(f"λ_{i} = {v}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
