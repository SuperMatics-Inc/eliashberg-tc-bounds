"""Float (non-rigorous) value of the zeroth-moment constant H_0 = sup_v h(v)/v of Theorem 8.

Nothing in the proofs depends on this file. Writes data/moment_constant.json with H_0, the maximizer v_0,
the resulting Tc/M_0 = H_0/pi, and the optimal Einstein frequency Omega/M_0 and coupling lambda.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as sl
from scipy.optimize import minimize_scalar

OUT = Path(__file__).resolve().parents[1] / 'data' / 'moment_constant.json'


def h(v: float, n: int) -> float:
    """Top eigenvalue of the N x N truncation of the Einstein operator K[a], a_j = v^2/(v^2+j^2)."""
    j = np.arange(2 * n + 2, dtype=float)
    a = v * v / (v * v + j * j)
    a[0] = 0.0
    idx = np.arange(n)
    w = 2.0 * idx + 1.0
    diff = np.abs(idx[:, None] - idx[None, :])
    m = a[diff] * (diff > 0) + a[idx[:, None] + idx[None, :] + 1]
    m = m / np.sqrt(np.outer(w, w))
    cs = np.concatenate([[0.0], np.cumsum(a[1:n])])
    m[idx, idx] -= 2.0 * cs / w
    return float(sl.eigh(m, eigvals_only=True, subset_by_index=[n - 1, n - 1])[0])


def main() -> None:
    rows = []
    for n in (400, 800):
        res = minimize_scalar(lambda v, n=n: -h(v, n) / v, bounds=(0.2, 5.0), method='bounded', options={'xatol': 1e-8})
        h0, v0 = -float(res.fun), float(res.x)
        tc = h0 / math.pi  # Tc / M_0
        omega = 2.0 * math.pi * tc * v0  # Omega / M_0
        rows.append({'N': n, 'H0': h0, 'v0': v0, 'Tc_over_M0': tc, 'Omega_over_M0': omega, 'lambda': 2.0 / omega})
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps({'kind': 'float value, not certified', 'rows': rows}, indent=1))
    for r in rows:
        print(r)


if __name__ == '__main__':
    main()
