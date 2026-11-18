"""Compute floating-point data for the plots of h(v)/(g v^2) and Einstein Tc.

The script writes data/curve.json for the figures rather than for the proof.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import scipy.linalg as sl

OUT = Path(__file__).resolve().parents[1] / 'data' / 'curve.json'


def top(v: float, n: int) -> float:
    j = np.arange(2 * n + 2, dtype=float)
    c = 1.0 / (v * v + j * j) if v > 0 else np.where(j > 0, 1.0 / np.maximum(j, 1) ** 2, 0.0)
    if v == 0:
        c[0] = 0.0
    else:
        c[0] = 0.0
    idx = np.arange(n)
    w = 2.0 * idx + 1.0
    diff = np.abs(idx[:, None] - idx[None, :])
    m = c[diff] * (diff > 0) + c[idx[:, None] + idx[None, :] + 1]
    m = m / np.sqrt(np.outer(w, w))
    cs = np.concatenate([[0.0], np.cumsum(c[1:n])])
    m[idx, idx] -= 2.0 * cs / w
    return float(sl.eigh(m, eigvals_only=True, subset_by_index=[n - 1, n - 1])[0])


def main() -> None:
    g = top(0.0, 3000)
    vs = np.geomspace(1e-2, 1e2, 81)
    rows = []
    for v in vs:
        n = int(min(4000, max(800, 40 * v)))
        gv = top(float(v), n)  # sup spec G(v), h = v^2 gv
        rows.append({'v': float(v), 'N': n, 'ratio': gv / g, 'h': float(v * v * gv)})
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps({'kind': 'float illustration, not part of the proof', 'g_float_N3000': g, 'rows': rows}, indent=1))
    print('g', g, 'max ratio', max(r['ratio'] for r in rows))


if __name__ == '__main__':
    main()
