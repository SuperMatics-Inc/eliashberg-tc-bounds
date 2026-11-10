"""Diagnostics for CONJ3-PROOF.md; float checks and exact rational checks.

Run from the paper folder: python scripts/conj3_check.py (needs numpy).
A successful run is not a proof or an independent review.
"""

from fractions import Fraction

import numpy as np


def float_check():
    rng = np.random.default_rng(20261108)
    cases = 0
    for n in (1, 2, 3, 5, 10, 20, 35, 50):
        idx = np.arange(n)
        i, j = idx[:, None], idx[None, :]
        delta = np.abs(i - j)
        d = 2 * idx + 1
        for gamma in (0.1, 0.5, 1.0, 2.0, 4.0, 10.0):
            weights = np.arange(1, 2 * n + 1, dtype=float) ** -gamma
            hankel = weights[i + j]
            toeplitz = np.where(delta > 0, weights[np.maximum(delta, 1) - 1], 0.0)
            diag = np.r_[0.0, 2 * np.cumsum(weights[: n - 1])]
            g = hankel + toeplitz - np.diag(diag)
            prefix_h = hankel.cumsum(0).cumsum(1)
            sizes = np.arange(1, n + 1)
            c = np.diag(prefix_h) / sizes**2
            assert np.all(np.diff(c) < 0), (n, gamma, c)
            a = g - np.diag(c[-1] * d)
            prefix_a = a.cumsum(0).cumsum(1)
            lower = sizes[:, None] ** 2 * (c[:, None] - c[-1])
            mask = np.triu(np.ones((n, n), dtype=bool))
            assert np.all((prefix_a - lower)[mask] >= -1e-9), (n, gamma)
            for _ in range(100):
                theta = np.sort(rng.random(n))[::-1]
                lhs = theta @ a @ theta
                assert lhs >= -1e-9, (n, gamma, lhs)
            cases += 1
    print(f'Float: {cases} N/gamma cases; all prefix pairs and 100 random vectors per case passed')


def exact_check():
    cases = 0
    for n in (1, 2, 3, 5, 8, 12):
        for gamma in (1, 2, 3, 5):
            w = [None] + [Fraction(1, k**gamma) for k in range(1, 2 * n)]
            c = [None] + [sum((w[i + j + 1] for i in range(a) for j in range(a)), Fraction()) / (a * a) for a in range(1, n + 1)]
            assert all(c[a] > c[a + 1] for a in range(1, n)), (n, gamma)
            g = [
                [(w[abs(i - j)] if i != j else -2 * sum(w[1 : i + 1], Fraction())) + w[i + j + 1] for j in range(n)]
                for i in range(n)
            ]
            for a in range(1, n + 1):
                for b in range(a, n + 1):
                    value = sum((g[i][j] for i in range(a) for j in range(b)), Fraction()) - c[n] * a * a
                    assert value >= a * a * (c[a] - c[n]), (n, gamma, a, b)
                    if a < n:
                        assert value > 0
                    else:
                        assert value == 0
            # Exact rational decreasing test vectors, including constants and zeros.
            for seed in range(12):
                theta = sorted((Fraction((seed * 11 + k * 7) % 19, 19) for k in range(n)), reverse=True)
                value = sum((theta[i] * g[i][j] * theta[j] for i in range(n) for j in range(n)), Fraction()) - c[n] * sum(
                    ((2 * i + 1) * theta[i] ** 2 for i in range(n)), Fraction()
                )
                assert value >= 0, (n, gamma, seed)
                assert (value == 0) == (len(set(theta)) == 1), (n, gamma, seed)
            cases += 1
    print(f'Exact fractions: {cases} N/gamma cases; all prefix pairs and 12 rational vectors per case passed')


if __name__ == '__main__':
    float_check()
    exact_check()
