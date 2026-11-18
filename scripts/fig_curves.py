"""Plot the two panels of Figure 2 from the floating-point data in data/curve.json."""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PAPER = SCRIPT_DIR.parent
sys.path.insert(0, str(PAPER.parent / 'shared'))

from figstyle import PALETTE, figure, save, use  # noqa: E402


def main() -> None:
    use()
    d = json.loads((PAPER / 'data' / 'curve.json').read_text())
    rows = d['rows']
    g = d['g_float_N3000']
    v = [r['v'] for r in rows]

    fig, ax = figure('springer', 'single', aspect=0.62)
    ax.plot(v, [r['ratio'] for r in rows], color=PALETTE['ours'], label=r'$h(\varpi)/(g\,\varpi^2)$')
    ax.axhline(1.0, color=PALETTE['reference'], lw=0.6, ls='--', label='proved bound')
    ax.set(xscale='log', xlabel=r'$\varpi=\Omega/2\pi T$', ylabel=r'$h(\varpi)/(g\,\varpi^2)$', ylim=(0, 1.08))
    ax.legend(loc='lower left')
    save(fig, PAPER / 'figures' / 'ratio')

    fig, ax = figure('springer', 'single', aspect=0.62)
    lam = [1.0 / r['h'] for r in rows]
    tc = [1.0 / (2 * math.pi * r['v']) for r in rows]
    ax.plot(lam, tc, color=PALETTE['ours'], label=r'$T_c/\Omega$, Einstein phonon')
    lb = [min(lam) * (max(lam) / min(lam)) ** (k / 200) for k in range(201)]
    ax.plot(
        lb,
        [math.sqrt(g * x) / (2 * math.pi) for x in lb],
        color=PALETTE['reference'],
        ls='--',
        lw=0.7,
        label=r'$\sqrt{g\lambda}/2\pi$, proved bound',
    )
    ax.set(xscale='log', yscale='log', xlabel=r'$\lambda$', ylabel=r'$T_c/\Omega$')
    ax.legend(loc='upper left')
    save(fig, PAPER / 'figures' / 'tc')


if __name__ == '__main__':
    main()
