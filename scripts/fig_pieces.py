"""Figure 1: sign pattern of the pairing parts T_j, H_j, the diagonal part -D_j and M_j itself.

Exact combinatorial pattern, no numerics. Positive entries are solid, negative entries hatched,
so the sign survives greyscale printing; every cell is a vector rectangle.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from matplotlib.patches import Rectangle

SCRIPT_DIR = Path(__file__).resolve().parent
PAPER = SCRIPT_DIR.parent
sys.path.insert(0, str(PAPER.parent / 'shared'))

from figstyle import PALETTE, figure, save, use  # noqa: E402

N = 10
J = 3


def main() -> None:
    use()
    n = np.arange(N)
    diff = np.abs(n[:, None] - n[None, :])
    toeplitz = (diff == J).astype(int)
    hankel = ((n[:, None] + n[None, :] + 1) == J).astype(int)
    diag = -np.diag((n >= J).astype(int))
    total = toeplitz + hankel + diag
    pos = {'facecolor': PALETTE['ours'], 'edgecolor': 'none'}
    neg = {'facecolor': PALETTE['alt4'], 'edgecolor': 'black', 'linewidth': 0, 'hatch': '/////'}
    fig, axes = figure('springer', 'double', aspect=0.27, ncols=4)
    panels = [
        (toeplitz, r'$T_j$: transfer $|n-m|=j$'),
        (hankel, r'$H_j$: $n+m+1=j$'),
        (diag, r'$-D_j$: diagonal, $n\geq j$'),
        (total, r'$M_j=T_j+H_j-D_j$'),
    ]
    for ax, (mat, title) in zip(axes, panels, strict=True):
        for i, k in zip(*np.nonzero(mat), strict=True):
            style = pos if mat[i, k] > 0 else neg
            ax.add_patch(Rectangle((k - 0.5, i - 0.5), 1, 1, **style))
        ax.set_xlim(-0.5, N - 0.5)
        ax.set_ylim(N - 0.5, -0.5)
        ax.set_aspect('equal')
        ax.set_xticks(np.arange(-0.5, N, 1), minor=True)
        ax.set_yticks(np.arange(-0.5, N, 1), minor=True)
        ax.grid(which='minor', color=PALETTE['muted'], lw=0.25)
        ax.tick_params(which='minor', length=0)
        ax.set_xticks([0, J, N - 1])
        ax.set_yticks([0, J, N - 1])
        ax.set_xlabel(r'$m$')
        ax.set_title(title, pad=3)
        for side in ('top', 'right'):
            ax.spines[side].set_visible(True)
    axes[0].set_ylabel(r'$n$')
    save(fig, PAPER / 'figures' / 'pieces')


if __name__ == '__main__':
    main()
