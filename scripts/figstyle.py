"""Shared figure style for SuperMatics manuscripts.

Every paper's figure script imports this module so that fonts, colours and
widths match across the series. Figures are saved as vector PDF (for LaTeX)
and SVG (for the web), with TrueType fonts embedded.

    from figstyle import use, figure, save, PALETTE
    use()
    fig, ax = figure("rsc", "single", aspect=0.75)
    ...
    save(fig, "figures/fig2_parity")
"""

from __future__ import annotations

from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt

MM = 1 / 25.4

# Column widths in millimetres, from each publisher's author guide.
WIDTHS_MM = {
    'rsc': {'single': 83.0, 'double': 171.0},  # Digital Discovery and other RSC journals
    'nature': {'single': 88.0, 'double': 180.0},  # npj, Scientific Data, Nature Communications
    'ieee': {'single': 88.9, 'double': 181.9},  # IEEE Transactions (3.5 in / 7.16 in)
    'iop': {'single': 84.0, 'double': 168.0},  # SuST and other IOP journals
    'aps': {'single': 86.0, 'double': 178.0},  # Physical Review
    'springer': {'single': 84.0, 'double': 174.0},  # Springer journals (J. Stat. Phys., Lett. Math. Phys.)
}

# Okabe-Ito, safe for colour-blind readers and in greyscale print.
PALETTE = {
    'ours': '#0072B2',
    'baseline': '#E69F00',
    'reference': '#000000',
    'alt1': '#009E73',
    'alt2': '#CC79A7',
    'alt3': '#56B4E9',
    'alt4': '#D55E00',
    'muted': '#999999',
}


def use() -> None:
    mpl.rcParams.update(
        {
            'font.family': 'sans-serif',
            'font.sans-serif': ['Arial', 'Helvetica', 'DejaVu Sans'],
            'font.size': 7,
            'axes.labelsize': 7,
            'axes.titlesize': 7,
            'xtick.labelsize': 6,
            'ytick.labelsize': 6,
            'legend.fontsize': 6,
            'legend.frameon': False,
            'axes.linewidth': 0.6,
            'lines.linewidth': 1.0,
            'lines.markersize': 3,
            'xtick.major.width': 0.6,
            'ytick.major.width': 0.6,
            'xtick.major.size': 2.5,
            'ytick.major.size': 2.5,
            'xtick.direction': 'out',
            'ytick.direction': 'out',
            'axes.spines.top': False,
            'axes.spines.right': False,
            'axes.prop_cycle': mpl.cycler(color=list(PALETTE.values())),
            'pdf.fonttype': 42,
            'ps.fonttype': 42,
            'svg.fonttype': 'none',
            'svg.hashsalt': 'supermatics',
            'savefig.bbox': 'tight',
            'savefig.pad_inches': 0.02,
        }
    )


def figure(journal: str, width: str = 'single', aspect: float = 0.7, **subplots):
    """Return (fig, axes) sized to a journal column. `aspect` is height / width."""
    w = WIDTHS_MM[journal][width] * MM
    return plt.subplots(figsize=(w, w * aspect), **subplots)


def save(fig, stem: str | Path) -> None:
    """Write stem.pdf and stem.svg without timestamps or random ids, so rebuilds are byte-stable, and close the figure."""
    stem = Path(stem)
    stem.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(stem.with_suffix('.pdf'), metadata={'Creator': None, 'Producer': None, 'CreationDate': None})
    fig.savefig(stem.with_suffix('.svg'), metadata={'Creator': None, 'Date': None})
    plt.close(fig)
