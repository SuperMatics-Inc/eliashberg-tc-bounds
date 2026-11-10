"""Build the journal upload in submission/: one flat main.tex, its bibliography, class files, figures and a supplement zip.

The Springer Nature template asks for a single .tex file without \\input, so values.tex is inlined here.
The script compiles the flat source with Tectonic, keeps main.bbl for the upload, and writes MANIFEST.txt with SHA-256 digests.
Usage: python scripts/flatten.py [--tectonic PATH]
"""

from __future__ import annotations

import argparse
import hashlib
import re
import shutil
import subprocess
import sys
import zipfile
from pathlib import Path

PAPER = Path(__file__).resolve().parents[1]
OUT = PAPER / 'submission'
TECTONIC = Path('D:/dev/tools/tectonic/tectonic.exe')

# Supplement members, relative to the paper folder. Lean build outputs (.lake) are never shipped.
SUPPLEMENT = [
    'lean/lakefile.toml',
    'lean/lake-manifest.json',
    'lean/lean-toolchain',
    'lean/KayProof.lean',
    'lean/AxiomCheck.lean',
    'lean/KayProof/*.lean',
    'certificates/*.py',
    'certificates/*.json',
    'certificates/*.md',
    'scripts/*.py',
    'data/*.json',
]
# Files from outside the paper folder, shipped under the given archive name. The figure scripts look for
# figstyle in ../shared first and fall back to their own folder, so in the supplement it sits beside them.
EXTRA = {PAPER.parent / 'shared' / 'figstyle.py': 'scripts/figstyle.py'}
# Fixed timestamp so the zip is byte-reproducible from the same inputs.
ZIP_TIME = (2026, 1, 1, 0, 0, 0)


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def flatten_tex() -> str:
    src = (PAPER / 'main.tex').read_text(encoding='utf-8')
    values = (PAPER / 'values.tex').read_text(encoding='utf-8')
    marker = '\\input{values.tex}'
    if src.count(marker) != 1:
        sys.exit(f'expected exactly one {marker} in main.tex')
    if re.search(r'\\(input|include)\{', src.replace(marker, '')):
        sys.exit('main.tex has another \\input or \\include; flatten it too')
    src = src.replace(marker, values.strip())
    # The internal header comments (status, provenance, this script) do not belong in the upload.
    head, sep, body = src.partition('\\documentclass')
    if any(line.strip() and not line.startswith('%') for line in head.split('\n')):
        sys.exit('unexpected non-comment text before \\documentclass')
    return sep + body


def build_supplement(dest: Path) -> list[tuple[Path, str]]:
    members: list[tuple[Path, str]] = [(PAPER / 'SUPPLEMENT-README.md', 'README.md')]
    for pattern in SUPPLEMENT:
        hits = sorted(PAPER.glob(pattern))
        if not hits:
            sys.exit(f'supplement pattern matched nothing: {pattern}')
        members.extend((p, p.relative_to(PAPER).as_posix()) for p in hits)
    members.extend(EXTRA.items())
    with zipfile.ZipFile(dest, 'w', zipfile.ZIP_DEFLATED) as zf:
        for path, rel in members:
            info = zipfile.ZipInfo(f'supplement/{rel}', ZIP_TIME)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16
            zf.writestr(info, path.read_bytes())
    return members


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--tectonic', type=Path, default=TECTONIC)
    args = ap.parse_args()

    if OUT.exists():
        shutil.rmtree(OUT)
    (OUT / 'figures').mkdir(parents=True)

    tex = flatten_tex()
    (OUT / 'main.tex').write_text(tex, encoding='utf-8', newline='\n')
    for name in ['refs.bib', 'sn-jnl.cls', 'sn-mathphys-num.bst']:
        shutil.copy2(PAPER / name, OUT / name)
    figures = sorted(set(re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}', tex)))
    for fig in figures:
        shutil.copy2(PAPER / fig, OUT / fig)

    run = subprocess.run(
        [str(args.tectonic), '-X', 'compile', '--keep-intermediates', 'main.tex'],
        cwd=OUT,
        capture_output=True,
        text=True,
    )
    log = run.stdout + run.stderr
    (OUT / 'build.log').write_text(log, encoding='utf-8')
    if run.returncode != 0:
        sys.exit(f'tectonic failed with exit {run.returncode}; see submission/build.log')
    if re.search(r'undefined|Citation .* undefined|Reference .* undefined', log, re.I):
        sys.exit('undefined references or citations; see submission/build.log')
    for junk in ['main.aux', 'main.blg', 'main.log', 'main.out']:
        (OUT / junk).unlink(missing_ok=True)

    members = build_supplement(OUT / 'supplement.zip')

    upload = ['main.tex', 'main.bbl', 'refs.bib', 'sn-jnl.cls', 'sn-mathphys-num.bst', *figures, 'main.pdf', 'supplement.zip']
    lines = ['# SHA-256 of the journal upload (main.pdf is the reference build, not an upload file).']
    lines += [f'{sha(OUT / f)}  {f}' for f in upload]
    lines += ['', '# Supplement members']
    lines += [f'{sha(p)}  {rel}' for p, rel in members]
    (OUT / 'MANIFEST.txt').write_text('\n'.join(lines) + '\n', encoding='utf-8', newline='\n')
    print('\n'.join(lines[: len(upload) + 1]))
    print(f'supplement: {len(members)} files')


if __name__ == '__main__':
    main()
