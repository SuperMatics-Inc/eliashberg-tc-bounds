# Supplementary material

Supplement to D. Rens, "Sharp bounds on the Eliashberg critical temperature: a comparison principle, convexity in the spectrum, and the Kiessling–Altshuler–Yuzbashyan conjectures", [arXiv:2611.20496](https://arxiv.org/abs/2611.20496) (2026). Not yet peer reviewed.

Release v1.0.0, the files as posted with the arXiv submission, is archived at Zenodo: [doi:10.5281/zenodo.24270482](https://doi.org/10.5281/zenodo.24270482) (all versions: [doi:10.5281/zenodo.24270481](https://doi.org/10.5281/zenodo.24270481)).

## Contents

| Path | What it is |
|---|---|
| `lean/` | Lean 4 formalization of the finite-dimensional core (Section 7.1, Table 1). |
| `certificates/certify_arb.py`, `receipt-arb.json` | Primary computer-assisted proof of the Einstein inequality in Arb ball arithmetic (Appendix A). |
| `certificates/PROOF-PLAN.md` | The plan of the primary certificate, fixed before it was run; its SHA-256 is quoted in Appendix A. |
| `certificates/verify_rational.py`, `receipt-rational.json`, `RATIONAL-DERIVATION.md` | Independent exact-rational certificate and the derivation of its lemmas (Appendix A). |
| `scripts/values.py` | Writes `values.tex`, the only source of the certificate numbers quoted in the paper, from the two receipts. |
| `scripts/curve_data.py`, `scripts/fig_curves.py`, `data/curve.json` | Floating-point data and plotting for Figure 2. No proof uses them. |
| `scripts/fig_pieces.py` | Figure 1 (exact sign pattern, no numerics). |
| `scripts/figstyle.py` | Shared figure style (fonts, Springer column widths, palette) used by both figure scripts. Rebuilding the figures from this archive in the author's environment reproduced the shipped PDFs byte for byte (checked 9 Nov 2026); other matplotlib versions can differ in PDF object order while drawing the same figures. |
| `scripts/conj3_check.py` | Numerical and exact-fraction spot checks of the Conjecture 3 theorem on random inputs. Not part of the proof. |
| `scripts/moment_constant.py`, `data/moment_constant.json` | Floating-point value of the zeroth-moment constant $H_0$ of Theorem 8 and the optimal Einstein spectrum, at $N=400$ and $N=800$. Not certified; no proof uses it. |
| `scripts/flatten.py` | Builds the single-file journal source. |

## Lean

Requires [elan](https://github.com/leanprover/elan). From `lean/`:

```
lake exe cache get              # downloads the Mathlib build cache
lake build                      # builds the library KayProof
lake env lean AxiomCheck.lean   # prints the axioms of every theorem in Table 1
```

The toolchain (`lean-toolchain`) is Lean v4.35.0 and `lakefile.toml` pins Mathlib v4.35.0. `KayProof/Defs.lean` holds every definition the theorem statements use (the truncated matrix, its quadratic form, the Rayleigh supremum `kappa`, kernels, the cone and the Conjecture 3 forms); the statements themselves are in `Rayleigh.lean`, `Cone.lean`, `Mu.lean`, `Comparison.lean` and `Conj3.lean`. On 9 November 2026 `lake build` finished without errors (linter and deprecation warnings only), the source contained no `sorry`, `admit`, `axiom` declarations or `native_decide`, and `AxiomCheck.lean` reported `[propext, Classical.choice, Quot.sound]` for all 16 theorems of Table 1.

## Certificates

Python 3.11 or later with `numpy` and `python-flint==0.9.0` (FLINT 3.6.0). From `certificates/`:

```
python certify_arb.py --out receipt-arb.json   # prints PASS, about 2 s
python verify_rational.py                      # prints PASS, under 1 s
```

Each script exits with status 0 only if every inequality it checks holds. Floating point is used only to propose trial vectors and Cholesky or Gram factors; these are then converted to exact dyadic or rational data, and every accepted inequality is decided in ball or exact rational arithmetic.

The trial data come from floating-point linear algebra and therefore depend on the platform; the accepted inequalities do not. On 9 November 2026 both certificates were rerun from a clean copy of this archive on an arm64 macOS machine (Python 3.12, NumPy 2.5.4, python-flint 0.9.0): both printed PASS and exited with status 0, with trial data that differ from the shipped receipts in the last digits.

## Licence

The code, Lean sources, data and documentation in this supplement are released under the Apache License, Version 2.0 (`LICENSE`).
