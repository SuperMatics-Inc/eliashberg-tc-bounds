# Sharp bounds on the Eliashberg critical temperature

This supplement accompanies D. Rens, “Sharp bounds on the Eliashberg critical temperature: a comparison principle, convexity in the spectrum, and the Kiessling–Altshuler–Yuzbashyan conjectures” ([arXiv:2611.20496](https://arxiv.org/abs/2611.20496)). Lean formalizes the finite-dimensional core. Two independent calculations certify the Einstein inequality in Appendix A, one in Arb ball arithmetic and the other over the rationals. The archived supplement is [10.5281/zenodo.24270482](https://doi.org/10.5281/zenodo.24270482).

## Contents

| Files | Contents |
|---|---|
| `lean/` | The finite-dimensional proofs in Lean 4 (Section 7.1, Table 1). |
| `certificates/certify_arb.py`, `certificates/receipt-arb.json` | The primary proof of the Einstein inequality in Arb ball arithmetic (Appendix A). |
| `certificates/PROOF-PLAN.md` | The proof plan as it stood before the certificate runs. Appendix A quotes its SHA-256 digest. |
| `certificates/verify_rational.py`, `certificates/receipt-rational.json`, `certificates/RATIONAL-DERIVATION.md` | The independent exact-rational certificate and its derivation (Appendix A). |
| `scripts/values.py` | Generates `values.tex`, the source of the paper's certificate values, from the two JSON files. |
| `scripts/curve_data.py`, `scripts/fig_curves.py`, `data/curve.json` | Floating-point data and plotting code for Figure 2. |
| `scripts/fig_pieces.py` | Figure 1, drawn from the exact sign pattern. |
| `scripts/figstyle.py` | The fonts, Springer column widths and colours shared by the two figures. |
| `scripts/conj3_check.py` | Floating-point and exact-fraction spot checks of the Conjecture 3 theorem on random inputs. |
| `scripts/moment_constant.py`, `data/moment_constant.json` | Floating-point calculations of the zeroth-moment constant $H_0$ in Theorem 8 and the optimal Einstein spectrum, at $N=400$ and $N=800$. |
| `scripts/flatten.py` | Assembles the single-file journal source. |

The floating-point illustrations and spot checks do not enter the proofs. On 9 November 2026, rebuilding the figures in the author's environment reproduced the supplied PDFs byte for byte. Other Matplotlib versions can order PDF objects differently without changing the figures.

## Lean

Requires [elan](https://github.com/leanprover/elan). From `lean/`:

```
lake exe cache get              # downloads the Mathlib build cache
lake build                      # builds the library KayProof
lake env lean AxiomCheck.lean   # prints the axioms of every theorem in Table 1
```

The build uses Lean v4.35.0 and Mathlib v4.35.0. `KayProof/Defs.lean` defines the truncated matrix and its quadratic form, the Rayleigh supremum `kappa`, and the kernels. It also defines the cone and the Conjecture 3 forms. The theorems are in `Rayleigh.lean`, `Cone.lean`, `Mu.lean`, `Comparison.lean` and `Conj3.lean`.

On 9 November 2026 the Lean build finished with linter and deprecation warnings only. The sources used no `sorry`, `admit`, new `axiom` declarations or `native_decide`. All 16 theorems of Table 1 reported the same dependencies: `propext`, `Classical.choice` and `Quot.sound`.

## Certificates

Python 3.11 or later with `numpy` and `python-flint==0.9.0` (FLINT 3.6.0). From `certificates/`:

```
python certify_arb.py --out receipt-arb.json   # prints PASS, about 2 s
python verify_rational.py                      # prints PASS, under 1 s
```

Each script exits with status 0 only when all its inequalities hold. Floating-point linear algebra proposes trial vectors and Cholesky or Gram factors. The scripts convert those objects to exact dyadic or rational data and decide the inequalities in ball or exact rational arithmetic.

On 9 November 2026 both certificates passed from a clean copy on arm64 macOS with Python 3.12, NumPy 2.5.4 and python-flint 0.9.0. The last digits of the trial data differed from the archived values. The accepted inequalities are independent of those platform differences.

## Licence

The code, Lean sources, data and documentation in this supplement are released under the Apache License, Version 2.0 (`LICENSE`).
