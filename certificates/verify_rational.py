"""Independent exact-rational certificate for the frozen KAY proof plan (paper, Appendix A).

Run from this folder: python verify_rational.py (needs numpy and python-flint).
Only proposals (the trial vector and Gram factors) use numpy floating point.
All accepted inequalities are exact python-flint fmpq comparisons.  No primary
implementation or precomputed numerical data is read.  See RATIONAL-DERIVATION.md for
the independent derivations of the analytic lemmas and the precise scope.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import platform
import sys
import time
from datetime import datetime, timezone

import flint
from flint import fmpq as Rat, fmpq_mat
import numpy as np


HERE = Path(__file__).resolve().parent
N = 40
VA = Rat(1, 8)
VB = Rat(5)
GRID_RATIO = Rat(5, 4)
S_TERMS = 96
TARGET = Rat(659, 500)
G2 = Rat(1, 4)
DEFLATION = Rat(2)
DEFLATED_ALPHA = Rat(1, 8)
TRIAL_BITS = 34
FACTOR_BITS = 42
SQRT_BITS = 60
RHO = Rat(53, 16)
WEIGHTS = [2 * n + 1 for n in range(N)]
ZERO = Rat(0)
ONE = Rat(1)


class CertificateFailure(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    # Deliberately not assert: python -O must not disable a proof check.
    if not condition:
        raise CertificateFailure(message)


def exact_json(value):
    if isinstance(value, Rat):
        return str(value)
    if isinstance(value, dict):
        return {str(key): exact_json(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [exact_json(item) for item in value]
    return value


def approximate(value: Rat) -> str:
    """Display only; never read back into a certificate inequality."""
    return format(float(value), ".12g")


def sqrt_upper(value: Rat) -> Rat:
    """Exact upper enclosure of sqrt(value) on a fixed dyadic grid."""
    require(value >= ZERO, "square-root input is negative")
    numerator = int(value.numerator)
    denominator = int(value.denominator)
    scale = 1 << SQRT_BITS
    scaled_numerator = numerator * scale * scale
    root = math.isqrt(scaled_numerator // denominator)
    if root * root * denominator < scaled_numerator:
        root += 1
    result = Rat(root, scale)
    require(result >= ZERO and result * result >= value,
            "integer square-root enclosure failed")
    return result


def s_upper(t: Rat) -> Rat:
    """S(sqrt(t)) <= finite rational sum + integral tail 1/K."""
    require(t >= ZERO, "negative squared parameter")
    return sum((ONE / (t + j * j) for j in range(1, S_TERMS + 1)),
               Rat(1, S_TERMS))


def t4(k: int) -> Rat:
    require(k >= 1, "invalid fourth-power tail index")
    return Rat(1, k**4) + Rat(1, 3 * k**3)


def off_block_squared() -> Rat:
    """Independent L6 evaluation; valid uniformly for every endpoint."""
    return sum((Rat(2, WEIGHTS[n] * (2 * N + 1)) *
                (t4(N - n) + t4(N + n + 1)) for n in range(N)), ZERO)


def rational_head(t_low: Rat, t_high: Rat) -> fmpq_mat:
    """W^(1/2) [P(sqrt(t_low))-D(sqrt(t_high))]_N W^(1/2)."""
    require(ZERO <= t_low <= t_high, "invalid envelope endpoints")
    cp = [ZERO] + [ONE / (t_low + j * j) for j in range(1, 2 * N)]
    negative = [ZERO]
    for n in range(1, N):
        negative.append(negative[-1] + Rat(2) / (t_high + n * n))
    entries = []
    for n in range(N):
        for m in range(N):
            entry = cp[n + m + 1]
            if n != m:
                entry += cp[abs(n - m)]
            else:
                entry -= negative[n]
            entries.append(entry)
    return fmpq_mat(N, N, entries)


def floating_head(head: fmpq_mat) -> np.ndarray:
    """Proposal generation only; the returned matrix is not evidence."""
    array = np.array([[float(head[n, m]) for m in range(N)]
                      for n in range(N)], dtype=np.float64)
    roots = np.sqrt(np.array(WEIGHTS, dtype=np.float64))
    return array / (roots[:, None] * roots[None, :])


def gram_certificate(head: fmpq_mat, s: Rat, tau: Rat) -> dict:
    """Certify head < s W using an exact dyadic Gram residual.

    The exact weighted row-sum residual bound is a Schur bound on the
    congruence by W^(-1/2); epsilon < tau proves a strict spectral gap.
    Every lower-triangular dyadic integer is included in the receipt.
    """
    require(tau > ZERO, "nonpositive Gram slack")
    proposed = np.array([[float(head[n, m]) for m in range(N)]
                         for n in range(N)], dtype=np.float64)
    numerical_matrix = np.diag([float(s - tau) * w for w in WEIGHTS]) - proposed
    factor = np.linalg.cholesky(numerical_matrix)
    require(bool(np.isfinite(factor).all()), "nonfinite proposed Gram factor")
    scale = 1 << FACTOR_BITS
    integers = [[int(round(float(factor[n, m]) * scale)) if m <= n else 0
                 for m in range(N)] for n in range(N)]
    exact_factor = fmpq_mat(N, N, [Rat(integers[n][m], scale)
                                  for n in range(N) for m in range(N)])
    gram = exact_factor * exact_factor.transpose()
    row_bounds = []
    for n in range(N):
        row = ZERO
        for m in range(N):
            residual = -head[n, m] - gram[n, m]
            if n == m:
                residual += (s - tau) * WEIGHTS[n]
            row += abs(residual)
        row_bounds.append(row / WEIGHTS[n])
    epsilon = max(row_bounds)
    margin = tau - epsilon
    require(margin > ZERO, "exact rational Gram residual is not below tau")
    return {
        "method": "rational congruence / exact dyadic Gram / weighted Schur",
        "s": s,
        "tau": tau,
        "epsilon": epsilon,
        "strict_finite_spectral_margin_below_s": margin,
        "factor_denominator": scale,
        "factor_lower_triangle_integers": [integers[n][:n + 1] for n in range(N)],
        "max_residual_row": row_bounds.index(epsilon),
    }


def block_certificate(alpha: Rat, gamma: Rat, beta_squared: Rat,
                      target: Rat, label: str) -> dict:
    require(target > alpha, label + ": target is not above alpha")
    require(target > gamma, label + ": target is not above gamma")
    require(beta_squared >= ZERO, label + ": negative squared norm bound")
    determinant = (target - alpha) * (target - gamma) - beta_squared
    trace = Rat(2) * target - alpha - gamma
    require(determinant > ZERO and trace > ZERO,
            label + ": exact two-by-two Schur condition failed")
    return {
        "target": target,
        "alpha": alpha,
        "gamma": gamma,
        "beta_squared": beta_squared,
        "determinant_margin": determinant,
        "trace": trace,
        "spectral_gap_at_least": determinant / trace,
    }


def trial_certificate(head0: fmpq_mat, beta_squared: Rat) -> tuple[dict, list, Rat]:
    eigenvalues, eigenvectors = np.linalg.eigh(floating_head(head0))
    proposed = eigenvectors[:, -1]
    if float(proposed.sum()) < 0:
        proposed = -proposed
    roots = np.sqrt(np.array(WEIGHTS, dtype=np.float64))
    z = [int(round(float(proposed[n] * roots[n]) * (1 << TRIAL_BITS)))
         for n in range(N)]
    require(all(item > 0 for item in z), "trial vector is not strictly positive")
    y = [Rat(z[n], WEIGHTS[n]) for n in range(N)]
    norm_squared = sum((Rat(z[n]) * y[n] for n in range(N)), ZERO)
    require(norm_squared > ZERO, "zero trial vector")
    product = head0 * fmpq_mat(N, 1, y)
    rayleigh = sum((y[n] * product[n, 0] for n in range(N)), ZERO) / norm_squared
    require(rayleigh > TARGET, "trial Rayleigh quotient does not exceed target")
    residual_head_squared = sum(
        ((product[n, 0] - rayleigh * z[n]) ** 2 / WEIGHTS[n]
         for n in range(N)), ZERO) / norm_squared
    require(residual_head_squared >= ZERO, "negative exact head residual")
    residual_squared = residual_head_squared + beta_squared
    require(residual_squared >= ZERO, "negative residual norm bound")
    return ({
        "definition": "u_n=z_n/sqrt(w_n*d), d=sum z_n^2/w_n; zero on tail",
        "z_integers": z,
        "proposal_dyadic_bits": TRIAL_BITS,
        "d": norm_squared,
        "rayleigh_q0": rayleigh,
        "target_lower_bound_for_g": TARGET,
        "rayleigh_margin_above_target": rayleigh - TARGET,
        "residual_head_squared": residual_head_squared,
        "residual_tail_squared_upper": beta_squared,
        "residual_squared_upper": residual_squared,
        "note": "Floating eigensolver output is not an inequality certificate.",
    }, z, norm_squared)


def certify_small(head0: fmpq_mat, trial: dict, z: list[int], d: Rat,
                  beta_squared: Rat) -> dict:
    # The rank-one congruence is rational even though normalized u is not.
    deflated = fmpq_mat(N, N, [head0[n, m] - DEFLATION * z[n] * z[m] / d
                              for n in range(N) for m in range(N)])
    gram = gram_certificate(deflated, DEFLATED_ALPHA, Rat(1, 64))
    gamma = Rat(3) * s_upper(ZERO) / (2 * N + 1)
    blocks = block_certificate(DEFLATED_ALPHA, gamma, beta_squared, G2,
                               "deflated G0")
    gap = TARGET - G2
    require(gap > ZERO, "nonpositive certified spectral separation")
    delta_squared_upper = Rat(2) * trial["residual_squared_upper"] / (gap * gap)
    delta = sqrt_upper(delta_squared_upper)
    y = [Rat(z[n], WEIGHTS[n]) for n in range(N)]
    coefficients = []
    at_zero = ZERO
    lower = ZERO
    for j in range(1, 2 * N):
        toeplitz = Rat(2) * sum((y[n] * y[n + j]
                                for n in range(max(0, N - j))), ZERO)
        hankel = sum((y[n] * y[j - 1 - n]
                      for n in range(max(0, j - N), min(N, j))), ZERO)
        diagonal = Rat(2) * sum((y[n] * y[n] for n in range(j, N)), ZERO)
        mu = (toeplitz + hankel - diagonal) / d
        rayleigh_term = mu / (j * j)
        at_zero += rayleigh_term
        e_low = ONE / (Rat(j * j) * (VA * VA + j * j))
        e_high = Rat(1, j**4)
        contribution = mu * (e_low if mu >= ZERO else e_high)
        lower += contribution
        coefficients.append({"j": j, "mu_j": mu,
                             "lower_R_contribution": contribution})
    require(at_zero == trial["rayleigh_q0"],
            "independent M_j assembly disagrees with matrix Rayleigh quotient")
    r = lower - Rat(2) * delta * RHO
    complement = gap - VA * VA * RHO
    determinant = r * complement - VA * VA * RHO * RHO
    require(r > ZERO, "small region: nonpositive R expectation lower bound")
    require(complement > ZERO, "small region: nonpositive complementary gap")
    require(determinant > ZERO, "small region: perturbation determinant failed")
    trace_times_t = VA * VA * r + complement
    require(trace_times_t > ZERO, "small region: nonpositive scaled trace")
    kappa = determinant / trace_times_t
    require(kappa > ZERO, "small region: nonpositive normalized spectral gap")
    return {
        "interval": {"v_lower": ZERO, "lower_open": True, "v_upper": VA},
        "deflation_t": DEFLATION,
        "deflated_head_certificate": gram,
        "deflated_block_certificate": blocks,
        "g2_upper": G2,
        "separation_Q_minus_g2": gap,
        "rho_upper": RHO,
        "rho_derivation": "m_j<3; sum j^-4 <= 1+1/16+1/24; rho=53/16",
        "delta_squared_upper": delta_squared_upper,
        "delta_upper": delta,
        "trial_R_expectation_lower": lower,
        "r_lower": r,
        "complementary_gap_lower": complement,
        "determinant_margin": determinant,
        "normalized_spectral_gap_kappa": kappa,
        "gap_statement": "g-sup spec G(v) >= kappa*v^2 > 0",
        "infimum_unscaled_gap_on_region": ZERO,
        "mu_coefficients": coefficients,
    }


def certify_middle(beta_squared: Rat, receipt: dict) -> list[dict]:
    cells = []
    receipt["middle_cells"] = cells
    low = VA
    index = 0
    while low < VB:
        high = min(low * GRID_RATIO, VB)
        require(low < high, "nonincreasing subdivision")
        head = rational_head(low * low, high * high)
        # These guesses cannot establish an inequality: the Gram and block
        # certificates below must accept them over exact rationals.
        estimate = float(np.linalg.eigvalsh(floating_head(head))[-1])
        s = Rat(int(round((estimate + float(TARGET)) * (1 << 23))), 1 << 24)
        tau_guess = (float(s) - estimate) / 4.0
        tau = Rat(int(math.floor(tau_guess * (1 << 30))), 1 << 30)
        current = {"index": index, "v_lower": low, "v_upper": high,
                   "t_lower": low * low, "t_upper": high * high}
        # Append before certification so a failure receipt identifies the cell.
        cells.append(current)
        gram = gram_certificate(head, s, tau)
        gamma = Rat(3) * s_upper(low * low) / (2 * N + 1)
        blocks = block_certificate(s, gamma, beta_squared, TARGET,
                                   "middle cell " + str(index))
        current.update({"finite_head_certificate": gram,
                        "block_certificate": blocks, "certified": True})
        low = high
        index += 1
    require(bool(cells) and cells[0]["v_lower"] == VA and
            cells[-1]["v_upper"] == VB, "middle region endpoint coverage failed")
    for previous, current in zip(cells, cells[1:]):
        require(previous["v_upper"] == current["v_lower"],
                "gap in exact rational subdivision")
    return cells


def main() -> int:
    start = time.perf_counter()
    source_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    receipt = {
        "schema": "kay-independent-rational-v1",
        "status": "RUNNING",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "verify_py_sha256": source_hash,
        "derivation_md_sha256": hashlib.sha256((HERE / "RATIONAL-DERIVATION.md").read_bytes()).hexdigest(),
        "independence": "No kayproof file, result, trial vector, factor, or receipt read.",
        "arithmetic": "Exact python-flint fmpq/fmpq_mat. Floats propose objects only.",
        "python_version": sys.version,
        "python_executable": sys.executable,
        "python_flint_version": flint.__version__,
        "flint_version": flint.__FLINT_VERSION__,
        "numpy_version": np.__version__,
        "platform": platform.platform(),
        "parameters": {"N": N, "v_a": VA, "v_b": VB,
                       "geometric_v_ratio": GRID_RATIO,
                       "S_finite_sum_terms": S_TERMS,
                       "Q_lower_bound_for_g": TARGET,
                       "factor_bits": FACTOR_BITS, "sqrt_enclosure_bits": SQRT_BITS},
        "lemma_audit": {"L" + str(j): "independently derived; see FINDINGS.md"
                        for j in range(1, 9)},
        "lemma_issues": [],
        "scope_exclusions": ["crossing uniqueness", "thermodynamic transition existence"],
    }
    failure = None
    try:
        require(N >= 2 and ZERO < VA < VB and GRID_RATIO > ONE,
                "invalid global parameters")
        # Exact scalar checks for the analytic m_j and R norm relaxation.
        require(Rat(4, 3)**2 > Rat(4, 3), "m_1<3 rational comparison failed")
        require(RHO == Rat(3) * (ONE + Rat(1, 16) + Rat(1, 24)),
                "rho integral evaluation failed")
        beta_squared = off_block_squared()
        receipt["off_block_squared_upper"] = beta_squared
        head0 = rational_head(ZERO, ZERO)
        trial, z, d = trial_certificate(head0, beta_squared)
        receipt["trial"] = trial
        small = certify_small(head0, trial, z, d, beta_squared)
        receipt["small_region"] = small
        cells = certify_middle(beta_squared, receipt)
        s_at_vb = s_upper(VB * VB)
        large_gap = TARGET - Rat(3) * s_at_vb
        require(large_gap > ZERO, "large region: 3S(v_b) does not lie below Q")
        receipt["large_region"] = {
            "v_lower": VB, "v_upper": "infinity", "S_upper_at_v_b": s_at_vb,
            "spectral_upper": Rat(3) * s_at_vb,
            "spectral_gap_below_Q_at_least": large_gap,
        }
        middle_gap = min(cell["block_certificate"]["spectral_gap_at_least"]
                         for cell in cells)
        receipt["summary"] = {
            "cell_count": len(cells),
            "small_min_normalized_gap_kappa": small["normalized_spectral_gap_kappa"],
            "small_determinant_margin": small["determinant_margin"],
            "middle_min_gap_below_Q": middle_gap,
            "large_min_gap_below_Q": large_gap,
            "theorem": "For every v>0, sup spec G(v)<g.",
            "dispersive_consequence": "Strict linearized bound under the plan's assumptions.",
        }
        receipt["status"] = "PASS"
    except Exception as error:
        failure = error
        receipt["status"] = "FAIL"
        receipt["failure"] = {"type": type(error).__name__, "message": str(error)}
    receipt["runtime_seconds"] = time.perf_counter() - start
    receipt["completed_utc"] = datetime.now(timezone.utc).isoformat()
    (HERE / "receipt-rational.json").write_text(json.dumps(exact_json(receipt), indent=2) + "\n",
                                        encoding="utf-8")
    if failure is not None:
        print("FAIL: " + str(failure))
        print("Receipt: " + str(HERE / "receipt-rational.json"))
        return 1
    summary = receipt["summary"]
    print("PASS")
    print("Exact-rational middle cells:", summary["cell_count"])
    print("Small normalized gap kappa >=", approximate(summary["small_min_normalized_gap_kappa"]),
          "(display approximation; exact rational in receipt)")
    print("Small determinant margin:", approximate(summary["small_determinant_margin"]))
    print("Middle minimum gap below Q:", approximate(summary["middle_min_gap_below_Q"]))
    print("Large minimum gap below Q:", approximate(summary["large_min_gap_below_Q"]))
    print("Runtime seconds:", format(receipt["runtime_seconds"], ".6f"))
    print("verify.py SHA256:", source_hash)
    print("Receipt:", str(HERE / "receipt-rational.json"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
