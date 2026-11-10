"""Rigorous certificate: sup spec G(v) < g := sup spec G(0) for every v > 0.

Implements PROOF-PLAN.md in this folder (lemmas L1-L8, regions I-III; paper, Appendix A).
All claimed inequalities are decided in Arb ball arithmetic (python-flint); floating point
is used only to *produce* trial objects (trial eigenvector, Cholesky factors), which are then
converted exactly to dyadic Arb balls of radius zero.

Usage: python certify_arb.py [--out receipt-arb.json]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path

import flint
import numpy as np
from flint import arb, arb_mat, ctx, fmpq

ctx.prec = 200

# ---------------------------------------------------------------- parameters (frozen)
N_SMALL = 256  # block size for G0 (region I, q0, g2)
N_MID = 160  # block size for region II cells
V_A = Fraction(1, 4)
V_B = Fraction(4)
GRID_RATIO = 1.06
DYADIC = 2**20
RHO_J = 4000  # explicit terms in rho = sum m_j / j^4


def A(x) -> arb:
    if isinstance(x, Fraction):
        return arb(fmpq(x.numerator, x.denominator))
    return arb(x)


def rep(x: arb) -> str:
    return x.str(20, radius=True)


# ---------------------------------------------------------------- operator pieces
def c_list(v2: arb, kmax: int) -> list:
    """c[k] = 1/(v^2 + k^2) for 1 <= k <= kmax (index 0 unused)."""
    return [arb(0)] + [1 / (v2 + k * k) for k in range(1, kmax + 1)]


def isqrt_w(nmax: int) -> list:
    return [1 / arb(2 * n + 1).sqrt() for n in range(nmax)]


def block_U(vl2: arb, vu2: arb, N: int):
    """First N x N block of U = P(v_l) - D(v_u) (L2); returns (arb_mat, float ndarray)."""
    cl = c_list(vl2, 2 * N)
    cu = c_list(vu2, N)
    isq = isqrt_w(N)
    cum = [arb(0)] * N
    acc = arb(0)
    for n in range(1, N):
        acc += cu[n]
        cum[n] = acc
    M = arb_mat(N, N)
    F = np.empty((N, N))
    for n in range(N):
        for m in range(n, N):
            val = cl[n + m + 1] * isq[n] * isq[m]
            if m != n:
                val += cl[m - n] * isq[n] * isq[m]
            else:
                val -= 2 * cum[n] / (2 * n + 1)
            M[n, m] = val
            M[m, n] = val
            F[n, m] = F[m, n] = float(val.mid())
    return M, F


def T4(K: int) -> arb:
    """Upper bound for sum_{k>=K} k^-4 (K >= 1)."""
    Ka = arb(K)
    return 1 / Ka**4 + 1 / (3 * Ka**3)


def beta_bound(N: int) -> arb:
    """L6: ||B||_F^2 bound for the off block (c_k <= 1/k^2 for every v >= 0)."""
    s = arb(0)
    wN = arb(2 * N + 1)
    for n in range(N):
        s += 2 * (T4(N - n) + T4(N + n + 1)) / (arb(2 * n + 1) * wN)
    return s.sqrt()


def row_tail_bound(n: int, N: int) -> arb:
    """sqrt(sum_{m>=N} (G0_{nm})^2) for n < N (L6 row version)."""
    return (2 * (T4(N - n) + T4(N + n + 1)) / (arb(2 * n + 1) * arb(2 * N + 1))).sqrt()


def S_of(v2: arb) -> arb:
    """S(v) = sum_{k>=1} 1/(v^2+k^2) = (pi v coth(pi v) - 1)/(2 v^2); S(0) = pi^2/6."""
    if v2 == 0:
        return arb.pi() ** 2 / 6
    v = v2.sqrt()
    pv = arb.pi() * v
    return (pv * pv.coth() - 1) / (2 * v2)


def two_by_two(alpha: arb, beta: arb, gamma: arb) -> arb:
    return (alpha + gamma) / 2 + (((alpha - gamma) / 2) ** 2 + beta**2).sqrt()


def chol_cert(M: arb_mat, F: np.ndarray, s: float, tau: float) -> tuple[bool, arb]:
    """L4: certify s I - M > 0 via exact residual of a float Cholesky factor of (s-tau)I - F."""
    N = F.shape[0]
    try:
        L = np.linalg.cholesky((s - tau) * np.eye(N) - F)
    except np.linalg.LinAlgError:
        return False, arb("inf")
    La = arb_mat(L.tolist())  # exact conversion of doubles
    E = -M - La * La.transpose()
    sa, ta = arb(s), arb(tau)
    for i in range(N):
        E[i, i] += sa - ta
    fro2 = arb(0)
    for i in range(N):
        for j in range(N):
            e = E[i, j]
            fro2 += e * e
    return bool(fro2 < ta * ta), fro2.sqrt()


def certify_upper(M: arb_mat, F: np.ndarray, target: float):
    """Find s with sup spec M < s, s chosen between float top eigenvalue and target."""
    lam = float(np.linalg.eigvalsh(F)[-1])
    gap = target - lam
    if gap <= 0:
        return None
    for frac in (0.25, 0.05, 0.01, 0.5):
        s = lam + frac * gap
        tau = 0.5 * (s - lam)
        ok, res = chol_cert(M, F, s, tau)
        if ok:
            return {"lam_float": lam, "s": s, "tau": tau, "res_fro": rep(res)}, arb(s)
    return None


# ---------------------------------------------------------------- stage 0: q0 and trial vector
def stage_g0(log):
    N = N_SMALL
    A0, F0 = block_U(arb(0), arb(0), N)
    ev, V = np.linalg.eigh(F0)
    psi = V[:, -1] * np.sign(V[0, -1])
    P = arb_mat([[float(x)] for x in psi])
    num = (P.transpose() * A0 * P)[0, 0]
    den = (P.transpose() * P)[0, 0]
    q0 = num / den
    nrm = den.sqrt()
    u = [P[i, 0] / nrm for i in range(N)]
    Ua = arb_mat([[x] for x in u])
    r_blk = A0 * Ua
    rb2 = arb(0)
    for i in range(N):
        d = r_blk[i, 0] - q0 * u[i]
        rb2 += d * d
    tail = arb(0)
    for n in range(N):
        tail += abs(u[n]) * row_tail_bound(n, N)
    rho0 = (rb2 + tail * tail).sqrt()
    log(f"q0 = {rep(q0)} (float top eig {ev[-1]!r}); rho0 <= {rep(rho0)}")
    return {"N": N, "A0": A0, "F0": F0, "u": u, "q0": q0, "rho0": rho0, "psi_float": psi}


def stage_g2(st, log):
    """lambda_2(G0) <= sup spec(G0 - t u u^T) with t = q0 (L3-L6)."""
    N = st["N"]
    u, q0 = st["u"], st["q0"]
    Ua = arb_mat([[x] for x in u])
    Ap = st["A0"] - (Ua * Ua.transpose()) * q0
    Fp = np.array([[float(Ap[i, j].mid()) for j in range(N)] for i in range(N)])
    lam = float(np.linalg.eigvalsh(Fp)[-1])
    s = max(lam, 0.0) + 2e-3
    ok, res = chol_cert(Ap, Fp, s, 1e-3)
    if not ok:
        raise SystemExit("FAIL: g2 Cholesky certificate")
    gamma = 3 * S_of(arb(0)) / (2 * N + 1)
    beta = beta_bound(N)
    g2 = two_by_two(arb(s), beta, gamma)
    log(f"g2 <= {rep(g2)} (deflated float top {lam:.3e}, s={s}, beta<={rep(beta)}, gamma<={rep(gamma)})")
    return {"g2": g2, "s": s, "lam_float": lam, "beta": rep(beta), "gamma": rep(gamma), "res_fro": rep(res)}


# ---------------------------------------------------------------- region I
def m_bound(j: int) -> arb:
    return 2 / arb(2 * j + 1).sqrt() + 1 / arb(2 * j - 1).sqrt() + arb(2) / (2 * j + 1)


def stage_region1(st, g2, log):
    N, u, q0, rho0 = st["N"], st["u"], st["q0"], st["rho0"]
    isq = isqrt_w(N)
    va2 = A(V_A * V_A)
    # rho >= ||R(v)|| for all v >= 0
    rho = arb(0)
    for j in range(1, RHO_J + 1):
        rho += m_bound(j) / arb(j) ** 4
    rho += 4 / (3 * arb(RHO_J) ** 3)
    # r~ lower bound: sum_j min(mu_j e_j(0), mu_j e_j(v_a))
    rt = arb(0)
    for j in range(1, 2 * N):
        t = arb(0)
        for n in range(0, N - j):
            t += u[n] * u[n + j] * isq[n] * isq[n + j]
        mu = 2 * t
        for n in range(0, j):
            m = j - 1 - n
            if m < N and n < N:
                mu += u[n] * u[m] * isq[n] * isq[m]
        d = arb(0)
        for n in range(j, N):
            d += u[n] * u[n] / (2 * n + 1)
        mu -= 2 * d
        e0 = 1 / arb(j) ** 4
        ea = 1 / (arb(j) ** 2 * (va2 + j * j))
        x, y = (mu * e0).lower(), (mu * ea).lower()
        rt += x if x < y else y
    delta = arb(2).sqrt() * rho0 / (q0 - g2)
    r = rt - 2 * delta * rho
    gg = q0 - g2 - va2 * rho
    crit = r * gg - va2 * rho * rho
    ok = bool(r > 0) and bool(gg > 0) and bool(crit > 0)
    log(f"Region I: rho<={rep(rho)} r~>={rep(rt)} delta<={rep(delta)} r>={rep(r)} crit={rep(crit)} -> {ok}")
    return ok, {
        "v_a": str(V_A),
        "rho": rep(rho),
        "r_tilde_low": rep(rt),
        "delta": rep(delta),
        "r_low": rep(r),
        "gap_term": rep(gg),
        "criterion": rep(crit),
        "ok": ok,
    }


# ---------------------------------------------------------------- region II
def dy(x: float) -> Fraction:
    return Fraction(round(x * DYADIC), DYADIC)


def grid() -> list[Fraction]:
    pts = [V_A]
    x = float(V_A)
    while True:
        x *= GRID_RATIO
        if x >= float(V_B):
            break
        pts.append(dy(x))
    pts.append(V_B)
    return pts


def cert_cell(vl: Fraction, vu: Fraction, q0: arb, beta: arb, depth: int, cells: list, log) -> bool:
    N = N_MID
    M, F = block_U(A(vl * vl), A(vu * vu), N)
    gamma = 3 * S_of(A(vl * vl)) / (2 * N + 1)
    target = float(q0.lower().mid()) - 1e-6
    # aim s so that the 2x2 bound stays below q0: subtract the beta/gamma inflation estimate
    infl = float(beta.upper().mid()) ** 2 / max(1e-3, float(np.linalg.eigvalsh(F)[-1]) - float(gamma.upper().mid()))
    res = certify_upper(M, F, target - 2 * infl)
    if res is not None:
        info, s = res
        bound = two_by_two(s, beta, gamma)
        if bool(bound < q0):
            cells.append(
                {
                    "vl": str(vl),
                    "vu": str(vu),
                    **info,
                    "gamma": rep(gamma),
                    "bound": rep(bound),
                    "margin_rel": (float(q0.mid()) - float(bound.mid())) / float(q0.mid()),
                    "depth": depth,
                }
            )
            return True
    if depth >= 6:
        log(f"FAIL cell [{vl}, {vu}]")
        return False
    mid = dy((float(vl) + float(vu)) / 2)
    return cert_cell(vl, mid, q0, beta, depth + 1, cells, log) and cert_cell(mid, vu, q0, beta, depth + 1, cells, log)


def stage_region2(q0, log):
    pts = grid()
    beta = beta_bound(N_MID)
    cells: list = []
    ok = True
    for a, b in zip(pts[:-1], pts[1:]):
        if not cert_cell(a, b, q0, beta, 0, cells, log):
            ok = False
            break
    if cells:
        worst = min(cells, key=lambda c: c["margin_rel"])
        log(f"Region II: {len(cells)} cells, ok={ok}, worst rel margin {worst['margin_rel']:.4e} at [{worst['vl']},{worst['vu']}]")
    return ok, {"N": N_MID, "beta": rep(beta), "grid_ratio": GRID_RATIO, "cells": cells, "ok": ok}


# ---------------------------------------------------------------- region III
def stage_region3(q0, log):
    vb2 = A(V_B * V_B)
    bound = 3 * S_of(vb2)
    ok = bool(bound < q0)
    log(f"Region III: v >= {V_B}: sup spec G(v) <= 3 S(v_b) = {rep(bound)} < q0 -> {ok}")
    return ok, {"v_b": str(V_B), "bound": rep(bound), "ok": ok}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(Path(__file__).with_name("receipt-arb.json")))
    args = ap.parse_args()
    t0 = time.time()
    lines: list[str] = []

    def log(s: str) -> None:
        print(s, flush=True)
        lines.append(s)

    st = stage_g0(log)
    g2info = stage_g2(st, log)
    g2 = g2info.pop("g2")
    if not bool(st["q0"] > g2):
        raise SystemExit("FAIL: q0 <= g2")
    ok1, r1 = stage_region1(st, g2, log)
    ok2, r2 = stage_region2(st["q0"], log)
    ok3, r3 = stage_region3(st["q0"], log)
    allok = ok1 and ok2 and ok3
    src = Path(__file__).read_bytes()
    receipt = {
        "theorem": "sup spec G(v) < g = sup spec G(0) for all v > 0 (KAY Einstein bound h(v) < g v^2)",
        "plan": "PROOF-PLAN.md",
        "plan_sha256": hashlib.sha256(Path(__file__).with_name("PROOF-PLAN.md").read_bytes()).hexdigest(),
        "script_sha256": hashlib.sha256(src).hexdigest(),
        "python": sys.version,
        "platform": platform.platform(),
        "flint": flint.__version__,
        "numpy": np.__version__,
        "arb_prec_bits": ctx.prec,
        "q0_lower_bound_of_g": rep(st["q0"]),
        "rho0": rep(st["rho0"]),
        "g2": rep(g2),
        "g2_detail": g2info,
        "region1": r1,
        "region2": r2,
        "region3": r3,
        "PASS": allok,
        "runtime_s": round(time.time() - t0, 1),
        "log": lines,
    }
    Path(args.out).write_text(json.dumps(receipt, indent=1), encoding="utf-8")
    print("PASS" if allok else "FAIL", f"runtime {receipt['runtime_s']} s")
    return 0 if allok else 1


if __name__ == "__main__":
    raise SystemExit(main())
