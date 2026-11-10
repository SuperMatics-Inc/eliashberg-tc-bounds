# Computer-assisted proof plan: KAY Einstein bound h(v) < g v^2 for all v > 0

Status: plan frozen 2026-11-09 before any rigorous certificate was run. Exploratory float numerics
(explore1.py, explore2.py) only.

## Objects
Index n, m >= 0, w_n = 2n+1. For v >= 0, j >= 1: c_j(v) = 1/(v^2 + j^2).
G(v)_{nm} = [(1-δ_nm) c_|n-m| + c_{n+m+1}] / sqrt(w_n w_m) - δ_nm (2/w_n) Σ_{j=1}^n c_j.
H(v) = v^2 G(v) is the KAY Einstein operator (entries [[j]] = v^2/(v^2+j^2)); h(v) = sup spec H(v).
G0 := G(0) (entries with c_j = 1/j^2); g := sup spec G0 (claimed = g(2) of KAY, 1.3181402...).
Decomposition: G(v) = Σ_j c_j(v) M_j, M_j = T_j + H_j - D_j with
(T_j)_{nm} = [|n-m| = j]/sqrt(w_n w_m), (H_j)_{nm} = [n+m+1 = j]/sqrt(w_n w_m), (D_j)_{nn} = 2[n >= j]/w_n.
P(v) := Σ c_j(v)(T_j + H_j) >= 0 entrywise, D(v) := Σ c_j(v) D_j >= 0 diagonal. G = P - D.
All G(v) are compact self-adjoint on l^2 (Hilbert-Schmidt part + diagonal tending to 0).

Main Theorem: for every v > 0, sup spec G(v) < g. Equivalently h(v) < g v^2.

## Lemmas
L1 (absolute values). <x,G x> <= <|x|,P|x|> - <|x|,D|x|>.
L2 (envelope). For 0 <= v_l <= v <= v_u: c_j(v_l) >= c_j(v) >= c_j(v_u), so
  sup spec G(v) <= sup_{x>=0} <x,U x>/|x|^2 <= sup spec U, U := P(v_l) - D(v_u).
L3 (block). U = [[A,B],[B^T,C]] (first N coords / tail). If α >= sup spec A, γ >= sup spec C,
  β >= ||B|| then sup spec U <= (α+γ)/2 + sqrt(((α-γ)/2)^2 + β^2).
L4 (Cholesky certificate). If L is exact (dyadic) and τ > 0 with ||(sI-A) - τI - L L^T||_F < τ
  (rigorous ball enclosure), then sI - A > 0, so sup spec A < s.
L5 (tail Schur test, weights w^{-1/2}). sup spec C <= ||C_P|| <= sup_{n>=N} Σ_{m>=N} [(1-δ)c_|n-m| + c_{n+m+1}]/w_m
  <= 3 S(v_l)/w_N, S(v) := Σ_{k>=1} c_k(v) = (π v coth(π v) - 1)/(2 v^2) (S(0) = ζ(2)).
L6 (off block). B involves only P. ||B||^2 <= ||B||_F^2 <= Σ_{n<N} (2/(w_n w_N)) [T4(N-n) + T4(N+n+1)],
  T4(K) := K^-4 + 1/(3K^3) >= Σ_{k>=K} k^-4 >= Σ_{k>=K} c_k^2.
L7 (large v). sup spec G(v) <= ||P(v)|| <= 3 S(v) (same Schur test over all n); S decreasing.
L8 (small v). G0 - G(v) = v^2 R(v), R(v) = Σ_j e_j(v) M_j, e_j(v) = 1/(j^2(v^2+j^2)) in [1/(j^2(v_a^2+j^2)), j^-4].
  ||M_j|| <= m_j := 2/sqrt(2j+1) + 1/sqrt(2j-1) + 2/(2j+1); ρ := Σ_j m_j j^-4 >= ||R(v)|| for all v.
  Let ψ be the unit top eigenvector of G0 (g simple), g2 >= sup spec G0 on ψ^⊥. For unit x = aψ + bφ (φ ⊥ ψ):
  <x,(gI - G(v))x> >= (g-g2) b^2 + v^2 (r a^2 - 2ρ|a||b| - ρ b^2), r := inf_{0<v<=v_a} <ψ,R(v)ψ>.
  Positive definite (uniformly) for all v in (0, v_a] if r > 0, g-g2-v_a^2ρ > 0 and r(g-g2-v_a^2ρ) > v_a^2 ρ^2.
  r is bounded below through a finite rational trial vector ψ~ (unit):
   * q0 := <ψ~,G0 ψ~> <= g (Rayleigh), residual ρ0 := ||G0ψ~ - q0 ψ~|| (block part exact, tail by L6-type row bounds),
   * g2 from λ2(G0) <= sup spec(G0 - t ψ~ψ~^T) (min-max), bounded by L3/L4/L5/L6 with A' = A0 - tψ~ψ~^T,
   * sin θ <= ρ0/(q0 - g2), δ := ||ψ - ψ~|| <= sqrt(2) sin θ,
   * <ψ~,R(v)ψ~> = Σ_j e_j(v) μ_j with μ_j := <ψ~,M_j ψ~> (finitely many nonzero) >= Σ_j min(μ_j e_j(0), μ_j e_j(v_a)),
   * r >= that - 2δρ.
  g itself is replaced by its lower bound q0 in the final inequality (the condition is monotone in g).

## Regions
I: (0, v_a], v_a = 1/4, by L8.  II: [v_a, v_b], v_b = 4, by finite geometric subdivision with L2-L6, each cell
compared against q0 <= g.  III: [v_b, ∞) by L7, 3S(4) < q0.
All arithmetic in Arb (python-flint) ball arithmetic, 200-bit precision; float numerics only to produce trial
objects (ψ~, Cholesky factors L), which are then treated as exact dyadic data.

## Corollary (dispersive, KAY Part II Conjecture 2 inequality)
K(P,T) = ∫ H(ω/2πT) P(dω) (entries linear in a_j = ∫ [[j]](ω/2πT) dP). For any x in l^2,
<x,K x> <= ∫ h(ω/2πT) dP |x|^2 < g <ω^2>/(2πT)^2 |x|^2 whenever P((0,∞)) = 1 and <ω^2> < ∞.
So λ k(P,T) >= 1 implies T < sqrt(g λ <ω^2>)/(2π) = T~c.

## Kill / scope
If any certificate fails at all refinement levels, report the failing cell and stop (no claim).
Scope: linearized isotropic Eliashberg, μ* = 0, KAY's operator. Uniqueness of the crossing (monotonicity of h
for v > sqrt 2) is NOT part of this theorem; tracked separately.
