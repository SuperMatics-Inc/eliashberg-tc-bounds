# Derivation of the exact-rational certificate

We derive the checks in `verify_rational.py` from the fixed proof plan and elementary operator estimates. The derivation and implementation were developed without using `certify_arb.py`, its results or its trial objects. Floating-point linear algebra proposes exact dyadic trial objects; the verifier decides every inequality over the rationals.

## Scope

The certificate proves `sup spec G(v) < g` for every `v > 0` and the stated consequence for the linearized dispersive operator. Existence or uniqueness of a thermodynamic transition and monotonicity of the crossing lie outside its scope.

The operator normalization was checked against the arXiv texts of Kiessling, Altshuler and Yuzbashyan: Part III equations (40)–(42) give precisely `H(v)=v^2 G(v)`; Part I equations (42)–(44) give precisely `G0=G(gamma=2)`. Part I identifies `g(gamma)` as the largest eigenvalue; the proof here uses that variational definition and does not need the separate spectral-radius proposition. Part II gives the dispersive operator as the averages of the same three components (its equations (39)–(42)). Thus no factor of two or Matsubara weight is changed by the congruence.

## Objects, convergence, and simplicity

For `j >= 1`, the weighted shift in `T_j` has norm at most `1/sqrt(2j+1)`, so `||T_j|| <= 2/sqrt(2j+1)`. The anti-diagonal matrix `H_j` is a weighted reversal on its first `j` coordinates, whose largest entry is `1/sqrt(2j-1)`. The diagonal `D_j` has norm `2/(2j+1)`. Each is compact, including the diagonal and shifts because their entries tend to zero along their infinite support. The stated `m_j` therefore bounds `||M_j||`. Its decrease in `j`, together with `m_1 < 3`, gives the convenient independent relaxation `m_j < 3`.

The series for `G(v)`, `P(v)`, `D(v)`, and `R(v)` converge absolutely in operator norm using respectively `3 sum j^-2` and `3 sum j^-4`; their sums are compact and self-adjoint. A positive trial Rayleigh quotient ensures that `g > 0` is an attained eigenvalue. Since every off-diagonal entry of `G0` is strictly positive, replacing a maximizing real vector by its absolute value cannot decrease its Rayleigh quotient. A nonnegative maximizing eigenvector is strictly positive by its eigenvalue equation. Equality in the absolute-value comparison forces every nonzero entry of any maximizing real eigenvector to have the same sign. Consequently the top eigenspace is one-dimensional: an orthogonal second top eigenvector is impossible. Complex vectors reduce to the real case, or directly to the modulus inequality.

## L1 and L2: modulus and envelope

For finitely supported vectors, apply `Re(conj(x_n) x_m) <= |x_n| |x_m|` term by term to the nonnegative entries of `P`, leaving the real diagonal term unchanged. Operator-norm continuity extends this to all of `l2`. The derivative of `1/(v^2+j^2)` with respect to `v^2` is negative. Thus the positive part is bounded from above using the lower endpoint, and the subtracted diagonal using the upper endpoint. Entrywise domination is used only after taking absolute values, not as an unsupported Loewner comparison.

## L3: blocks

For `x = (u,z)`, bound the quadratic form by `alpha ||u||^2 + 2 beta ||u|| ||z|| + gamma ||z||^2`. The maximum on `||u||^2+||z||^2=1` is the upper eigenvalue of the indicated two-by-two real symmetric matrix. The verifier avoids its square root: with target `Q`, it checks `Q > alpha`, `Q > gamma`, and `(Q-alpha)(Q-gamma) > beta^2`. The positive gap is at least determinant divided by trace of the corresponding positive two-by-two matrix. This last bound is exact because its larger eigenvalue is at most its trace.

## L4: rational congruence replacement

Put `W = diag(2n+1)` and `Atilde = W^(1/2) A W^(1/2)`. For rational squared endpoints all entries of `Atilde` are rational. The verifier proposes a dyadic lower-triangular `L` and rational `tau > 0`, and computes exactly

`E = (s-tau)W - Atilde - L L^T`.

The weighted Schur test with positive weights `sqrt(w_n)` gives

`||W^(-1/2) E W^(-1/2)|| <= max_n sum_m |E_nm| / w_n = epsilon`.

Hence `epsilon < tau` implies `sI-A >= (tau-epsilon)I > 0`. This is an independent exact-rational residual certificate, not the primary implementation's Arb/Frobenius certificate. The square roots in the proof cancel in the computation. No positivity of a floating-point factorization is trusted.

## L5: tail

For the nonnegative symmetric positive part, use Schur weights `p_n = 1/sqrt(w_n)`. Its weighted row sum is exactly `sum_m [(1-delta_nm)c_|n-m| + c_(n+m+1)]/w_m`. On indices `m >= N`, replace `1/w_m` by `1/w_N`. The two sides of the Toeplitz row each sum to at most `S`, and the Hankel row to at most `S`, giving `3S/w_N`. Dropping the subtracted nonnegative diagonal bounds the spectral supremum, not the norm of the signed block. The Schur weights need not belong to `l2`: apply the estimate first to finite supports.

The rational verifier uses an integral estimate in place of the coth formula:

`S(v) <= sum_(j=1)^K 1/(v^2+j^2) + 1/K`,

because `sum_(j>K) j^-2 <= integral_K^infinity t^-2 dt`. This is valid also at `v=0` and requires no enclosure of pi or coth.

## L6: off-block

For `n < N <= m`, the diagonal subtraction vanishes. Use `(a+b)^2 <= 2a^2+2b^2`, `w_m >= w_N`, and `c_j(v)^2 <= j^-4`. The Toeplitz indices start at `N-n`, the Hankel indices at `N+n+1`. The decreasing-function integral bound is `sum_(j>=k) j^-4 <= k^-4 + integral_k^infinity t^-4 dt = k^-4+1/(3k^3)`. Summing over the head indices proves exactly the stated Frobenius bound, hence also the operator bound. The same bound controls the squared norm of the uncomputed tail of a unit finite-support trial vector.

## L7: large parameter

The same Schur argument with all indices and `w_m >= 1` gives `sup spec G(v) <= ||P(v)|| <= 3S(v)`. Each summand in `S` decreases with `v^2`. The exact finite-sum/integral estimate at the chosen `v_b` therefore controls the whole unbounded region, including its endpoint.

## L8: perturbation and eigenvector transfer

The scalar identity `j^-2 - 1/(v^2+j^2) = v^2/[j^2(v^2+j^2)]` is exact, and the absolutely norm-convergent series permits subtraction. Independently, the verifier uses

`rho = 3 (1 + 1/16 + integral_2^infinity t^-4 dt) = 53/16`

as an upper bound for `||R(v)||` for all `v`, using `m_j < 3`. For a finite normalized trial vector `u`, its Rayleigh quotient is rational after congruence, despite the square roots in `u`. Its residual is computed exactly on the head and bounded by L6 on the tail.

For any `t > 0`, the min-max principle yields `lambda_2(G0) <= sup spec(G0-t uu^T)`: choose the codimension-one subspace `u^perp`, on which the rank-one term vanishes. Once that supremum is below a certified bound `g2 < q`, spectral expansion of the residual gives `sin(theta) <= residual/(q-g2)`. Choosing the positive overlap gives `||psi-u|| <= sqrt(2) sin(theta)`. The verifier uses only an exact rational upper enclosure of this last square root.

The coefficients `mu_j = <u,M_j u>` vanish for `j >= 2N`. Each remaining scalar `e_j(v)` lies between its values at `v_a` and zero; choose its lower endpoint when `mu_j >= 0` and its upper endpoint otherwise. The transfer error is at most `2 rho ||psi-u||` by the triangle inequality and the unit norms. This proves the lower bound `r` without assuming that `R(v)` is positive.

Finally the orthogonal decomposition gives the plan's two-by-two lower matrix. The verifier replaces `g` by a rational `Q <= q <= g`, checks `r > 0`, `Q-g2-v_a^2 rho > 0`, and the strict determinant condition. It also reports a rational coefficient `kappa > 0` with `g-sup spec G(v) >= kappa v^2` throughout the small region. An unscaled uniform positive gap cannot hold on a region accumulating at zero; its infimum is zero.

## Dispersive consequence

With positive frequencies almost surely and finite second moment, `h(v) < g v^2` integrates strictly: the nonnegative difference is positive almost surely and integrable. For every unit vector, the quadratic form of the integral operator is at most `integral h(v) dP < g integral v^2 dP`. The bound is independent of the vector, so taking the supremum preserves strictness. The temperature inequality follows under the stated linearized spectral instability condition.
