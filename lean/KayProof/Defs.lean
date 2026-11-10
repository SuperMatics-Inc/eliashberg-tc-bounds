/-
Definitions for the finite-dimensional (N-frequency truncated) KAY operator.

Notation follows the paper: indices n, m ∈ {0, …, N-1}, w n = 2n+1, a kernel
a : ℕ → ℝ (only the values a j with j ≥ 1 enter), and

  K[a]_{nm} = ((1-δ_{nm}) a_{|n-m|} + a_{n+m+1}) / (√w_n √w_m) - δ_{nm} (2/w_n) Σ_{j=1}^{n} a_j.

The top eigenvalue is defined variationally (Rayleigh–Ritz) as the supremum of
the quadratic form over the unit sphere.
-/
import Mathlib

open Finset

namespace KayProof

/-- `w n = 2n+1`. -/
noncomputable def w (n : ℕ) : ℝ := 2 * (n : ℝ) + 1

/-- `s n = √(2n+1)`. -/
noncomputable def s (n : ℕ) : ℝ := Real.sqrt (w n)

/-- Truncated KAY matrix on `Fin N`. -/
noncomputable def K (N : ℕ) (a : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ := fun n m =>
  ((if n = m then 0 else a (Nat.dist n.val m.val)) + a (n.val + m.val + 1)) / (s n.val * s m.val)
    - (if n = m then 2 / w n.val * ∑ j ∈ Icc 1 n.val, a j else 0)

/-- Quadratic form `⟨x, K[a] x⟩`. -/
noncomputable def qf (N : ℕ) (a : ℕ → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ n, ∑ m, x n * K N a n m * x m

/-- Unit sphere of `ℝ^N` (Euclidean norm). -/
def sphere (N : ℕ) : Set (Fin N → ℝ) := {x | ∑ n, x n ^ 2 = 1}

/-- Top eigenvalue, defined as the supremum of the Rayleigh quotient. -/
noncomputable def kappa (N : ℕ) (a : ℕ → ℝ) : ℝ := sSup (qf N a '' sphere N)

/-- A kernel: positive and non-increasing on `j ≥ 1`. -/
def IsKernel (a : ℕ → ℝ) : Prop :=
  (∀ j, 1 ≤ j → 0 < a j) ∧ ∀ j, 1 ≤ j → a (j + 1) ≤ a j

/-- The cone: `x ≥ 0` and the gap variables `y n = x n / √w n` non-increasing. -/
def InCone {N : ℕ} (x : Fin N → ℝ) : Prop :=
  (∀ n, 0 ≤ x n) ∧ ∀ n m : Fin N, n ≤ m → x m / s m.val ≤ x n / s n.val

/-- Einstein kernel `a_j(v) = v²/(v²+j²)`. -/
noncomputable def einstein (v : ℝ) : ℕ → ℝ := fun j => v ^ 2 / (v ^ 2 + (j : ℝ) ^ 2)

/-- The γ = 2 kernel `j⁻²` (the strong-coupling limit). -/
noncomputable def invSq : ℕ → ℝ := fun j => 1 / (j : ℝ) ^ 2

/-! ### Conjecture 3 of KAY Part II -/

/-- Numerator `𝒢_N[a](θ)`. -/
noncomputable def G (N : ℕ) (a : ℕ → ℝ) (θ : Fin N → ℝ) : ℝ :=
  -(∑ n : Fin N, (2 * ∑ k ∈ Icc 1 n.val, a k) * θ n ^ 2)
    + ∑ n : Fin N, ∑ m : Fin N,
        θ n * ((if n = m then 0 else a (Nat.dist n.val m.val)) + a (n.val + m.val + 1)) * θ m

/-- Denominator `𝒟_N(θ) = Σ w_n θ_n²`. -/
noncomputable def D (N : ℕ) (θ : Fin N → ℝ) : ℝ := ∑ n : Fin N, w n.val * θ n ^ 2

/-- The constant `c_N[a] = N⁻² Σ_{n,m<N} a_{n+m+1}`. -/
noncomputable def cN (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  (∑ n : Fin N, ∑ m : Fin N, a (n.val + m.val + 1)) / (N : ℝ) ^ 2

end KayProof
