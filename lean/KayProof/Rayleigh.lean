import KayProof.Defs

open Finset

namespace KayProof

/-- Symmetry of the finite KAY matrix. -/
theorem K_symm (N) (a : ℕ → ℝ) (n m : Fin N) : K N a n m = K N a m n := by
  classical
  by_cases h : n = m
  · subst m; rfl
  · simp only [K, h, Ne.symm h, ite_false, sub_zero, Nat.dist_comm,
      Nat.add_comm n.val m.val, mul_comm (s n.val) (s m.val)]

/-- The quadratic form is continuous in its finite-dimensional argument. -/
theorem continuous_qf (N : ℕ) (a : ℕ → ℝ) : Continuous (qf N a) := by
  unfold qf
  fun_prop

/-- The algebraic unit sphere is compact in the finite product topology. -/
theorem isCompact_sphere (N : ℕ) : IsCompact (sphere N) := by
  have hc : IsClosed (sphere N) := by
    apply isClosed_eq _ continuous_const
    fun_prop
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin N => (-1 : ℝ)) (fun _ => 1))).of_isClosed_subset hc
  intro x hx
  have hs : ∑ n, x n ^ 2 = 1 := hx
  have hb (n : Fin N) : x n ^ 2 ≤ 1 := by
    calc
      x n ^ 2 ≤ ∑ m, x m ^ 2 := single_le_sum (fun m _ => sq_nonneg (x m)) (mem_univ n)
      _ = 1 := hs
  constructor <;> intro n <;> have := hb n <;> dsimp <;> nlinarith

/-- A coordinate unit vector witnesses nonemptiness when the truncation is nonzero. -/
theorem sphere_nonempty {N : ℕ} (hN : 0 < N) : (sphere N).Nonempty := by
  classical
  refine ⟨Pi.single (⟨0, hN⟩ : Fin N) 1, ?_⟩
  simp [sphere, Pi.single_apply]

/-- The finite Rayleigh quadratic form is bounded above on the unit sphere. -/
theorem bddAbove_qf (N) (a : ℕ → ℝ) : BddAbove (qf N a '' sphere N) :=
  (isCompact_sphere N).bddAbove_image (continuous_qf N a).continuousOn

/-- Every unit-vector Rayleigh value lies below its variational supremum. -/
theorem qf_le_kappa {N} (a : ℕ → ℝ) {x : Fin N → ℝ} (hx : x ∈ sphere N) :
    qf N a x ≤ kappa N a :=
  le_csSup (bddAbove_qf N a) ⟨x, hx, rfl⟩

/-- Rayleigh–Ritz: the maximum is attained for every nonempty truncation. -/
theorem exists_max {N} (hN : 0 < N) (a : ℕ → ℝ) :
    ∃ x ∈ sphere N, qf N a x = kappa N a := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere N).exists_isMaxOn
    (sphere_nonempty hN) (continuous_qf N a).continuousOn
  refine ⟨x, hx, le_antisymm (qf_le_kappa a hx) ?_⟩
  exact csSup_le ((sphere_nonempty hN).image (qf N a)) (by
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy)

end KayProof
