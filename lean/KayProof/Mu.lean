import KayProof.Defs

open Finset

namespace KayProof

/-- The coefficient of the j-th kernel value in the quadratic form (Lemma 6). -/
noncomputable def mu (N j : ℕ) (x : Fin N → ℝ) : ℝ :=
  2 * (∑ n : Fin N, ∑ m : Fin N,
    if m.val = n.val + j then (x m / s m.val) * (x n / s n.val - x m / s m.val) else 0) +
  ∑ n : Fin N, ∑ m : Fin N,
    if n.val + m.val + 1 = j then (x n / s n.val) * (x m / s m.val) else 0

private theorem s_pos (n : ℕ) : 0 < s n := by
  apply Real.sqrt_pos.2
  simp only [w]
  positivity

private theorem s_sq (n : ℕ) : s n ^ 2 = w n := by
  apply Real.sq_sqrt
  simp only [w]
  positivity

private theorem qf_gap (N : ℕ) (a : ℕ → ℝ) (x : Fin N → ℝ) :
    qf N a x =
      (∑ n : Fin N, ∑ m : Fin N,
        ((if n = m then 0 else a (Nat.dist n.val m.val)) + a (n.val + m.val + 1)) *
          (x n / s n.val) * (x m / s m.val)) -
      ∑ n : Fin N, 2 * (∑ j ∈ Icc 1 n.val, a j) * (x n / s n.val) ^ 2 := by
  unfold qf K
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    ring
  · apply Finset.sum_congr rfl
    intro n _
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, mem_univ, ↓reduceIte]
    have hs := s_sq n.val
    have hn : s n.val ≠ 0 := ne_of_gt (s_pos n.val)
    have hw : w n.val ≠ 0 := by nlinarith [sq_pos_of_ne_zero hn]
    field_simp
    rw [← hs]
    ring

private theorem shift_fiber_sum {N : ℕ} (m : Fin N) (j : ℕ) (c : ℝ) :
    (∑ n : Fin N, if m.val = n.val + j then c else 0) =
      if j ≤ m.val then c else 0 := by
  classical
  by_cases hj : j ≤ m.val
  · let k : Fin N := ⟨m.val - j, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩
    have hk : m.val = k.val + j := by dsimp [k]; omega
    calc
      (∑ n : Fin N, if m.val = n.val + j then c else 0) =
          (if m.val = k.val + j then c else 0) := by
        apply Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
        intro n _ hnk
        apply if_neg
        intro hn
        apply hnk
        apply Fin.ext
        omega
      _ = if j ≤ m.val then c else 0 := by rw [if_pos hk, if_pos hj]
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro n _
    apply if_neg
    intro hn
    exact hj (by omega)

private theorem sum_Icc_mul_eq_sum_shift
    (N : ℕ) (a : ℕ → ℝ) (F : Fin N → ℝ) :
    (∑ n : Fin N, ∑ j ∈ Icc 1 n.val, a j * F n) =
      ∑ j ∈ Icc 1 (2 * N),
        a j * ∑ n : Fin N, ∑ m : Fin N,
          if m.val = n.val + j then F m else 0 := by
  classical
  have hprefix (m : Fin N) :
      (∑ j ∈ Icc 1 m.val, a j * F m) =
        ∑ j ∈ Icc 1 (2 * N),
          a j * (if j ≤ m.val then F m else 0) := by
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · intro j hj
      rcases Finset.mem_Icc.mp hj with ⟨hj1, hjm⟩
      apply Finset.mem_Icc.mpr
      have hm := m.isLt
      omega
    · intro j hj
      rcases Finset.mem_sdiff.mp hj with ⟨hjBig, hjSmall⟩
      have hjm : ¬j ≤ m.val := by
        intro hle
        apply hjSmall
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hjBig).1, hle⟩
      rw [if_neg hjm, mul_zero]
    · intro j hj
      rw [if_pos (Finset.mem_Icc.mp hj).2]
  symm
  calc
    (∑ j ∈ Icc 1 (2 * N),
        a j * ∑ n : Fin N, ∑ m : Fin N,
          if m.val = n.val + j then F m else 0) =
        ∑ j ∈ Icc 1 (2 * N), ∑ m : Fin N,
          a j * (if j ≤ m.val then F m else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      simp_rw [shift_fiber_sum]
      rw [Finset.mul_sum]
    _ = ∑ m : Fin N, ∑ j ∈ Icc 1 (2 * N),
          a j * (if j ≤ m.val then F m else 0) := Finset.sum_comm
    _ = ∑ m : Fin N, ∑ j ∈ Icc 1 m.val, a j * F m := by
      apply Finset.sum_congr rfl
      intro m _
      exact (hprefix m).symm

private theorem sum_shift_entry {N : ℕ} (a : ℕ → ℝ) (n m : Fin N) (r : ℝ) :
    (∑ j ∈ Icc 1 (2 * N), a j * (if m.val = n.val + j then r else 0)) =
      if n < m then a (Nat.dist n.val m.val) * r else 0 := by
  classical
  by_cases h : n < m
  · have hnm : n.val < m.val := h
    have hd : m.val - n.val ∈ Icc 1 (2 * N) := by
      simp only [mem_Icc]
      have hm := m.isLt
      omega
    have heq (j : ℕ) : (m.val = n.val + j) ↔ j = m.val - n.val := by omega
    simp_rw [heq, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', hd, ↓reduceIte, if_pos h, Nat.dist_eq_sub_of_le hnm.le]
  · have hnm : m.val ≤ n.val := by
      have : ¬n.val < m.val := h
      omega
    simp only [if_neg h]
    apply Finset.sum_eq_zero
    intro j hj
    have hj1 := (mem_Icc.mp hj).1
    have hjne : m.val ≠ n.val + j := by omega
    simp [hjne]

private theorem sum_hankel_entry {N : ℕ} (a : ℕ → ℝ) (n m : Fin N) (r : ℝ) :
    (∑ j ∈ Icc 1 (2 * N), a j * (if n.val + m.val + 1 = j then r else 0)) =
      a (n.val + m.val + 1) * r := by
  classical
  have hmem : n.val + m.val + 1 ∈ Icc 1 (2 * N) := by
    simp only [mem_Icc]
    have hn := n.isLt
    have hm := m.isLt
    omega
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hmem, ↓reduceIte]

private theorem sum_offdiag (N : ℕ) (a : ℕ → ℝ) (y : Fin N → ℝ) :
    (∑ n : Fin N, ∑ m : Fin N,
      (if n = m then 0 else a (Nat.dist n.val m.val)) * y n * y m) =
    2 * (∑ n : Fin N, ∑ m : Fin N,
      if n < m then a (Nat.dist n.val m.val) * (y m * y n) else 0) := by
  classical
  let f : Fin N → Fin N → ℝ := fun n m =>
    if n < m then a (Nat.dist n.val m.val) * (y m * y n) else 0
  have hswap : (∑ n, ∑ m, f m n) = ∑ n, ∑ m, f n m := Finset.sum_comm
  have hpoint (n m : Fin N) :
      (if n = m then 0 else a (Nat.dist n.val m.val)) * y n * y m =
        f n m + f m n := by
    rcases lt_trichotomy n m with h | h | h
    · have hne : n ≠ m := ne_of_lt h
      have hn : ¬m < n := not_lt_of_ge h.le
      simp [f, h, hne, hn]
      ring
    · subst m
      simp [f]
    · have hne : n ≠ m := ne_of_gt h
      have hn : ¬n < m := not_lt_of_ge h.le
      simp [f, h, hne, hn, Nat.dist_comm]
      ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [hswap]
  ring

private theorem weighted_shift (N : ℕ) (a : ℕ → ℝ) (F : Fin N → Fin N → ℝ) :
    (∑ j ∈ Icc 1 (2 * N), a j * (∑ n : Fin N, ∑ m : Fin N,
      if m.val = n.val + j then F n m else 0)) =
      ∑ n : Fin N, ∑ m : Fin N,
        if n < m then a (Nat.dist n.val m.val) * F n m else 0 := by
  classical
  calc
    _ = ∑ j ∈ Icc 1 (2 * N), ∑ n : Fin N, ∑ m : Fin N,
          a j * (if m.val = n.val + j then F n m else 0) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ n : Fin N, ∑ m : Fin N, ∑ j ∈ Icc 1 (2 * N),
          a j * (if m.val = n.val + j then F n m else 0) := Finset.sum_comm_cycle.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      exact sum_shift_entry a n m (F n m)

private theorem weighted_hankel (N : ℕ) (a : ℕ → ℝ) (F : Fin N → Fin N → ℝ) :
    (∑ j ∈ Icc 1 (2 * N), a j * (∑ n : Fin N, ∑ m : Fin N,
      if n.val + m.val + 1 = j then F n m else 0)) =
      ∑ n : Fin N, ∑ m : Fin N, a (n.val + m.val + 1) * F n m := by
  classical
  calc
    _ = ∑ j ∈ Icc 1 (2 * N), ∑ n : Fin N, ∑ m : Fin N,
          a j * (if n.val + m.val + 1 = j then F n m else 0) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ n : Fin N, ∑ m : Fin N, ∑ j ∈ Icc 1 (2 * N),
          a j * (if n.val + m.val + 1 = j then F n m else 0) := Finset.sum_comm_cycle.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      exact sum_hankel_entry a n m (F n m)

private theorem qf_eq_sum (N : ℕ) (a : ℕ → ℝ) (x : Fin N → ℝ) :
    qf N a x = ∑ j ∈ Icc 1 (2 * N), a j * mu N j x := by
  classical
  let y : Fin N → ℝ := fun n => x n / s n.val
  have hsub (j : ℕ) (n m : Fin N) :
      (if m.val = n.val + j then y m * (y n - y m) else 0) =
        (if m.val = n.val + j then y m * y n else 0) -
        (if m.val = n.val + j then y m * y m else 0) := by
    split_ifs <;> ring
  have hpoint (j : ℕ) :
      a j * mu N j x =
        2 * (a j * (∑ n : Fin N, ∑ m : Fin N,
          if m.val = n.val + j then y m * y n else 0)) +
        a j * (∑ n : Fin N, ∑ m : Fin N,
          if n.val + m.val + 1 = j then y n * y m else 0) -
        2 * (a j * (∑ n : Fin N, ∑ m : Fin N,
          if m.val = n.val + j then y m * y m else 0)) := by
    change a j * (2 * (∑ n : Fin N, ∑ m : Fin N,
      if m.val = n.val + j then y m * (y n - y m) else 0) +
      (∑ n : Fin N, ∑ m : Fin N,
        if n.val + m.val + 1 = j then y n * y m else 0)) = _
    simp_rw [hsub, Finset.sum_sub_distrib]
    ring
  have hmu :
      (∑ j ∈ Icc 1 (2 * N), a j * mu N j x) =
        2 * (∑ j ∈ Icc 1 (2 * N), a j * (∑ n : Fin N, ∑ m : Fin N,
          if m.val = n.val + j then y m * y n else 0)) +
        (∑ j ∈ Icc 1 (2 * N), a j * (∑ n : Fin N, ∑ m : Fin N,
          if n.val + m.val + 1 = j then y n * y m else 0)) -
        2 * (∑ j ∈ Icc 1 (2 * N), a j * (∑ n : Fin N, ∑ m : Fin N,
          if m.val = n.val + j then y m * y m else 0)) := by
    simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdiag :
      (∑ j ∈ Icc 1 (2 * N), a j * (∑ n : Fin N, ∑ m : Fin N,
        if m.val = n.val + j then y m * y m else 0)) =
      ∑ n : Fin N, (∑ j ∈ Icc 1 n.val, a j) * (y n * y n) := by
    rw [← sum_Icc_mul_eq_sum_shift N a (fun n => y n * y n)]
    simp_rw [Finset.sum_mul]
  rw [weighted_shift N a (fun n m => y m * y n),
      weighted_hankel N a (fun n m => y n * y m), hdiag] at hmu
  have hq := qf_gap N a x
  change qf N a x =
      (∑ n : Fin N, ∑ m : Fin N,
        ((if n = m then 0 else a (Nat.dist n.val m.val)) + a (n.val + m.val + 1)) *
          y n * y m) -
      ∑ n : Fin N, 2 * (∑ j ∈ Icc 1 n.val, a j) * (y n) ^ 2 at hq
  simp_rw [add_mul, Finset.sum_add_distrib] at hq
  rw [sum_offdiag] at hq
  simp_rw [mul_assoc, pow_two, ← Finset.mul_sum] at hq
  linarith

/-- Lemma 6: the kernel difference expands in the cone coefficients. -/
theorem qf_sub (N : ℕ) (a b : ℕ → ℝ) (x : Fin N → ℝ) :
    qf N b x - qf N a x = ∑ j ∈ Icc 1 (2 * N), (b j - a j) * mu N j x := by
  rw [qf_eq_sum N b x, qf_eq_sum N a x, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem gap_nonneg {N : ℕ} {x : Fin N → ℝ} (hx : InCone x) (n : Fin N) :
    0 ≤ x n / s n.val := div_nonneg (hx.1 n) (le_of_lt (s_pos n.val))

private theorem toe_nonneg {N j : ℕ} {x : Fin N → ℝ} (hx : InCone x) :
    0 ≤ ∑ n : Fin N, ∑ m : Fin N,
      if m.val = n.val + j then (x m / s m.val) * (x n / s n.val - x m / s m.val) else 0 := by
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro m hm
  split_ifs with h
  · apply mul_nonneg (gap_nonneg hx m)
    apply sub_nonneg.mpr
    apply hx.2 n m
    exact Fin.le_def.mpr (by omega)
  · exact le_rfl

private theorem hankel_nonneg {N j : ℕ} {x : Fin N → ℝ} (hx : InCone x) :
    0 ≤ ∑ n : Fin N, ∑ m : Fin N,
      if n.val + m.val + 1 = j then (x n / s n.val) * (x m / s m.val) else 0 := by
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro m hm
  split_ifs
  · exact mul_nonneg (gap_nonneg hx n) (gap_nonneg hx m)
  · exact le_rfl

/-- The coefficient is nonnegative on the monotone cone (Lemma 6). -/
theorem mu_nonneg {N j : ℕ} {x : Fin N → ℝ} (hx : InCone x) (_hj : 1 ≤ j) :
    0 ≤ mu N j x := by
  unfold mu
  exact add_nonneg (mul_nonneg (by norm_num) (toe_nonneg hx)) (hankel_nonneg hx)

/-- The first coefficient dominates the square of the first coordinate (Lemma 6). -/
theorem mu_one_ge {N : ℕ} (hN : 0 < N) {x : Fin N → ℝ} (hx : InCone x) :
    x ⟨0, hN⟩ ^ 2 ≤ mu N 1 x := by
  let z : Fin N := ⟨0, hN⟩
  have hz : s z.val = 1 := by simp [z, s, w]
  have hinner : x z ^ 2 ≤ ∑ m : Fin N,
      if z.val + m.val + 1 = 1 then (x z / s z.val) * (x m / s m.val) else 0 := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
      (f := fun m => if z.val + m.val + 1 = 1 then (x z / s z.val) * (x m / s m.val) else 0)
      (fun m _ => by
        split_ifs
        · exact mul_nonneg (gap_nonneg hx z) (gap_nonneg hx m)
        · exact le_rfl) (Finset.mem_univ z)
    simpa [hz, z, pow_two] using h
  have houter : (∑ m : Fin N,
      if z.val + m.val + 1 = 1 then (x z / s z.val) * (x m / s m.val) else 0) ≤
      ∑ n : Fin N, ∑ m : Fin N,
        if n.val + m.val + 1 = 1 then (x n / s n.val) * (x m / s m.val) else 0 := by
    apply Finset.single_le_sum (f := fun n : Fin N => ∑ m : Fin N,
      if n.val + m.val + 1 = 1 then (x n / s n.val) * (x m / s m.val) else 0) _ (Finset.mem_univ z)
    intro n hn
    apply Finset.sum_nonneg
    intro m hm
    split_ifs
    · exact mul_nonneg (gap_nonneg hx n) (gap_nonneg hx m)
    · exact le_rfl
  unfold mu
  have ht := toe_nonneg (j := 1) hx
  dsimp [z] at hinner houter
  linarith

end KayProof
