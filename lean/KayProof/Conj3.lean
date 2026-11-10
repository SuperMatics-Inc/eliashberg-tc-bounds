import KayProof.Defs

open Finset

namespace KayProof

private theorem kernel_strictAnti {a : ℕ → ℝ}
    (hdec : ∀ j, 1 ≤ j → a (j + 1) < a j) :
    StrictAnti (fun j : ℕ => a (j + 1)) := by
  apply strictAnti_nat_of_succ_lt
  intro j
  simpa [Nat.add_assoc] using hdec (j + 1) (by omega)

/-- The Hankel grid average strictly decreases as the square grows. -/
private theorem grid_average_step {a : ℕ → ℝ}
    (hdec : ∀ j, 1 ≤ j → a (j + 1) < a j) {l : ℕ} (hl : 0 < l) :
    (∑ i ∈ range (l + 1), ∑ j ∈ range (l + 1), a (i + j + 1)) /
        ((l + 1 : ℕ) : ℝ) ^ 2 <
      (∑ i ∈ range l, ∑ j ∈ range l, a (i + j + 1)) / (l : ℝ) ^ 2 := by
  let S : ℝ := ∑ i ∈ range l, ∑ j ∈ range l, a (i + j + 1)
  let R : ℝ := ∑ j ∈ range l, a (l + j + 1)
  let C : ℝ := a (l + l + 1)
  have ha := kernel_strictAnti hdec
  have hS : (l : ℝ) * R < S := by
    have h : ∑ _i ∈ range l, R < ∑ i ∈ range l, ∑ j ∈ range l, a (i + j + 1) := by
      apply Finset.sum_lt_sum
      · intro i hi
        apply le_of_lt
        dsimp [R]
        apply Finset.sum_lt_sum
        · intro j hj
          apply le_of_lt
          exact ha (by simp only [mem_range] at hi; omega : i + j < l + j)
        · exact ⟨0, mem_range.mpr hl, ha (by simp only [mem_range] at hi; omega : i + 0 < l + 0)⟩
      · refine ⟨0, mem_range.mpr hl, ?_⟩
        dsimp [R]
        apply Finset.sum_lt_sum
        · intro j hj
          exact le_of_lt (ha (by omega : 0 + j < l + j))
        · exact ⟨0, mem_range.mpr hl, ha (by omega : 0 + 0 < l + 0)⟩
    simpa [S] using h
  have hR : (l : ℝ) * C < R := by
    have h : ∑ _j ∈ range l, C < ∑ j ∈ range l, a (l + j + 1) := by
      apply Finset.sum_lt_sum
      · intro j hj
        exact le_of_lt (ha (by simp only [mem_range] at hj; omega : l + j < l + l))
      · exact ⟨0, mem_range.mpr hl, ha (by omega : l + 0 < l + l)⟩
    simpa [C, R] using h
  have hsum : (∑ i ∈ range (l + 1), ∑ j ∈ range (l + 1), a (i + j + 1)) = S + 2 * R + C := by
    simp only [Finset.sum_range_succ]
    dsimp [S, R, C]
    rw [Finset.sum_add_distrib]
    have heq : (∑ i ∈ range l, a (i + l + 1)) = ∑ j ∈ range l, a (l + j + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    rw [heq]
    ring
  rw [hsum]
  change (S + 2 * R + C) / ((l + 1 : ℕ) : ℝ) ^ 2 < S / (l : ℝ) ^ 2
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hl1 : (0 : ℝ) < ((l + 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < l + 1 by omega)
  apply (div_lt_div_iff₀ (sq_pos_of_pos hl1) (sq_pos_of_pos hlr)).2
  push_cast
  nlinarith [mul_pos hlr (sub_pos.mpr hS), mul_pos hlr (sub_pos.mpr hR)]

/-- The normalized Hankel sums are strictly decreasing at positive sizes. -/
private theorem cN_strictAnti {a : ℕ → ℝ}
    (hdec : ∀ j, 1 ≤ j → a (j + 1) < a j) :
    StrictAnti (fun n : ℕ => cN (n + 1) a) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have h := grid_average_step hdec (show 0 < n + 1 by omega)
  simp_rw [← Fin.sum_univ_eq_sum_range] at h
  simpa [cN, Nat.add_assoc] using h

private def preVec {N : ℕ} (l : ℕ) (n : Fin N) : ℝ :=
  if n.val < l then 1 else 0

private theorem sum_w_range (l : ℕ) : (∑ n ∈ range l, w n) = (l : ℝ) ^ 2 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [sum_range_succ, ih]
    simp only [w, Nat.cast_add, Nat.cast_one]
    ring

/-- The denominator of a prefix vector is the square of its length. -/
private theorem prefix_D {N l : ℕ} (hl : l ≤ N) :
    D N (preVec l) = (l : ℝ) ^ 2 := by
  rw [D, ← sum_w_range l]
  have h : (∑ n : Fin N, w n.val * preVec l n ^ 2) =
      ∑ n : Fin N, if n.val < l then w n.val else 0 := by
    apply sum_congr rfl
    intro n hn
    by_cases h : n.val < l <;> simp [preVec, h]
  rw [h]
  rw [show (∑ n : Fin N, if n.val < l then w n.val else 0) =
      ∑ n ∈ range N, if n < l then w n else 0 by
        exact Fin.sum_univ_eq_sum_range (fun n : ℕ => if n < l then w n else 0) N]
  rw [← sum_filter]
  have hfilter : (range N).filter (fun n => n < l) = range l := by
    ext n
    simp only [mem_filter, mem_range]
    omega
  rw [hfilter]

private def padded {N : ℕ} (θ : Fin N → ℝ) (i : ℕ) : ℝ :=
  if h : i < N then θ ⟨i, h⟩ else 0

private def gap {N : ℕ} (θ : Fin N → ℝ) (i : ℕ) : ℝ :=
  padded θ i - padded θ (i + 1)

private theorem gap_nonneg {N : ℕ} {θ : Fin N → ℝ}
    (h0 : ∀ n, 0 ≤ θ n) (hmono : Antitone θ) (i : ℕ) :
    0 ≤ gap θ i := by
  unfold gap padded
  split_ifs with hi hj
  · exact sub_nonneg.mpr (hmono (show (⟨i, hi⟩ : Fin N) ≤ ⟨i + 1, hj⟩ by simp))
  · exact sub_nonneg.mpr (by simpa using h0 ⟨i, hi⟩)
  · omega
  · simp

/-- Every antitone nonnegative vector is a nonnegative sum of prefixes. -/
private theorem prefix_decomposition {N : ℕ} (θ : Fin N → ℝ) (n : Fin N) :
    θ n = ∑ i ∈ range N, gap θ i * preVec (i + 1) n := by
  have hp : padded θ N = 0 := by simp [padded]
  have ht : (∑ i ∈ Ico n.val N, gap θ i) = padded θ n.val := by
    have h := Finset.sum_Ico_sub (padded θ) (show n.val ≤ N by omega)
    have hn : (∑ i ∈ Ico n.val N, gap θ i) =
        -(∑ i ∈ Ico n.val N, (padded θ (i + 1) - padded θ i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [gap]
      ring
    rw [hn, h, hp]
    ring
  calc
    θ n = padded θ n.val := by simp [padded, n.isLt]
    _ = ∑ i ∈ Ico n.val N, gap θ i := ht.symm
    _ = ∑ i ∈ range N, gap θ i * preVec (i + 1) n := by
      rw [show Ico n.val N = (range N).filter (fun i => n.val ≤ i) by
        ext i; simp; omega]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : n.val ≤ i
      · simp [preVec, h, show n.val < i + 1 by omega]
      · simp [preVec, h, show ¬ n.val < i + 1 by omega]

private theorem range_dist_sum (a : ℕ → ℝ) (n : ℕ) :
    (∑ m ∈ range n, a (n - m)) = ∑ k ∈ Icc 1 n, a k := by
  apply Finset.sum_bij (fun m _ => n - m)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm m' hm' heq
    simp only [mem_range] at hm hm'
    omega
  · intro k hk
    simp only [mem_Icc] at hk
    refine ⟨n - k, mem_range.mpr (by omega), ?_⟩
    omega
  · intro m hm
    rfl

/-- On a prefix, the Toeplitz contribution exactly cancels the subtraction. -/
private theorem toeplitz_prefix (a : ℕ → ℝ) (l : ℕ) :
    (∑ n ∈ range l, ∑ m ∈ range l,
      if n = m then 0 else a (Nat.dist n m)) =
      2 * ∑ n ∈ range l, ∑ k ∈ Icc 1 n, a k := by
  let lower : ℝ := ∑ n ∈ range l, ∑ m ∈ range l,
    if m < n then a (Nat.dist n m) else 0
  have hswap : (∑ n ∈ range l, ∑ m ∈ range l,
      if n < m then a (Nat.dist n m) else 0) = lower := by
    dsimp [lower]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [Nat.dist_comm]
  have hsplit : (∑ n ∈ range l, ∑ m ∈ range l,
      if n = m then 0 else a (Nat.dist n m)) =
      lower + (∑ n ∈ range l, ∑ m ∈ range l,
        if n < m then a (Nat.dist n m) else 0) := by
    dsimp [lower]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    rcases lt_trichotomy n m with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge (le_of_lt h)]
    · subst m; simp
    · simp [h, Ne.symm (ne_of_lt h), not_lt_of_ge (le_of_lt h)]
  have hlower : lower = ∑ n ∈ range l, ∑ k ∈ Icc 1 n, a k := by
    dsimp [lower]
    apply sum_congr rfl
    intro n hn
    rw [← sum_filter]
    have hf : (range l).filter (fun m => m < n) = range n := by
      ext m
      simp only [mem_filter, mem_range] at *
      omega
    rw [hf]
    calc
      (∑ m ∈ range n, a (Nat.dist n m)) =
          ∑ m ∈ range n, a (n - m) := by
        apply sum_congr rfl
        intro m hm
        rw [Nat.dist_comm n m, Nat.dist_eq_sub_of_le (show m ≤ n by simp only [mem_range] at hm; omega)]
      _ = ∑ k ∈ Icc 1 n, a k := range_dist_sum a n
  rw [hsplit, hswap, hlower]
  ring

private theorem sum_fin_trunc {N l : ℕ} (hl : l ≤ N) (f : ℕ → ℝ) :
    (∑ n : Fin N, if n.val < l then f n.val else 0) = ∑ n ∈ range l, f n := by
  rw [show (∑ n : Fin N, if n.val < l then f n.val else 0) =
      ∑ n ∈ range N, if n < l then f n else 0 by
        exact Fin.sum_univ_eq_sum_range (fun n : ℕ => if n < l then f n else 0) N]
  rw [← sum_filter]
  have hf : (range N).filter (fun n => n < l) = range l := by
    ext n; simp only [mem_filter, mem_range]; omega
  rw [hf]

/-- The numerator of a prefix vector is its Hankel grid sum. -/
private theorem prefix_G {N l : ℕ} (hl : l ≤ N) (a : ℕ → ℝ) :
    G N a (preVec l) = ∑ n ∈ range l, ∑ m ∈ range l, a (n + m + 1) := by
  have hdiag : (∑ n : Fin N, (2 * ∑ k ∈ Icc 1 n.val, a k) * preVec l n ^ 2) =
      2 * ∑ n ∈ range l, ∑ k ∈ Icc 1 n, a k := by
    rw [Finset.mul_sum]
    rw [← sum_fin_trunc hl]
    apply sum_congr rfl
    intro n hn
    by_cases h : n.val < l <;> simp [preVec, h]
  have hdouble : (∑ n : Fin N, ∑ m : Fin N,
      preVec l n * ((if n = m then 0 else a (Nat.dist n.val m.val)) +
        a (n.val + m.val + 1)) * preVec l m) =
      ∑ n ∈ range l, ∑ m ∈ range l,
        ((if n = m then 0 else a (Nat.dist n m)) + a (n + m + 1)) := by
    rw [← sum_fin_trunc hl]
    apply sum_congr rfl
    intro n hn
    by_cases h : n.val < l
    · simp only [preVec, h]
      rw [← sum_fin_trunc hl]
      apply sum_congr rfl
      intro m hm
      by_cases hm' : m.val < l
      · simp [hm', Fin.ext_iff]
      · simp [hm']
    · simp [preVec, h]
  unfold G
  rw [hdiag, hdouble]
  simp only [sum_add_distrib]
  rw [toeplitz_prefix]
  ring

private noncomputable def B (N : ℕ) (a : ℕ → ℝ) (x y : Fin N → ℝ) : ℝ :=
  -(∑ n : Fin N, (2 * ∑ k ∈ Icc 1 n.val, a k) * x n * y n) +
    (∑ n : Fin N, ∑ m : Fin N,
      x n * ((if n = m then 0 else a (Nat.dist n.val m.val)) +
        a (n.val + m.val + 1)) * y m) -
    cN N a * ∑ n : Fin N, w n.val * x n * y n

private theorem B_self (N : ℕ) (a : ℕ → ℝ) (x : Fin N → ℝ) :
    B N a x x = G N a x - cN N a * D N x := by
  simp only [B, G, D, pow_two]
  congr 1
  · congr 1
    congr 1
    apply sum_congr rfl
    intro n hn
    ring
  · congr 1
    apply sum_congr rfl
    intro n hn
    ring

private theorem B_symm (N : ℕ) (a : ℕ → ℝ) (x y : Fin N → ℝ) :
    B N a x y = B N a y x := by
  unfold B
  have hd : (∑ n : Fin N, (2 * ∑ k ∈ Icc 1 n.val, a k) * x n * y n) =
      ∑ n : Fin N, (2 * ∑ k ∈ Icc 1 n.val, a k) * y n * x n := by
    apply sum_congr rfl
    intro n hn
    ring
  have hw : (∑ n : Fin N, w n.val * x n * y n) =
      ∑ n : Fin N, w n.val * y n * x n := by
    apply sum_congr rfl
    intro n hn
    ring
  rw [hd, hw]
  congr 1
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro m hm
  rw [Nat.dist_comm, show n.val + m.val + 1 = m.val + n.val + 1 by omega]
  by_cases h : n = m <;> simp [h, eq_comm] <;> ring

private theorem prefix_diag {N l t : ℕ} (hlt : l ≤ t) (hlN : l ≤ N)
    (f : ℕ → ℝ) :
    (∑ n : Fin N, f n.val * preVec l n * preVec t n) =
      ∑ n ∈ range l, f n := by
  rw [← sum_fin_trunc hlN]
  apply sum_congr rfl
  intro n hn
  by_cases h : n.val < l
  · have ht : n.val < t := by omega
    simp [preVec, h, ht]
  · simp [preVec, h]

private theorem prefix_double {N l t : ℕ} (hlN : l ≤ N) (htN : t ≤ N)
    (a : ℕ → ℝ) :
    (∑ n : Fin N, ∑ m : Fin N,
      preVec l n * ((if n = m then 0 else a (Nat.dist n.val m.val)) +
        a (n.val + m.val + 1)) * preVec t m) =
      ∑ n ∈ range l, ∑ m ∈ range t,
        ((if n = m then 0 else a (Nat.dist n m)) + a (n + m + 1)) := by
  rw [← sum_fin_trunc hlN]
  apply sum_congr rfl
  intro n hn
  by_cases h : n.val < l
  · simp only [preVec, h]
    rw [← sum_fin_trunc htN]
    apply sum_congr rfl
    intro m hm
    by_cases hm' : m.val < t
    · simp [hm', Fin.ext_iff]
    · simp [hm']
  · simp [preVec, h]

private theorem B_prefix_le {N l t : ℕ} (hlt : l ≤ t) (htN : t ≤ N)
    {a : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j) :
    B N a (preVec l) (preVec l) ≤ B N a (preVec l) (preVec t) := by
  have hlN : l ≤ N := le_trans hlt htN
  unfold B
  rw [prefix_diag le_rfl hlN (fun n => 2 * ∑ k ∈ Icc 1 n, a k),
      prefix_diag hlt hlN (fun n => 2 * ∑ k ∈ Icc 1 n, a k),
      prefix_diag le_rfl hlN w, prefix_diag hlt hlN w,
      prefix_double hlN hlN, prefix_double hlN htN]
  have hh : (∑ n ∈ range l, ∑ m ∈ range l,
        ((if n = m then 0 else a (Nat.dist n m)) + a (n + m + 1))) ≤
      ∑ n ∈ range l, ∑ m ∈ range t,
        ((if n = m then 0 else a (Nat.dist n m)) + a (n + m + 1)) := by
    apply sum_le_sum
    intro n hn
    apply sum_le_sum_of_subset_of_nonneg (range_mono hlt)
    intro m hm hnot
    have hhank : 0 ≤ a (n + m + 1) := le_of_lt (hpos _ (by omega))
    have he : n ≠ m := by
      simp only [mem_range] at hn hnot
      omega
    have hdist : 1 ≤ Nat.dist n m := by
      have : Nat.dist n m ≠ 0 := fun h => he (Nat.eq_of_dist_eq_zero h)
      omega
    simp only [ite_eq_right he]
    exact add_nonneg (le_of_lt (hpos _ hdist)) hhank
  linarith

private theorem B_prefix_self {N l : ℕ} (hl : 0 < l) (hlN : l ≤ N) (a : ℕ → ℝ) :
    B N a (preVec l) (preVec l) = (l : ℝ) ^ 2 * (cN l a - cN N a) := by
  rw [B_self, prefix_G hlN, prefix_D hlN]
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hc : (∑ n ∈ range l, ∑ m ∈ range l, a (n + m + 1)) =
      cN l a * (l : ℝ) ^ 2 := by
    unfold cN
    rw [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hlr))]
    simp_rw [← Fin.sum_univ_eq_sum_range]
  rw [hc]
  ring

private theorem B_prefix_self_nonneg {N l : ℕ} (hl : 0 < l) (hlN : l ≤ N)
    {a : ℕ → ℝ} (hdec : ∀ j, 1 ≤ j → a (j + 1) < a j) :
    0 ≤ B N a (preVec l) (preVec l) := by
  rw [B_prefix_self hl hlN]
  apply mul_nonneg (sq_nonneg _)
  apply sub_nonneg.mpr
  by_cases h : l = N
  · simp [h]
  · have hlt : l < N := lt_of_le_of_ne hlN h
    cases l with
    | zero => omega
    | succ l =>
      cases N with
      | zero => omega
      | succ n => exact le_of_lt (cN_strictAnti hdec (by omega : l < n))

private theorem B_prefix_self_pos {N l : ℕ} (hl : 0 < l) (hlN : l < N)
    {a : ℕ → ℝ} (hdec : ∀ j, 1 ≤ j → a (j + 1) < a j) :
    0 < B N a (preVec l) (preVec l) := by
  rw [B_prefix_self hl (le_of_lt hlN)]
  apply mul_pos
  · exact sq_pos_of_pos (by exact_mod_cast hl)
  · apply sub_pos.mpr
    cases l with
    | zero => omega
    | succ l =>
      cases N with
      | zero => omega
      | succ n => exact cN_strictAnti hdec (by omega : l < n)

private theorem B_prefix_nonneg {N l t : ℕ} (hl : 0 < l) (ht : 0 < t)
    (hlN : l ≤ N) (htN : t ≤ N) {a : ℕ → ℝ}
    (hpos : ∀ j, 1 ≤ j → 0 < a j)
    (hdec : ∀ j, 1 ≤ j → a (j + 1) < a j) :
    0 ≤ B N a (preVec l) (preVec t) := by
  rcases le_total l t with h | h
  · exact le_trans (B_prefix_self_nonneg hl hlN hdec) (B_prefix_le h htN hpos)
  · rw [B_symm]
    exact le_trans (B_prefix_self_nonneg ht htN hdec) (B_prefix_le h hlN hpos)

private theorem B_add_left (N : ℕ) (a : ℕ → ℝ) (x y z : Fin N → ℝ) :
    B N a (fun n => x n + y n) z = B N a x z + B N a y z := by
  simp only [B, mul_add, add_mul, sum_add_distrib]
  ring

private theorem B_mul_left (N : ℕ) (a : ℕ → ℝ) (c : ℝ) (x y : Fin N → ℝ) :
    B N a (fun n => c * x n) y = c * B N a x y := by
  simp only [B]
  simp_rw [show ∀ d x y : ℝ, d * (c * x) * y = c * (d * x * y) by
    intros; ring]
  simp_rw [show ∀ x d y : ℝ, (c * x) * d * y = c * (x * d * y) by
    intros; ring]
  simp only [← Finset.mul_sum]
  ring

private theorem B_sum_left {ι : Type*} (s : Finset ι) (N : ℕ) (a : ℕ → ℝ)
    (v : ι → Fin N → ℝ) (y : Fin N → ℝ) :
    B N a (fun n => ∑ i ∈ s, v i n) y = ∑ i ∈ s, B N a (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [B]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    rw [B_add_left, ih]

/-- Expansion of the quadratic form in the nonnegative prefix increments. -/
private theorem B_expansion (N : ℕ) (a : ℕ → ℝ) (θ : Fin N → ℝ) :
    B N a θ θ =
      ∑ i ∈ range N, ∑ j ∈ range N,
        gap θ i * gap θ j * B N a (preVec (i + 1)) (preVec (j + 1)) := by
  let v : ℕ → Fin N → ℝ := fun i n => gap θ i * preVec (i + 1) n
  have hθ : θ = fun n => ∑ i ∈ range N, v i n := by
    funext n
    exact prefix_decomposition θ n
  conv_lhs => rw [hθ]
  rw [B_sum_left]
  apply sum_congr rfl
  intro i hi
  rw [B_symm, B_sum_left]
  apply sum_congr rfl
  intro j hj
  dsimp [v]
  rw [B_mul_left, B_symm, B_mul_left]
  ring

private theorem expansion_term_nonneg {N : ℕ} {a : ℕ → ℝ} {θ : Fin N → ℝ}
    (hpos : ∀ j, 1 ≤ j → 0 < a j)
    (hdec : ∀ j, 1 ≤ j → a (j + 1) < a j)
    (h0 : ∀ n, 0 ≤ θ n) (hmono : Antitone θ)
    {i j : ℕ} (hi : i ∈ range N) (hj : j ∈ range N) :
    0 ≤ gap θ i * gap θ j * B N a (preVec (i + 1)) (preVec (j + 1)) := by
  apply mul_nonneg (mul_nonneg (gap_nonneg h0 hmono i) (gap_nonneg h0 hmono j))
  apply B_prefix_nonneg (by omega) (by omega) (by simpa using hi) (by simpa using hj) hpos hdec

/-- Truncated Conjecture 3: the prefix decomposition gives the sharp lower bound. -/
theorem conj3 {N} (hN : 0 < N) {a : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j)
    (hdec : ∀ j, 1 ≤ j → a (j + 1) < a j) {θ : Fin N → ℝ} (h0 : ∀ n, 0 ≤ θ n)
    (hmono : Antitone θ) : cN N a * D N θ ≤ G N a θ := by
  have _ := hN
  have hb : 0 ≤ B N a θ θ := by
    rw [B_expansion]
    apply sum_nonneg
    intro i hi
    apply sum_nonneg
    intro j hj
    exact expansion_term_nonneg hpos hdec h0 hmono hi hj
  rw [B_self] at hb
  linarith

/-- Equality in truncated Conjecture 3 holds exactly for constant vectors. -/
theorem conj3_eq_iff {N} (hN : 0 < N) {a : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j)
    (hdec : ∀ j, 1 ≤ j → a (j + 1) < a j) {θ : Fin N → ℝ} (h0 : ∀ n, 0 ≤ θ n)
    (hmono : Antitone θ) : G N a θ = cN N a * D N θ ↔ ∀ n m, θ n = θ m := by
  constructor
  · intro heq
    have hz : B N a θ θ = 0 := by rw [B_self, heq, sub_self]
    rw [B_expansion] at hz
    have hrow : ∀ i ∈ range N, (∑ j ∈ range N,
        gap θ i * gap θ j * B N a (preVec (i + 1)) (preVec (j + 1))) = 0 := by
      apply (sum_eq_zero_iff_of_nonneg ?_).mp hz
      intro i hi
      apply sum_nonneg
      intro j hj
      exact expansion_term_nonneg hpos hdec h0 hmono hi hj
    have hgap : ∀ i, i + 1 < N → gap θ i = 0 := by
      intro i hi
      have himem : i ∈ range N := mem_range.mpr (by omega)
      have hterm := (sum_eq_zero_iff_of_nonneg
        (fun j hj => expansion_term_nonneg hpos hdec h0 hmono himem hj)).mp
          (hrow i himem) i himem
      have hbpos : 0 < B N a (preVec (i + 1)) (preVec (i + 1)) :=
        B_prefix_self_pos (by omega) hi hdec
      have hg := gap_nonneg h0 hmono i
      by_contra hn
      have hgp : 0 < gap θ i := lt_of_le_of_ne hg (Ne.symm hn)
      have hh : 0 < gap θ i * gap θ i * B N a (preVec (i + 1)) (preVec (i + 1)) :=
        mul_pos (mul_pos hgp hgp) hbpos
      linarith
    have hc : ∀ k, k < N → padded θ k = padded θ 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro hk
        have hh := hgap k hk
        change padded θ k - padded θ (k + 1) = 0 at hh
        exact (sub_eq_zero.mp hh).symm.trans (ih (by omega))
    intro n m
    have hn := hc n.val n.isLt
    have hm := hc m.val m.isLt
    simp only [padded, n.isLt, m.isLt, dite_true] at hn hm
    exact hn.trans hm.symm
  · intro hc
    let c := θ ⟨0, hN⟩
    have hθ : θ = fun n => c * preVec N n := by
      funext n
      simp [preVec, n.isLt, c, hc n ⟨0, hN⟩]
    apply sub_eq_zero.mp
    rw [← B_self, hθ, B_mul_left, B_symm, B_mul_left,
      B_prefix_self hN le_rfl]
    ring

end KayProof
