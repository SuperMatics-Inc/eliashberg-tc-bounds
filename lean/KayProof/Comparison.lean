import KayProof.Cone
import KayProof.Mu

open Finset

namespace KayProof

private theorem comparison_s_pos (n : ℕ) : 0 < s n := by
  apply Real.sqrt_pos.2
  simp only [w]
  positivity

private theorem cone_first_pos {N : ℕ} (hN : 0 < N) {x : Fin N → ℝ}
    (hx : x ∈ sphere N) (hcone : InCone x) : 0 < x ⟨0, hN⟩ := by
  by_contra h
  have hz : x ⟨0, hN⟩ = 0 := le_antisymm (le_of_not_gt h) (hcone.1 _)
  have hxzero (n : Fin N) : x n = 0 := by
    have hgap := hcone.2 ⟨0, hN⟩ n (Fin.le_def.mpr (Nat.zero_le _))
    rw [hz, zero_div] at hgap
    have hn := (div_le_iff₀ (comparison_s_pos n.val)).mp hgap
    exact le_antisymm (by simpa using hn) (hcone.1 n)
  have hsum : ∑ n, x n ^ 2 = 0 := by simp [hxzero]
  have hunit : ∑ n, x n ^ 2 = 1 := hx
  linarith

/-- Theorem 1: increasing the kernel, strictly at its first entry, increases the top eigenvalue. -/
theorem comparison {N : ℕ} (hN : 0 < N) {a b : ℕ → ℝ} (ha : IsKernel a)
    (hab : ∀ j, 1 ≤ j → a j ≤ b j) (h1 : a 1 < b 1) :
    kappa N a < kappa N b := by
  obtain ⟨x, hx, hmax, hcone⟩ := exists_cone_maximizer hN ha
  have hnonneg (j : ℕ) (hj : j ∈ Icc 1 (2 * N)) :
      0 ≤ (b j - a j) * mu N j x :=
    mul_nonneg (sub_nonneg.mpr (hab j (mem_Icc.mp hj).1))
      (mu_nonneg hcone (mem_Icc.mp hj).1)
  have hmu : 0 < mu N 1 x :=
    lt_of_lt_of_le (sq_pos_of_pos (cone_first_pos hN hx hcone)) (mu_one_ge hN hcone)
  have hmem : 1 ∈ Icc 1 (2 * N) := by simp only [mem_Icc]; omega
  have hsum : 0 < ∑ j ∈ Icc 1 (2 * N), (b j - a j) * mu N j x :=
    lt_of_lt_of_le (mul_pos (sub_pos.mpr h1) hmu)
      (single_le_sum hnonneg hmem)
  have hdiff := qf_sub N a b x
  have hupper := qf_le_kappa b hx
  linarith

private theorem comparison_le {N : ℕ} (hN : 0 < N) {a b : ℕ → ℝ}
    (ha : IsKernel a) (hab : ∀ j, 1 ≤ j → a j ≤ b j) :
    kappa N a ≤ kappa N b := by
  obtain ⟨x, hx, hmax, hcone⟩ := exists_cone_maximizer hN ha
  have hsum : 0 ≤ ∑ j ∈ Icc 1 (2 * N), (b j - a j) * mu N j x := by
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (sub_nonneg.mpr (hab j (mem_Icc.mp hj).1))
      (mu_nonneg hcone (mem_Icc.mp hj).1)
  have hdiff := qf_sub N a b x
  have hupper := qf_le_kappa b hx
  linarith

private theorem comparison_K_smul (N : ℕ) (a : ℕ → ℝ) (c : ℝ) (n m : Fin N) :
    K N (fun j => c * a j) n m = c * K N a n m := by
  classical
  unfold K
  by_cases h : n = m
  · simp only [h, if_true]
    rw [← mul_sum]
    ring
  · simp only [h, if_false]
    ring

private theorem comparison_qf_smul (N : ℕ) (a : ℕ → ℝ) (c : ℝ) (x : Fin N → ℝ) :
    qf N (fun j => c * a j) x = c * qf N a x := by
  unfold qf
  simp_rw [comparison_K_smul]
  calc
    (∑ n, ∑ m, x n * (c * K N a n m) * x m) =
        ∑ n, ∑ m, c * (x n * K N a n m * x m) := by
      apply sum_congr rfl
      intro n hn
      apply sum_congr rfl
      intro m hm
      ring
    _ = c * ∑ n, ∑ m, x n * K N a n m * x m := by simp_rw [← mul_sum]

/-- Positive scalar multiplication of a kernel scales its Rayleigh maximum. -/
theorem kappa_smul {N : ℕ} (a : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    kappa N (fun j => c * a j) = c * kappa N a := by
  by_cases hN : 0 < N
  · obtain ⟨x, hx, hmax⟩ := exists_max hN a
    obtain ⟨y, hy, hmax'⟩ := exists_max hN (fun j => c * a j)
    apply le_antisymm
    · rw [← hmax', comparison_qf_smul]
      exact mul_le_mul_of_nonneg_left (qf_le_kappa a hy) hc.le
    · rw [← hmax]
      have h := qf_le_kappa (fun j => c * a j) hx
      simpa only [comparison_qf_smul] using h
  · have hzero : N = 0 := by omega
    subst N
    have hsphere : sphere 0 = ∅ := by ext x; simp [sphere]
    simp [kappa, hsphere]

/-- The first coordinate unit vector gives the lower bound `a₁ ≤ κ_N[a]`. -/
theorem kappa_pos {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ} (_ha : IsKernel a) :
    a 1 ≤ kappa N a := by
  classical
  let x : Fin N → ℝ := Pi.single (⟨0, hN⟩ : Fin N) 1
  have hx : x ∈ sphere N := by simp [x, sphere, Pi.single_apply]
  have hq : qf N a x = a 1 := by
    simp [qf, x, Pi.single_apply, ite_mul, mul_ite, K, s, w]
  rw [← hq]
  exact qf_le_kappa a hx

private theorem comparison_nat_pos {j : ℕ} (hj : 1 ≤ j) : 0 < (j : ℝ) := by
  exact_mod_cast (show 0 < j by omega)

private theorem einstein_kernel {v : ℝ} (hv : 0 < v) : IsKernel (einstein v) := by
  constructor
  · intro j hj
    exact div_pos (sq_pos_of_pos hv) (add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) (sq_nonneg _))
  · intro j hj
    have hstep : (j : ℝ) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 (by exact_mod_cast Nat.le_succ j)
    exact div_le_div_of_nonneg_left (sq_nonneg v)
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) (sq_nonneg _))
      (add_le_add_right hstep (v ^ 2))

private theorem einstein_entry_strictMono {u v : ℝ} (hu : 0 < u) (huv : u < v)
    {j : ℕ} (hj : 1 ≤ j) : einstein u j < einstein v j := by
  have hv : 0 < v := hu.trans huv
  have hsq : u ^ 2 < v ^ 2 := (sq_lt_sq₀ hu.le hv.le).2 huv
  have hjpos : 0 < (j : ℝ) ^ 2 := sq_pos_of_pos (comparison_nat_pos hj)
  apply (div_lt_div_iff₀
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) hjpos.le)
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) hjpos.le)).2
  nlinarith [mul_pos (sub_pos.mpr hsq) hjpos]

private theorem einstein_entry_lt_invSq {v : ℝ} (hv : 0 < v)
    {j : ℕ} (hj : 1 ≤ j) : einstein v j < v ^ 2 * invSq j := by
  have hjpos : 0 < (j : ℝ) ^ 2 := sq_pos_of_pos (comparison_nat_pos hj)
  change v ^ 2 / (v ^ 2 + (j : ℝ) ^ 2) < v ^ 2 * (1 / (j : ℝ) ^ 2)
  rw [mul_one_div]
  exact div_lt_div_of_pos_left (sq_pos_of_pos hv) hjpos (by linarith [sq_pos_of_pos hv])

/-- Truncated Conjecture 1 (Einstein): `h^(N)(v) < g^(N) v²`. -/
theorem einstein_lt {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 0 < v) :
    kappa N (einstein v) < v ^ 2 * kappa N invSq := by
  have h := comparison hN (einstein_kernel hv)
    (fun j hj => (einstein_entry_lt_invSq hv hj).le)
    (einstein_entry_lt_invSq hv (show 1 ≤ (1 : ℕ) by rfl))
  rwa [kappa_smul invSq (sq_pos_of_pos hv)] at h

/-- Truncated Corollary 2: the Einstein Rayleigh maximum is strictly increasing in `v > 0`. -/
theorem einstein_strictMonoOn {N : ℕ} (hN : 0 < N) :
    StrictMonoOn (fun v => kappa N (einstein v)) (Set.Ioi 0) := by
  intro u hu v hv huv
  exact comparison hN (einstein_kernel hu)
    (fun j hj => (einstein_entry_strictMono hu huv hj).le)
    (einstein_entry_strictMono hu huv (show 1 ≤ (1 : ℕ) by rfl))

/-- The finite-mode phonon kernel, with nonnegative normalized mode weights in the theorems below. -/
noncomputable def disp {M : ℕ} (p ω : Fin M → ℝ) (T : ℝ) : ℕ → ℝ :=
  fun j => ∑ i, p i * (ω i ^ 2 / (ω i ^ 2 + (2 * Real.pi * T * j) ^ 2))

/-- The second frequency moment of a discrete phonon spectrum. -/
noncomputable def secondMoment {M : ℕ} (p ω : Fin M → ℝ) : ℝ :=
  ∑ i, p i * ω i ^ 2

private theorem positive_weight {M : ℕ} {p : Fin M → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : ∃ i, 0 < p i := by
  by_contra h
  push_neg at h
  have hz : ∑ i, p i = 0 := sum_eq_zero (fun i hi => le_antisymm (h i) (hp i))
  linarith

private theorem secondMoment_pos {M : ℕ} {p ω : Fin M → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hω : ∀ i, 0 < ω i) :
    0 < secondMoment p ω := by
  obtain ⟨i, hi⟩ := positive_weight hp hsum
  exact sum_pos' (fun i _ => mul_nonneg (hp i) (sq_nonneg _))
    ⟨i, mem_univ i, mul_pos hi (sq_pos_of_pos (hω i))⟩

private theorem thermal_scale_pos {T : ℝ} (hT : 0 < T) : 0 < 2 * Real.pi * T :=
  mul_pos (mul_pos (by norm_num) Real.pi_pos) hT

private theorem einstein_div {u A : ℝ} (hA : 0 < A) (j : ℕ) :
    einstein (u / A) j = u ^ 2 / (u ^ 2 + (A * (j : ℝ)) ^ 2) := by
  unfold einstein
  simp only [div_pow]
  have hden : u ^ 2 / A ^ 2 + (j : ℝ) ^ 2 =
      (u ^ 2 + (A * (j : ℝ)) ^ 2) / A ^ 2 := by
    field_simp [ne_of_gt hA]
    <;> ring
  rw [hden, div_div_div_cancel_right₀ (pow_ne_zero 2 (ne_of_gt hA))]

private theorem disp_kernel {M : ℕ} {p ω : Fin M → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hω : ∀ i, 0 < ω i)
    {T : ℝ} (hT : 0 < T) : IsKernel (disp p ω T) := by
  have hA := thermal_scale_pos hT
  have hmode (i : Fin M) : IsKernel
      (fun j => ω i ^ 2 / (ω i ^ 2 + (2 * Real.pi * T * (j : ℝ)) ^ 2)) := by
    simpa only [IsKernel, einstein_div hA] using einstein_kernel (div_pos (hω i) hA)
  obtain ⟨i, hi⟩ := positive_weight hp hsum
  constructor
  · intro j hj
    exact sum_pos' (fun k _ => mul_nonneg (hp k) ((hmode k).1 j hj).le)
      ⟨i, mem_univ i, mul_pos hi ((hmode i).1 j hj)⟩
  · intro j hj
    exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ((hmode i).2 j hj) (hp i))

private theorem disp_entry_lt_invSq {M : ℕ} {p ω : Fin M → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hω : ∀ i, 0 < ω i)
    {T : ℝ} (hT : 0 < T) {j : ℕ} (hj : 1 ≤ j) :
    disp p ω T j < (secondMoment p ω / (2 * Real.pi * T) ^ 2) * invSq j := by
  have hA := thermal_scale_pos hT
  have hjR := comparison_nat_pos hj
  have hden : 0 < (2 * Real.pi * T * (j : ℝ)) ^ 2 :=
    sq_pos_of_pos (mul_pos hA hjR)
  have hmode (i : Fin M) :
      ω i ^ 2 / (ω i ^ 2 + (2 * Real.pi * T * (j : ℝ)) ^ 2) <
        ω i ^ 2 / (2 * Real.pi * T * (j : ℝ)) ^ 2 :=
    div_lt_div_of_pos_left (sq_pos_of_pos (hω i)) hden (by linarith [sq_pos_of_pos (hω i)])
  obtain ⟨i, hi⟩ := positive_weight hp hsum
  have hlt : disp p ω T j <
      ∑ i, p i * (ω i ^ 2 / (2 * Real.pi * T * (j : ℝ)) ^ 2) := by
    apply sum_lt_sum
    · intro i hi
      exact mul_le_mul_of_nonneg_left (hmode i).le (hp i)
    · exact ⟨i, mem_univ i, mul_lt_mul_of_pos_left (hmode i) hi⟩
  have hsum_div : (∑ i, p i * (ω i ^ 2 / (2 * Real.pi * T * (j : ℝ)) ^ 2)) =
      secondMoment p ω / (2 * Real.pi * T * (j : ℝ)) ^ 2 := by
    unfold secondMoment
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum_div] at hlt
  have hscale : secondMoment p ω / (2 * Real.pi * T * (j : ℝ)) ^ 2 =
      (secondMoment p ω / (2 * Real.pi * T) ^ 2) * invSq j := by
    simp only [invSq, mul_pow, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rwa [hscale] at hlt

/-- Truncated Conjecture 2 for a finite discrete phonon spectrum. -/
theorem disp_lt {N M : ℕ} (hN : 0 < N) {p ω : Fin M → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hω : ∀ i, 0 < ω i)
    {T : ℝ} (hT : 0 < T) :
    kappa N (disp p ω T) <
      secondMoment p ω / (2 * Real.pi * T) ^ 2 * kappa N invSq := by
  have hcoef : 0 < secondMoment p ω / (2 * Real.pi * T) ^ 2 :=
    div_pos (secondMoment_pos hp hsum hω) (sq_pos_of_pos (thermal_scale_pos hT))
  have h := comparison hN (disp_kernel hp hsum hω hT)
    (fun j hj => (disp_entry_lt_invSq hp hsum hω hT hj).le)
    (disp_entry_lt_invSq hp hsum hω hT (show 1 ≤ (1 : ℕ) by rfl))
  rwa [kappa_smul invSq hcoef] at h

private theorem disp_entry_strictAnti {M : ℕ} {p ω : Fin M → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hω : ∀ i, 0 < ω i)
    {T U : ℝ} (hT : 0 < T) (hTU : T < U) {j : ℕ} (hj : 1 ≤ j) :
    disp p ω U j < disp p ω T j := by
  have hU : 0 < U := hT.trans hTU
  have hAT := thermal_scale_pos hT
  have hAU := thermal_scale_pos hU
  have hjR := comparison_nat_pos hj
  have hscale : 2 * Real.pi * T < 2 * Real.pi * U :=
    mul_lt_mul_of_pos_left hTU (mul_pos (by norm_num) Real.pi_pos)
  have hsq : (2 * Real.pi * T * (j : ℝ)) ^ 2 <
      (2 * Real.pi * U * (j : ℝ)) ^ 2 :=
    (sq_lt_sq₀ (mul_pos hAT hjR).le (mul_pos hAU hjR).le).2
      (mul_lt_mul_of_pos_right hscale hjR)
  have hmode (i : Fin M) :
      ω i ^ 2 / (ω i ^ 2 + (2 * Real.pi * U * (j : ℝ)) ^ 2) <
        ω i ^ 2 / (ω i ^ 2 + (2 * Real.pi * T * (j : ℝ)) ^ 2) :=
    div_lt_div_of_pos_left (sq_pos_of_pos (hω i))
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos (hω i)) (sq_nonneg _))
      (add_lt_add_right hsq (ω i ^ 2))
  obtain ⟨i, hi⟩ := positive_weight hp hsum
  apply sum_lt_sum
  · intro i hi
    exact mul_le_mul_of_nonneg_left (hmode i).le (hp i)
  · exact ⟨i, mem_univ i, mul_lt_mul_of_pos_left (hmode i) hi⟩

/-- The truncated dispersive Rayleigh maximum is strictly decreasing for `T > 0`. -/
theorem disp_strictAntiOn {N M : ℕ} (hN : 0 < N) {p ω : Fin M → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hω : ∀ i, 0 < ω i) :
    StrictAntiOn (fun T => kappa N (disp p ω T)) (Set.Ioi 0) := by
  intro T hT U hU hTU
  exact comparison hN (disp_kernel hp hsum hω hU)
    (fun j hj => (disp_entry_strictAnti hp hsum hω hT hTU hj).le)
    (disp_entry_strictAnti hp hsum hω hT hTU (show 1 ≤ (1 : ℕ) by rfl))

private theorem fraction_le_tangent {u m d : ℝ} (hu : 0 ≤ u) (hm : 0 < m) (hd : 0 < d) :
    u / (u + d) ≤ m / (m + d) + d / (m + d) ^ 2 * (u - m) := by
  have hud : 0 < u + d := add_pos_of_nonneg_of_pos hu hd
  have hmd : 0 < m + d := add_pos hm hd
  have hid : m / (m + d) + d / (m + d) ^ 2 * (u - m) - u / (u + d) =
      d * (u - m) ^ 2 / ((m + d) ^ 2 * (u + d)) := by
    field_simp [ne_of_gt hud, ne_of_gt hmd]
    <;> ring
  have hnonneg : 0 ≤ d * (u - m) ^ 2 / ((m + d) ^ 2 * (u + d)) := by positivity
  linarith

private theorem disp_entry_le_einstein {M : ℕ} {p ω : Fin M → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hω : ∀ i, 0 < ω i)
    {T : ℝ} (hT : 0 < T) {j : ℕ} (hj : 1 ≤ j) :
    disp p ω T j ≤
      einstein (Real.sqrt (secondMoment p ω) / (2 * Real.pi * T)) j := by
  let m := secondMoment p ω
  let d := (2 * Real.pi * T * (j : ℝ)) ^ 2
  have hm : 0 < m := secondMoment_pos hp hsum hω
  have hA := thermal_scale_pos hT
  have hd : 0 < d := sq_pos_of_pos (mul_pos hA (comparison_nat_pos hj))
  have hbound (i : Fin M) : p i * (ω i ^ 2 / (ω i ^ 2 + d)) ≤
      p i * (m / (m + d)) + d / (m + d) ^ 2 * (p i * ω i ^ 2 - p i * m) := by
    convert mul_le_mul_of_nonneg_left (fraction_le_tangent (sq_nonneg (ω i)) hm hd) (hp i) using 1
    <;> ring
  have hsum_bound : disp p ω T j ≤ m / (m + d) := by
    calc
      disp p ω T j ≤ ∑ i, (p i * (m / (m + d)) +
          d / (m + d) ^ 2 * (p i * ω i ^ 2 - p i * m)) :=
        sum_le_sum (fun i _ => hbound i)
      _ = m / (m + d) := by
        rw [sum_add_distrib, ← sum_mul, ← mul_sum, sum_sub_distrib, ← sum_mul]
        simp only [hsum]
        change 1 * (m / (m + d)) + d / (m + d) ^ 2 * (m - 1 * m) = m / (m + d)
        ring
  have heq : einstein (Real.sqrt (secondMoment p ω) / (2 * Real.pi * T)) j =
      m / (m + d) := by
    change einstein (Real.sqrt m / (2 * Real.pi * T)) j = m / (m + d)
    rw [einstein_div hA, Real.sq_sqrt hm.le]
  rwa [heq]

/-- Einstein optimality: the spectrum concentrated at the root-mean-square frequency is optimal. -/
theorem disp_le_einstein {N M : ℕ} (hN : 0 < N) {p ω : Fin M → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hω : ∀ i, 0 < ω i)
    {T : ℝ} (hT : 0 < T) :
    kappa N (disp p ω T) ≤
      kappa N (einstein (Real.sqrt (secondMoment p ω) / (2 * Real.pi * T))) := by
  exact comparison_le hN (disp_kernel hp hsum hω hT)
    (fun j hj => disp_entry_le_einstein hp hsum hω hT hj)

end KayProof
