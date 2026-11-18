import KayProof.Rayleigh

open Finset

namespace KayProof

/-- A strictly positive matrix preserving the decreasing cone has every positive
fixed vector in that cone. Compact maximization of the minimum coordinate ratio
avoids any appeal to Perron–Frobenius theory. -/
private theorem antitone_of_positive_fixed {N : ℕ} (hN : 0 < N)
    (Q : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ)
    (hy : ∀ n, 0 < y n) (hQ : ∀ n m, 0 < Q n m)
    (hfix : ∀ n, ∑ m, Q n m * y m = y n)
    (hpres : ∀ v : Fin N → ℝ, (∀ n, 0 ≤ v n) → Antitone v →
      Antitone (fun n => ∑ m, Q n m * v m)) : Antitone y := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let α (v : Fin N → ℝ) : ℝ := univ.inf' univ_nonempty (fun n => v n / y n)
  let S : Set (Fin N → ℝ) := Set.Icc 0 y ∩ {v | Antitone v}
  have hclosed : IsClosed {v : Fin N → ℝ | Antitone v} := by
    have : {v : Fin N → ℝ | Antitone v} =
        ⋂ n : Fin N, ⋂ m : Fin N, ⋂ (_ : n ≤ m), {v | v m ≤ v n} := by
      ext v
      simp [Antitone]
    rw [this]
    exact isClosed_iInter fun n => isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply m) (continuous_apply n)
  have hcompact : IsCompact S := isCompact_Icc.inter_right hclosed
  let c : ℝ := univ.inf' univ_nonempty y
  have hc : 0 < c := (lt_inf'_iff _).2 (fun n _ => hy n)
  have hcy (n : Fin N) : c ≤ y n := inf'_le _ (mem_univ n)
  have hv0 : (fun _ : Fin N => c) ∈ S := by
    exact ⟨⟨fun _ => hc.le, hcy⟩, fun _ _ _ => le_rfl⟩
  have hα : Continuous α := by
    apply Continuous.finset_inf'_apply
    intro n _
    exact (continuous_apply n : Continuous (fun v : Fin N → ℝ => v n)).div_const (y n)
  obtain ⟨v, hv, hmax⟩ := hcompact.exists_isMaxOn ⟨_, hv0⟩ hα.continuousOn
  have ht : 0 < α v := lt_of_lt_of_le
    ((lt_inf'_iff _).2 (fun n _ => div_pos hc (hy n))) (hmax hv0)
  have hlow (n : Fin N) : α v * y n ≤ v n :=
    (le_div_iff₀ (hy n)).mp (inf'_le _ (mem_univ n))
  let u : Fin N → ℝ := fun n => ∑ m, Q n m * v m
  have hu : u ∈ S := by
    refine ⟨⟨?_, ?_⟩, hpres v hv.1.1 hv.2⟩
    · intro n
      exact sum_nonneg fun m _ => mul_nonneg (hQ n m).le (hv.1.1 m)
    · intro n
      calc
        u n ≤ ∑ m, Q n m * y m := sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_left (hv.1.2 m) (hQ n m).le
        _ = y n := hfix n
  have heq : ∀ n, v n = α v * y n := by
    by_contra h
    push_neg at h
    obtain ⟨j, hj⟩ := h
    have hjpos : 0 < v j - α v * y j := by have := hlow j; grind
    have hu_gt (n : Fin N) : α v < u n / y n := by
      have hsum : 0 < ∑ m, Q n m * (v m - α v * y m) := by
        apply sum_pos'
        · intro m _
          exact mul_nonneg (hQ n m).le (sub_nonneg.mpr (hlow m))
        · exact ⟨j, mem_univ j, mul_pos (hQ n j) hjpos⟩
      have hexpand : (∑ m, Q n m * (v m - α v * y m)) = u n - α v * y n := by
        simp only [mul_sub, sum_sub_distrib]
        rw [show (∑ m, Q n m * (α v * y m)) = α v * ∑ m, Q n m * y m by
          rw [mul_sum]; apply sum_congr rfl; intro m _; ring]
        rw [hfix]
      rw [hexpand] at hsum
      exact (lt_div_iff₀ (hy n)).2 (by linarith)
    have : α v < α u := (lt_inf'_iff _).2 (fun n _ => hu_gt n)
    exact (not_lt_of_ge (hmax hu)) this
  intro n m hnm
  have := hv.2 hnm
  rw [heq m, heq n] at this
  exact (mul_le_mul_iff_right₀ ht).mp this

private def rowKernel (b : ℕ → ℝ) (n m : ℕ) : ℝ :=
  b (Nat.dist n m) + b (n + m + 1)

/-- The difference of two consecutive row-prefix sums telescopes to two endpoints. -/
private theorem row_prefix_sub (b : ℕ → ℝ) (n l : ℕ) :
    (∑ m ∈ range (l + 1), rowKernel b n m) -
        (∑ m ∈ range (l + 1), rowKernel b (n + 1) m) =
      b (Nat.dist n l) - b (n + l + 2) := by
  induction l with
  | zero => simp [rowKernel, Nat.dist_zero_right]; ring
  | succ l ih =>
    rw [sum_range_succ (f := rowKernel b n) (l + 1),
      sum_range_succ (f := rowKernel b (n + 1)) (l + 1)]
    have hd : Nat.dist (n + 1) (l + 1) = Nat.dist n l := Nat.dist_succ_succ
    simp only [rowKernel] at ih ⊢
    rw [hd]
    have hi : n + (l + 1) + 1 = n + l + 2 := by omega
    have hj : n + 1 + (l + 1) + 1 = n + (l + 1) + 2 := by omega
    rw [hi, hj]
    linarith

/-- Abel summation: nonnegative prefix sums pair nonnegatively with a decreasing weight. -/
private theorem weighted_sum_nonneg (f v : ℕ → ℝ) (N : ℕ)
    (hf : ∀ l, l ≤ N → 0 ≤ ∑ i ∈ range l, f i)
    (hv : ∀ i, i < N → 0 ≤ v i)
    (hdec : ∀ i, i + 1 < N → v (i + 1) ≤ v i) :
    0 ≤ ∑ i ∈ range N, v i * f i := by
  by_cases hN : N = 0
  · subst N; simp
  have hid := sum_range_by_parts (fun i => v i) (fun i => f i) N
  simp only [smul_eq_mul] at hid
  rw [hid]
  apply sub_nonneg.mpr
  apply le_trans _ (mul_nonneg (hv _ (by omega)) (hf N le_rfl))
  apply sum_nonpos
  intro i hi
  have hi' : i < N - 1 := mem_range.mp hi
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (hdec i (by omega))) (hf (i + 1) (by omega))

/-- Positive decreasing kernels send positive decreasing vectors to decreasing vectors. -/
private theorem rowKernel_antitone {N : ℕ} (b : ℕ → ℝ) (hb : Antitone b)
    (v : Fin N → ℝ) (hv : ∀ n, 0 ≤ v n) (hdec : Antitone v) :
    Antitone (fun n : ℕ => ∑ m : Fin N, rowKernel b n m.val * v m) := by
  apply antitone_nat_of_succ_le
  intro n
  let V : ℕ → ℝ := fun i => if h : i < N then v ⟨i, h⟩ else 0
  let f : ℕ → ℝ := fun m => rowKernel b n m - rowKernel b (n + 1) m
  have hp (l : ℕ) (hl : l ≤ N) : 0 ≤ ∑ i ∈ range l, f i := by
    cases l with
    | zero => simp
    | succ l =>
      simp only [f, sum_sub_distrib]
      rw [row_prefix_sub]
      exact sub_nonneg.mpr (hb (by unfold Nat.dist; omega))
  have hh := weighted_sum_nonneg f V N hp (by
    intro i hi
    simpa [V, hi] using hv ⟨i, hi⟩) (by
    intro i hi
    simpa [V, hi, show i < N by omega] using
      hdec (show (⟨i, by omega⟩ : Fin N) ≤ ⟨i + 1, hi⟩ from by simp))
  have he : (∑ i ∈ range N, V i * f i) =
      (∑ m : Fin N, rowKernel b n m.val * v m) -
        (∑ m : Fin N, rowKernel b (n + 1) m.val * v m) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [V, Fin.is_lt, dite_true, f, mul_sub, sum_sub_distrib]
    congr 1 <;> apply sum_congr rfl <;> intro i _ <;> ring
  rw [he] at hh
  exact sub_nonneg.mp hh

private theorem qf_scale {N : ℕ} (a : ℕ → ℝ) (c : ℝ) (x : Fin N → ℝ) :
    qf N a (fun n => c * x n) = c ^ 2 * qf N a x := by
  unfold qf
  simp_rw [show ∀ n m, c * x n * K N a n m * (c * x m) =
    c ^ 2 * (x n * K N a n m * x m) by intros; ring, ← mul_sum]

/-- Homogeneous extension of the unit-sphere Rayleigh bound. -/
private theorem qf_le_norm {N : ℕ} (a : ℕ → ℝ) (x : Fin N → ℝ) :
    qf N a x ≤ kappa N a * ∑ n, x n ^ 2 := by
  let S : ℝ := ∑ n, x n ^ 2
  have hS : 0 ≤ S := sum_nonneg fun n _ => sq_nonneg (x n)
  rcases eq_or_lt_of_le hS with hS | hS
  · have hx : x = 0 := by
      funext n
      have hn : x n ^ 2 ≤ S := single_le_sum (fun m _ => sq_nonneg (x m)) (mem_univ n)
      have : x n = 0 := by nlinarith
      exact this
    subst x
    simp [qf]
  · let r := Real.sqrt S
    have hr : 0 < r := Real.sqrt_pos.2 hS
    have hr2 : r ^ 2 = S := Real.sq_sqrt hS.le
    let z : Fin N → ℝ := fun n => x n / r
    have hz : z ∈ sphere N := by
      change (∑ n, (x n / r) ^ 2) = 1
      simp only [div_pow, ← sum_div]
      rw [hr2]
      exact div_self hS.ne'
    have he : qf N a x = S * qf N a z := by
      rw [← hr2, ← qf_scale]
      congr 1
      funext n
      exact (mul_div_cancel₀ (x n) hr.ne').symm
    rw [he]
    exact (mul_le_mul_of_nonneg_left (qf_le_kappa a hz) hS.le).trans_eq (mul_comm _ _)

private theorem bilinear_symm {N : ℕ} (a : ℕ → ℝ) (x u : Fin N → ℝ) :
    (∑ n, ∑ m, x n * K N a n m * u m) =
      ∑ n, ∑ m, u n * K N a n m * x m := by
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro m _
  rw [K_symm]
  ring

/-- A maximizing unit vector satisfies the eigenvector equation. -/
private theorem maximizer_eigen {N : ℕ} (a : ℕ → ℝ) (z : Fin N → ℝ)
    (hz : z ∈ sphere N) (hmax : qf N a z = kappa N a) :
    ∀ n, ∑ m, K N a n m * z m = kappa N a * z n := by
  classical
  intro n
  let u : Fin N → ℝ := Pi.single n 1
  have he (t : ℝ) :
      qf N a (fun m => z m + t * u m) =
        qf N a z + 2 * t * (∑ m, K N a n m * z m) + t ^ 2 * K N a n n := by
    have hcross := bilinear_symm a z u
    have hu : (∑ i, ∑ j, u i * K N a i j * z j) = ∑ j, K N a n j * z j := by
      simp [u, Pi.single_apply]
    have huu : qf N a u = K N a n n := by simp [qf, u, Pi.single_apply]
    have hexpand :
        qf N a (fun m => z m + t * u m) =
          qf N a z +
            t * (∑ i, ∑ j, z i * K N a i j * u j) +
            t * (∑ i, ∑ j, u i * K N a i j * z j) + t ^ 2 * qf N a u := by
      unfold qf
      simp_rw [show ∀ i j, (z i + t * u i) * K N a i j * (z j + t * u j) =
        (z i * K N a i j * z j) + t * (z i * K N a i j * u j) +
          t * (u i * K N a i j * z j) + t ^ 2 * (u i * K N a i j * u j) by
            intros; ring, sum_add_distrib, ← mul_sum]
    rw [hexpand, hcross, hu, huu]
    ring
  have hn (t : ℝ) :
      (∑ m, (z m + t * u m) ^ 2) = 1 + 2 * t * z n + t ^ 2 := by
    simp_rw [show ∀ m, (z m + t * u m) ^ 2 =
      z m ^ 2 + (2 * t * z m * u m) + t ^ 2 * u m ^ 2 by intros; ring]
    simp only [sum_add_distrib, ← mul_sum]
    have hz' : ∑ m, z m ^ 2 = 1 := hz
    simp [hz', u, Pi.single_apply]
  have hp (t : ℝ) :
      (K N a n n - kappa N a) * (t * t) +
        (2 * ((∑ m, K N a n m * z m) - kappa N a * z n)) * t + 0 ≤ 0 := by
    have := qf_le_norm a (fun m => z m + t * u m)
    rw [he, hn, hmax] at this
    nlinarith
  have hd := discrim_le_zero_of_nonpos hp
  unfold discrim at hd
  nlinarith [sq_nonneg ((∑ m, K N a n m * z m) - kappa N a * z n)]

private theorem weight_pos (n : ℕ) : 0 < w n := by unfold w; positivity

private theorem root_pos (n : ℕ) : 0 < s n := Real.sqrt_pos.2 (weight_pos n)

private theorem root_sq (n : ℕ) : s n ^ 2 = w n := Real.sq_sqrt (weight_pos n).le

private theorem offdiag_pos {N : ℕ} {a : ℕ → ℝ} (ha : IsKernel a)
    (n m : Fin N) (hnm : n ≠ m) : 0 < K N a n m := by
  have hd : 1 ≤ Nat.dist n.val m.val := by
    have hv : n.val ≠ m.val := fun h => hnm (Fin.ext h)
    unfold Nat.dist
    omega
  have h1 := ha.1 _ hd
  have h2 := ha.1 (n.val + m.val + 1) (by omega)
  simpa only [K, hnm, ite_false, sub_zero] using
    div_pos (add_pos h1 h2) (mul_pos (root_pos n.val) (root_pos m.val))

private theorem qf_abs_ge {N : ℕ} {a : ℕ → ℝ} (ha : IsKernel a) (x : Fin N → ℝ) :
    qf N a x ≤ qf N a (fun n => |x n|) := by
  classical
  apply sum_le_sum
  intro n _
  apply sum_le_sum
  intro m _
  by_cases h : n = m
  · subst m
    have hh : |x n| * K N a n n * |x n| = x n * K N a n n * x n := by
      calc
        _ = K N a n n * |x n| ^ 2 := by ring
        _ = K N a n n * x n ^ 2 := by rw [sq_abs]
        _ = _ := by ring
    exact hh.ge
  · have hp := mul_le_mul_of_nonneg_right
      (le_abs_self (x n * x m)) (offdiag_pos ha n m h).le
    rw [abs_mul] at hp
    nlinarith

/-- Absolute values and irreducibility give a strictly positive maximizing eigenvector. -/
private theorem exists_positive_maximizer {N : ℕ} (hN : 0 < N)
    {a : ℕ → ℝ} (ha : IsKernel a) :
    ∃ z ∈ sphere N, qf N a z = kappa N a ∧
      (∀ n, 0 < z n) ∧ (∀ n, ∑ m, K N a n m * z m = kappa N a * z n) := by
  classical
  obtain ⟨x, hx, hmax⟩ := exists_max hN a
  let z : Fin N → ℝ := fun n => |x n|
  have hz : z ∈ sphere N := by
    change (∑ n, |x n| ^ 2) = 1
    simpa only [sq_abs] using (show ∑ n, x n ^ 2 = 1 from hx)
  have hzmax : qf N a z = kappa N a :=
    le_antisymm (qf_le_kappa a hz) (hmax ▸ qf_abs_ge ha x)
  have heig := maximizer_eigen a z hz hzmax
  have hz0 (n : Fin N) : 0 ≤ z n := abs_nonneg _
  have hnonzero : ∃ j, 0 < z j := by
    by_contra h
    push Not at h
    have hzall : ∀ n, z n = 0 := fun n => le_antisymm (h n) (hz0 n)
    have hs : ∑ n, z n ^ 2 = 1 := hz
    simp [hzall] at hs
  obtain ⟨j, hj⟩ := hnonzero
  refine ⟨z, hz, hzmax, ?_, heig⟩
  intro n
  by_contra h
  have hn : z n = 0 := le_antisymm (le_of_not_gt h) (hz0 n)
  have hnj : n ≠ j := by intro he; subst j; linarith
  have hs : 0 < ∑ m, K N a n m * z m := by
    apply sum_pos'
    · intro m _
      by_cases hm : n = m
      · subst m; simp [hn]
      · exact mul_nonneg (offdiag_pos ha n m hm).le (hz0 m)
    · exact ⟨j, mem_univ j, mul_pos (offdiag_pos ha n j hnj) hj⟩
  rw [heig, hn, mul_zero] at hs
  exact lt_irrefl _ hs

private theorem kappa_ge_first {N : ℕ} (hN : 0 < N) (a : ℕ → ℝ) :
    a 1 ≤ kappa N a := by
  classical
  let e : Fin N → ℝ := Pi.single ⟨0, hN⟩ 1
  have he : e ∈ sphere N := by simp [e, sphere, Pi.single_apply]
  have hq : qf N a e = a 1 := by
    simp [qf, e, Pi.single_apply, K, s, w]
  exact hq ▸ qf_le_kappa a he

private def adjusted (a : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then a 1 else a j

private theorem adjusted_pos {a : ℕ → ℝ} (ha : IsKernel a) (j : ℕ) :
    0 < adjusted a j := by
  cases j with
  | zero => simpa [adjusted] using ha.1 1 le_rfl
  | succ j => simpa [adjusted] using ha.1 (j + 1) (by omega)

private theorem adjusted_antitone {a : ℕ → ℝ} (ha : IsKernel a) :
    Antitone (adjusted a) := by
  apply antitone_nat_of_succ_le
  intro j
  cases j with
  | zero => simp [adjusted]
  | succ j => simpa [adjusted] using ha.2 (j + 1) (by omega)

/-- The diagonal correction in the gap-variable eigen-equation. -/
private theorem gap_entry {N : ℕ} (a : ℕ → ℝ) (n m : Fin N) :
    rowKernel (adjusted a) n.val m.val / s m.val =
      s n.val * K N a n m +
        if m = n then (a 1 + 2 * ∑ j ∈ Icc 1 n.val, a j) / s n.val else 0 := by
  classical
  have hn := (root_pos n.val).ne'
  have hm := (root_pos m.val).ne'
  by_cases h : n = m
  · subst m
    simp only [rowKernel, adjusted, Nat.dist_self, ite_true, K,
      show n.val + n.val + 1 ≠ 0 by omega, ite_false]
    rw [← root_sq n.val]
    field_simp
    <;> ring
  · have hd : Nat.dist n.val m.val ≠ 0 := by
      have hv : n.val ≠ m.val := fun hh => h (Fin.ext hh)
      unfold Nat.dist
      omega
    simp only [rowKernel, adjusted, hd, ite_false, K, h, Ne.symm h,
      show n.val + m.val + 1 ≠ 0 by omega, sub_zero, add_zero]
    field_simp

/-- Lemma 7: a finite KAY Rayleigh maximizer can be chosen positive and
non-increasing in the gap variables. -/
theorem exists_cone_maximizer {N} (hN : 0 < N) {a : ℕ → ℝ} (ha : IsKernel a) :
    ∃ x ∈ sphere N, qf N a x = kappa N a ∧ InCone x := by
  classical
  obtain ⟨z, hz, hzmax, hzpos, heig⟩ := exists_positive_maximizer hN ha
  let y : Fin N → ℝ := fun n => z n / s n.val
  have hy (n : Fin N) : 0 < y n := div_pos (hzpos n) (root_pos n.val)
  have hk : 0 < kappa N a := lt_of_lt_of_le (ha.1 1 le_rfl) (kappa_ge_first hN a)
  let d : ℕ → ℝ := fun n => kappa N a * w n + a 1 + 2 * ∑ j ∈ Icc 1 n, a j
  have hdpos (n : ℕ) : 0 < d n := by
    have hsum : 0 ≤ ∑ j ∈ Icc 1 n, a j :=
      sum_nonneg fun j hj => (ha.1 j (mem_Icc.mp hj).1).le
    dsimp [d]
    positivity [weight_pos n, ha.1 1 le_rfl]
  have hdmono : Monotone d := by
    intro n m hnm
    have hw : w n ≤ w m := by
      unfold w
      exact_mod_cast (show 2 * n + 1 ≤ 2 * m + 1 by omega)
    have hs : (∑ j ∈ Icc 1 n, a j) ≤ ∑ j ∈ Icc 1 m, a j := by
      apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hnm)
      intro j hj _
      exact (ha.1 j (mem_Icc.mp hj).1).le
    dsimp [d]
    nlinarith
  let C : Matrix (Fin N) (Fin N) ℝ := fun n m => rowKernel (adjusted a) n.val m.val
  have hCpos (n m : Fin N) : 0 < C n m :=
    add_pos (adjusted_pos ha _) (adjusted_pos ha _)
  have hCy (n : Fin N) : (∑ m, C n m * y m) = d n.val * y n := by
    have hterm (m : Fin N) :
        C n m * y m = s n.val * (K N a n m * z m) +
          if m = n then (a 1 + 2 * ∑ j ∈ Icc 1 n.val, a j) * y n else 0 := by
      have he := congrArg (fun t : ℝ => t * z m) (gap_entry a n m)
      by_cases hm : m = n
      · subst m
        simp only [ite_true] at he ⊢
        dsimp [C, y]
        convert he using 1 <;> ring
      · simp only [hm, ite_false, zero_mul, add_zero] at he ⊢
        dsimp [C, y]
        convert he using 1 <;> ring
    simp_rw [hterm, sum_add_distrib, ← mul_sum]
    simp only [sum_ite_eq', mem_univ, ite_true]
    rw [heig]
    dsimp [d, y]
    rw [← root_sq n.val]
    field_simp
    <;> ring
  let Q : Matrix (Fin N) (Fin N) ℝ := fun n m => C n m / d n.val
  have hQpos (n m : Fin N) : 0 < Q n m := div_pos (hCpos n m) (hdpos n.val)
  have hQy (n : Fin N) : (∑ m, Q n m * y m) = y n := by
    simp only [Q, div_mul_eq_mul_div, ← sum_div]
    rw [hCy]
    exact mul_div_cancel_left₀ (y n) (hdpos n.val).ne'
  have hpres (v : Fin N → ℝ) (hv : ∀ n, 0 ≤ v n) (hvdec : Antitone v) :
      Antitone (fun n => ∑ m, Q n m * v m) := by
    have hrow := rowKernel_antitone (adjusted a) (adjusted_antitone ha) v hv hvdec
    intro n m hnm
    have hnum (i : Fin N) : 0 ≤ ∑ j, C i j * v j :=
      sum_nonneg fun j _ => mul_nonneg (hCpos i j).le (hv j)
    simp only [Q, div_mul_eq_mul_div, ← sum_div]
    exact div_le_div₀ (hnum n) (hrow hnm) (hdpos n.val) (hdmono hnm)
  have hydec := antitone_of_positive_fixed hN Q y hy hQpos hQy hpres
  exact ⟨z, hz, hzmax, (fun n => (hzpos n).le), hydec⟩

end KayProof
