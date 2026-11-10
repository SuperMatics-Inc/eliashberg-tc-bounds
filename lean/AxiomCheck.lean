import KayProof

/-! Run with `lake env lean AxiomCheck.lean` after `lake build`.
Each line must print exactly `[propext, Classical.choice, Quot.sound]`. -/

open KayProof

#print axioms exists_max
#print axioms qf_le_kappa
#print axioms exists_cone_maximizer
#print axioms qf_sub
#print axioms mu_nonneg
#print axioms mu_one_ge
#print axioms comparison
#print axioms kappa_pos
#print axioms kappa_smul
#print axioms einstein_lt
#print axioms einstein_strictMonoOn
#print axioms disp_lt
#print axioms disp_strictAntiOn
#print axioms disp_le_einstein
#print axioms conj3
#print axioms conj3_eq_iff
