import Dubon2026.SourceJPrimeTwistCoordinates

/-! DUB-17/18 -> numerical modular genus -> exact j-map degree ->
prime lower bound. The literal q-substituted j series cannot be a polynomial
in j: its root-of-unity orbit would force a positive j coefficient to vanish.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean.
Only the coefficient obstruction is selected; field integrality is supplied
by the already proved actual monic relation, without an irreducibility input.
-/
namespace Dubon2026.SourceFunctionField.PrimeDegreeAux
noncomputable section
variable {K : Type*} [Field K]

section PoleOrder

private theorem coeff_algebraMap_mul (c : K) (x : LaurentSeries K) (k : ℤ) :
    (algebraMap K (LaurentSeries K) c * x).coeff k = c * x.coeff k := by
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, HahnSeries.coeff_single_zero_mul]

theorem coeff_aeval_jqModC_of_lt (P : Polynomial K) {m : ℤ} (hm : m < -(P.natDegree : ℤ)) :
    (Polynomial.aeval (jqModC K) P).coeff m = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_algebraMap_mul, Dubon2026.SourceFunctionField.coeff_jqModC_pow_of_lt K (n := i) (m := m) (by omega), mul_zero]

theorem coeff_aeval_jqModC_neg_natDegree (P : Polynomial K) :
    (Polynomial.aeval (jqModC K) P).coeff (-(P.natDegree : ℤ)) = P.coeff P.natDegree := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single P.natDegree]
  · rw [coeff_algebraMap_mul, Dubon2026.SourceFunctionField.coeff_jqModC_pow_self K P.natDegree, mul_one]
  · intro i hi hin
    have hilt : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
    rw [coeff_algebraMap_mul, Dubon2026.SourceFunctionField.coeff_jqModC_pow_of_lt K (n := i) (m := -(P.natDegree : ℤ)) (by omega),
      mul_zero]
  · intro hn
    exact absurd (Finset.self_mem_range_succ P.natDegree) hn

end PoleOrder

section Forcing

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

theorem coeff_jqNModC_self : (jqNModC K p).coeff (-(p : ℤ)) = 1 := by
  rw [jqNModC_eq_TS, TS_coeff_neg, inv_one, Units.val_one]

theorem coeff_jqNModC_of_lt {m : ℤ} (hm : m < -(p : ℤ)) : (jqNModC K p).coeff m = 0 := by
  rw [jqNModC_eq_TS]
  exact TS_coeff_of_lt p 1 hm

variable {p} {P : Polynomial K}

theorem ne_zero_of_aeval_eq (h : Polynomial.aeval (jqModC K) P = jqNModC K p) : P ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  have h1 := coeff_jqNModC_self (K := K) p
  rw [← h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

theorem natDegree_eq_of_aeval_eq (h : Polynomial.aeval (jqModC K) P = jqNModC K p) : P.natDegree = p := by
  have hP0 : P ≠ 0 := ne_zero_of_aeval_eq h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : (Polynomial.aeval (jqModC K) P).coeff (-(p : ℤ)) = 0 := coeff_aeval_jqModC_of_lt P (by omega)
    rw [h, coeff_jqNModC_self] at h1
    exact one_ne_zero h1
  · have h1 := coeff_aeval_jqModC_neg_natDegree P
    rw [h, coeff_jqNModC_of_lt p (m := -(P.natDegree : ℤ)) (by omega)] at h1
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp h1.symm)

theorem monic_of_aeval_eq (h : Polynomial.aeval (jqModC K) P = jqNModC K p) : P.Monic := by
  have hd := natDegree_eq_of_aeval_eq h
  have h1 := coeff_aeval_jqModC_neg_natDegree P
  rw [h, hd, coeff_jqNModC_self] at h1
  show P.coeff P.natDegree = 1
  rw [hd]
  exact h1.symm

end Forcing
end
end Dubon2026.SourceFunctionField.PrimeDegreeAux
