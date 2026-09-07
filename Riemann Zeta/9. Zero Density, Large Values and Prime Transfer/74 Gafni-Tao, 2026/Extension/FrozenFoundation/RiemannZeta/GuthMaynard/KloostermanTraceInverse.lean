import RiemannZeta.GuthMaynard.KloostermanEquationTen
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Trace of the inverse from the reversed minimal polynomial

This file supplies the inverse-root coefficient identity used in the
closed-point proof of Harcos equation (8).  It is stated for arbitrary finite
field extensions, so the later Kloosterman argument only has to perform the
Frobenius-orbit reindexing.
-/

open Polynomial

namespace RiemannZeta.GuthMaynard

theorem natTrailingDegree_eq_zero_of_coeff_zero_ne_zero
    {K : Type*} [Field K] (f : K[X]) (hf0 : f.coeff 0 ≠ 0) :
    f.natTrailingDegree = 0 := by
  exact natTrailingDegree_eq_zero.mpr (Or.inr hf0)

theorem reverse_natDegree_eq_of_coeff_zero_ne_zero
    {K : Type*} [Field K] (f : K[X]) (hf0 : f.coeff 0 ≠ 0) :
    f.reverse.natDegree = f.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero_of_coeff_zero_ne_zero f hf0,
    Nat.sub_zero]

theorem reverse_reverse_eq_of_coeff_zero_ne_zero
    {K : Type*} [Field K] (f : K[X]) (hf0 : f.coeff 0 ≠ 0) :
    f.reverse.reverse = f := by
  ext i
  rw [coeff_reverse, reverse_natDegree_eq_of_coeff_zero_ne_zero f hf0,
    coeff_reverse]
  exact congrArg (f.coeff ·) revAt_invol

/-- The monic reciprocal polynomial attached to a monic polynomial with
nonzero constant coefficient. -/
noncomputable def normalizedReverse
    {K : Type*} [Field K] (f : K[X]) : K[X] :=
  C (f.coeff 0)⁻¹ * f.reverse

theorem normalizedReverse_natDegree
    {K : Type*} [Field K] (f : K[X]) (hf0 : f.coeff 0 ≠ 0) :
    (normalizedReverse f).natDegree = f.natDegree := by
  unfold normalizedReverse
  rw [natDegree_C_mul (inv_ne_zero hf0),
    reverse_natDegree_eq_of_coeff_zero_ne_zero f hf0]

theorem normalizedReverse_monic
    {K : Type*} [Field K] (f : K[X]) (hf0 : f.coeff 0 ≠ 0) :
    (normalizedReverse f).Monic := by
  unfold normalizedReverse
  rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff,
    trailingCoeff, natTrailingDegree_eq_zero_of_coeff_zero_ne_zero f hf0]
  exact inv_mul_cancel₀ hf0

theorem aeval_normalizedReverse_inv_eq_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : K[X]) (x : L) (hx : x ≠ 0)
    (hroot : Polynomial.aeval x f = 0) :
    Polynomial.aeval x⁻¹ (normalizedReverse f) = 0 := by
  letI : Invertible x := invertibleOfNonzero hx
  have hrev : eval₂ (algebraMap K L) (⅟x) f.reverse = 0 :=
    (eval₂_reverse_eq_zero_iff (algebraMap K L) x f).2 hroot
  rw [invOf_eq_inv] at hrev
  simp only [normalizedReverse, aeval_def, eval₂_mul, eval₂_C, hrev, mul_zero]

theorem adjoin_inv_eq_adjoin
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) :
    IntermediateField.adjoin K {x⁻¹} = IntermediateField.adjoin K {x} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact (IntermediateField.adjoin K {x}).inv_mem
      (IntermediateField.mem_adjoin_simple_self K x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hmem := (IntermediateField.adjoin K {x⁻¹}).inv_mem
      (IntermediateField.mem_adjoin_simple_self K x⁻¹)
    simpa [inv_inv] using hmem

theorem minpoly_inv_natDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    (minpoly K x⁻¹).natDegree = (minpoly K x).natDegree := by
  rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x⁻¹),
    ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x),
    adjoin_inv_eq_adjoin x]

theorem minpoly_inv_eq_normalizedReverse
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) (hx : x ≠ 0) :
    minpoly K x⁻¹ = normalizedReverse (minpoly K x) := by
  have hmin0 : (minpoly K x).coeff 0 ≠ 0 :=
    minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x) hx
  have hdvd : minpoly K x⁻¹ ∣ normalizedReverse (minpoly K x) :=
    minpoly.dvd K x⁻¹ (aeval_normalizedReverse_inv_eq_zero
      (minpoly K x) x hx (minpoly.aeval K x))
  have hdeg : (normalizedReverse (minpoly K x)).natDegree ≤
      (minpoly K x⁻¹).natDegree := by
    rw [normalizedReverse_natDegree (minpoly K x) hmin0,
      minpoly_inv_natDegree x]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (Algebra.IsIntegral.isIntegral x⁻¹))
    (normalizedReverse_monic (minpoly K x) hmin0)
    hdvd hdeg).symm

theorem trace_inv_eq_finrank_mul_coeff_one_div_coeff_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) (hx : x ≠ 0) :
    Algebra.trace K L x⁻¹ =
      Module.finrank (IntermediateField.adjoin K {x}) L *
        -((minpoly K x).coeff 1 / (minpoly K x).coeff 0) := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff,
    minpoly_inv_eq_normalizedReverse x hx]
  rw [adjoin_inv_eq_adjoin x]
  congr 1
  have hmin0 : (minpoly K x).coeff 0 ≠ 0 :=
    minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x) hx
  have hdeg : 0 < (minpoly K x).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)
  rw [nextCoeff, normalizedReverse_natDegree _ hmin0, if_neg hdeg.ne']
  unfold normalizedReverse
  rw [coeff_C_mul, coeff_reverse, revAt_le (by omega),
    Nat.sub_sub_self (by omega : 1 ≤ (minpoly K x).natDegree)]
  simp only [div_eq_mul_inv, neg_inj]
  rw [mul_comm]

end RiemannZeta.GuthMaynard
