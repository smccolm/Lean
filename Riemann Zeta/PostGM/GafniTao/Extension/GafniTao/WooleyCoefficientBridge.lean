import GafniTao.WooleySourceBox

/-!
# Coefficient-one specialization of the source means

The source-level Corollary 3.2 is uniform in finitely supported weights.
This file proves, rather than assumes, that its all-one box specialization is
the modular count used by `WooleyMonomialPadicConcentration`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleyWeightedMassSq_one (Q : ℕ) :
    wooleyWeightedMassSq (fun _ : Fin Q => (1 : ℂ)) = Q := by
  simp [wooleyWeightedMassSq]

theorem wooleyWeightedResidueMassSq_one (Q q : ℕ) (xi : ZMod q) :
    wooleyWeightedResidueMassSq (fun _ : Fin Q => (1 : ℂ)) xi =
      wooleyResidueMassSq Q q xi := by
  simp [wooleyWeightedResidueMassSq, wooleyResidueMassSq]

theorem wooleyWeightedGridSum_one
    (q k Q : ℕ) [NeZero q] (alpha : Fin k → ZMod q) :
    wooleyWeightedGridSum q k (fun _ : Fin Q => (1 : ℂ)) alpha =
      wooleyMonomialGridSum q k Q alpha := by
  simp [wooleyWeightedGridSum, wooleyMonomialGridSum]

theorem wooleyWeightedResidueGridSum_one
    (qB k Q qH : ℕ) [NeZero qB]
    (alpha : Fin k → ZMod qB) (xi : ZMod qH) :
    wooleyWeightedResidueGridSum qB k (fun _ : Fin Q => (1 : ℂ)) alpha xi =
      wooleyResidueGridSum qB k Q qH alpha xi := by
  simp [wooleyWeightedResidueGridSum, wooleyResidueGridSum]

theorem wooleyWeightedNormalizedResidueGridSum_one
    (qB k Q qH : ℕ) [NeZero qB]
    (alpha : Fin k → ZMod qB) (xi : ZMod qH) :
    wooleyWeightedNormalizedResidueGridSum
        qB k (fun _ : Fin Q => (1 : ℂ)) alpha xi =
      wooleyNormalizedResidueGridSum qB k Q qH alpha xi := by
  unfold wooleyWeightedNormalizedResidueGridSum
    wooleyNormalizedResidueGridSum
  rw [wooleyWeightedResidueMassSq_one,
    wooleyWeightedResidueGridSum_one]
  norm_cast

theorem wooleyWeightedConditionedGridMean_one
    {s k Q qB qH : ℕ} [NeZero qB] [NeZero qH] (hQ : 1 ≤ Q) :
    wooleyWeightedConditionedGridMean
        s k qB qH (fun _ : Fin Q => (1 : ℂ)) =
      wooleyConditionedGridMean s k Q qB qH := by
  unfold wooleyWeightedConditionedGridMean wooleyConditionedGridMean
    wooleyResidueRawMoment
  rw [wooleyWeightedMassSq_one]
  have hQne : (Q : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_eq_zero, show Q ≠ 0 by omega, ↓reduceIte]
  simp_rw [wooleyWeightedResidueMassSq_one,
    wooleyWeightedNormalizedResidueGridSum_one]
  apply congrArg ((Q : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro xi hxi
  ring

/-- The all-one weighted global mean is exactly Wooley's normalized
coefficient-one mean. -/
theorem wooleyWeightedGridMean_one
    {s k Q q : ℕ} [NeZero q] (hQ : 1 ≤ Q) :
    wooleyWeightedGridMean s k q (fun _ : Fin Q => (1 : ℂ)) =
      wooleyMonomialNormalizedGridMean s k Q q := by
  unfold wooleyWeightedGridMean wooleyWeightedNormalizedGridSum
    wooleyMonomialNormalizedGridMean wooleyMonomialRawGridMoment
  rw [wooleyWeightedMassSq_one]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hsqrt : Real.sqrt (Q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hQpos
  simp only [Nat.cast_eq_zero, show Q ≠ 0 by omega, ↓reduceIte,
    wooleyWeightedGridSum_one, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqrtPow : (Real.sqrt (Q : ℝ)) ^ (2 * s) = (Q : ℝ) ^ s := by
    rw [show 2 * s = 2 * s by rfl, pow_mul, Real.sq_sqrt hQpos.le]
  simp_rw [mul_pow, inv_pow, hsqrtPow]
  rw [← Finset.mul_sum]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqpow : (((q ^ k : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero k (NeZero.ne q))
  have hQpow : ((Q : ℝ) ^ s) ≠ 0 := pow_ne_zero _ hQpos.ne'
  field_simp
  norm_num
  ring

/-- The all-one source sequence is admissible. -/
  theorem wooleyBoxSourceSequence_one_admissible (Q : ℕ) :
    (wooleyBoxSourceSequence (fun _ : Fin Q => (1 : ℂ))).Admissible := by
  intro n
  unfold wooleyBoxSourceSequence
  rw [Finsupp.embDomain_apply]
  split_ifs <;> norm_num

#print axioms wooleyWeightedMassSq_one
#print axioms wooleyWeightedResidueMassSq_one
#print axioms wooleyWeightedGridSum_one
#print axioms wooleyWeightedResidueGridSum_one
#print axioms wooleyWeightedNormalizedResidueGridSum_one
#print axioms wooleyWeightedConditionedGridMean_one
#print axioms wooleyWeightedGridMean_one
#print axioms wooleyBoxSourceSequence_one_admissible

end

end GafniTao
