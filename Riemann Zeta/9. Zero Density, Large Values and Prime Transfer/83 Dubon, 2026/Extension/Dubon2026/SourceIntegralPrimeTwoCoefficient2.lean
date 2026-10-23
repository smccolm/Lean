import Dubon2026.SourcePrimeTwoExplicitCoefficients
import Dubon2026.SourceIntegralJFiniteCoefficientTest

/-! Exact coefficient comparisons between the actual integral prime-two
minimal polynomial and the explicit cubic. The finite test uses the proved
degree-three bound and kernel-checked Laurent coefficients. No modular
polynomial symmetry, coefficient table or quotient interpretation is assumed.
This discharges the explicit-polynomial bridge for the degree-two cyclic
quotient root interpretation, required on the DUB-17 / DUB-18 inertia and
good-reduction dependency chain. -/
namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
noncomputable section
open Polynomial PhiTwoCalc
open Dubon2026.SourcePrimeTwoPolynomial

theorem modularPolynomial_two_coeff_2_eq :
    (modularPolynomial 2).coeff 2 = phiTwoC2 := by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero _ 3
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (modularPolynomial_two_coeff_natDegree_le 2) natDegree_phiTwoC.2.2)
  · intro m hm₁ hm₂
    rw [map_sub, HahnSeries.coeff_sub, coeff_eq_coeff_qExpand_two,
      coeff_eq_coeff_qExpand_two (evalAtJ _), sub_eq_zero,
      modularPolynomial_two_coefficient_identities.1, qExpand_evalAtJ_phiTwoC.1]
    interval_cases m
    · simp only [Int.reduceMul, HahnSeries.coeff_neg, HahnSeries.coeff_add,
        HahnSeries.coeff_sub, coeff_C_mul', coeff_C']
      rw [nf_qExpand_four_jq.coeff (-6) (by decide), nf_jq.coeff (-6) (by decide), nf_qTwist_neg_one_jq.coeff (-6) (by decide), nf_J22.coeff (-6) (by decide), nf_qExpand_two_jq.coeff (-6) (by decide)]
      norm_num [LA, LJ, LC, L2, Int.toNat]
    · simp only [Int.reduceMul, HahnSeries.coeff_neg, HahnSeries.coeff_add,
        HahnSeries.coeff_sub, coeff_C_mul', coeff_C']
      rw [nf_qExpand_four_jq.coeff (-4) (by decide), nf_jq.coeff (-4) (by decide), nf_qTwist_neg_one_jq.coeff (-4) (by decide), nf_J22.coeff (-4) (by decide), nf_qExpand_two_jq.coeff (-4) (by decide)]
      norm_num [LA, LJ, LC, L2, Int.toNat]
    · simp only [Int.reduceMul, HahnSeries.coeff_neg, HahnSeries.coeff_add,
        HahnSeries.coeff_sub, coeff_C_mul', coeff_C']
      rw [nf_qExpand_four_jq.coeff (-2) (by decide), nf_jq.coeff (-2) (by decide), nf_qTwist_neg_one_jq.coeff (-2) (by decide), nf_J22.coeff (-2) (by decide), nf_qExpand_two_jq.coeff (-2) (by decide)]
      norm_num [LA, LJ, LC, L2, Int.toNat]
    · simp only [Int.reduceMul, HahnSeries.coeff_neg, HahnSeries.coeff_add,
        HahnSeries.coeff_sub, coeff_C_mul', coeff_C']
      rw [nf_qExpand_four_jq.coeff (0) (by decide), nf_jq.coeff (0) (by decide), nf_qTwist_neg_one_jq.coeff (0) (by decide), nf_J22.coeff (0) (by decide), nf_qExpand_two_jq.coeff (0) (by decide)]
      norm_num [LA, LJ, LC, L2, Int.toNat]

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
