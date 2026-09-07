import GafniTao.FordExplicitData.PositiveIntegralFormulaCoefficients

/-!
# Source identification of Ford's positive-side exact certificate

This module closes the source-to-data bridge for the positive compact integral.
The coefficient formula is derived from the lifted cubic phase in
`FordPositiveIntegralFormula`; the rational polynomial on the right is generated
independently.  Equality is checked coefficientwise in degrees `0` through `66`,
with a proved common zero tail.
-/

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

theorem fordPositiveIntegralPolynomialFormula_eq_explicit :
    fordPositiveIntegralPolynomialFormula fordPositiveTaylorPower11 =
      fordPositiveAtThreeHalvesExplicit := by
  apply Polynomial.ext
  intro n
  by_cases hn : n < 67
  · interval_cases n <;> simp
  · have hn' : 67 ≤ n := by omega
    have hleft :
        (fordPositiveIntegralPolynomialFormula
          fordPositiveTaylorPower11).coeff n = 0 := by
      rw [fordPositiveIntegralPolynomialFormula_coeff]
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : k < 67 := Finset.mem_range.mp hk
      rw [if_neg]
      omega
    have hright : fordPositiveAtThreeHalvesExplicit.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hdegree : fordPositiveAtThreeHalvesExplicit.natDegree ≤ 66 := by
        unfold fordPositiveAtThreeHalvesExplicit
        unfold fordPositiveAtThreeHalvesValueBlock0
          fordPositiveAtThreeHalvesValueBlock1
          fordPositiveAtThreeHalvesValueBlock2
          fordPositiveAtThreeHalvesValueBlock3
          fordPositiveAtThreeHalvesValueBlock4
          fordPositiveAtThreeHalvesValueBlock5
        compute_degree
      omega
    rw [hleft, hright]

theorem fordPositiveIntegralFormula_eq_explicit :
    fordPositiveIntegralFormula fordPositiveTaylorPower11 =
      fordPositiveAtThreeHalvesExplicit := by
  rw [fordPositiveIntegralFormula_eq_polynomialFormula,
    fordPositiveIntegralPolynomialFormula_eq_explicit]

theorem fordPositiveIntegral_source_eq_explicit :
    fordBiEvalV
        (fordBiIntegralPolynomial fordPositiveUpperPolynomial) (3 / 2) =
      fordPositiveAtThreeHalvesExplicit := by
  rw [fordPositiveIntegral_source_eq_formula,
    fordPositiveIntegralFormula_eq_explicit]

end

end GafniTao
