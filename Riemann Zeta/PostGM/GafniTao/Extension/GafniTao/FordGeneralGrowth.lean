import GafniTao.FordQualitativeGlobalGrowth

/-!
# A parameterized Richert--Ford zeta-growth interface

The numerical Ford contract used elsewhere in the repository records the
optimized constants from the paper.  Gafni--Tao only needs the qualitative
shape of that estimate.  This module exposes that shape without weakening or
relabeling the numerical contract.
-/

open Complex

namespace GafniTao

noncomputable section

/-- A Richert-type zeta-growth estimate with visible coefficient `A` and
height exponent coefficient `B`. -/
def FordGeneralZetaGrowthBound (A B : ℝ) : Prop :=
  ∀ ⦃sigma t : ℝ⦄, 1 / 2 ≤ sigma → sigma ≤ 1 → 3 ≤ |t| →
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      A * |t| ^ (B * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log |t| ^ (2 / 3 : ℝ)

/-- The proved qualitative Ford theorem realizes the general interface. -/
theorem ford_qualitative_general_zeta_growth :
    FordGeneralZetaGrowthBound
      fordQualitativeGlobalCoefficient (fordSourceB 3000000) := by
  exact ford_qualitative_global_zeta_growth

theorem fordQualitativeGlobalCoefficient_pos :
    0 < fordQualitativeGlobalCoefficient := by
  unfold fordQualitativeGlobalCoefficient
  linarith [fordQualitativeZetaCoefficient_nonneg]

theorem fordSourceB_three_million_pos :
    0 < fordSourceB 3000000 :=
  lt_of_lt_of_le (by norm_num) four_le_fordSourceB_three_million

#print axioms ford_qualitative_general_zeta_growth

end

end GafniTao
