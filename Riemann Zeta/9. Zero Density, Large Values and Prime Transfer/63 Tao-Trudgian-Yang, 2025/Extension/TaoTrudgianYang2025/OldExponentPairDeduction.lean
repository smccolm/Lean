import TaoTrudgianYang2025.ExponentPairAProcess
import TaoTrudgianYang2025.ExponentPairBProcess
import TaoTrudgianYang2025.ZetaGrowthBridge
import TaoTrudgianYang2025.HeathBrownDensityRange

/-!
# The printed old-pair deduction from Watt's analytic exponent pair

The A/B transformations and both convex combinations are proved consumers.
Watt's 1989 analytic exponent-pair theorem is an explicit upstream
hypothesis, not established by this module. The growth and density
corollaries consequently remain conditional on that one analytic input.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem ExponentPair.old_pair_of_watt
    (hW : ExponentPair (89/560) (369/560)) :
    ExponentPair (3/40) (31/40) := by
  have hA := hW.aProcess
  have hABA := hA.bProcess.aProcess
  have hmix := hABA.convexCombination hA
    (by norm_num : (0 : ℝ) ≤ 37081/40415)
    (by norm_num : (37081/40415 : ℝ) ≤ 1)
  have hfinal := hW.convexCombination hmix
    (by norm_num : (0 : ℝ) ≤ 476897/493711)
    (by norm_num : (476897/493711 : ℝ) ≤ 1)
  norm_num at hfinal
  exact hfinal

theorem ExponentPair.old_growth_bound_of_watt
    (hW : ExponentPair (89/560) (369/560)) :
    IsZetaGrowthBound (7/10) (3/40) := by
  have h := hW.old_pair_of_watt.isZetaGrowthBound
  norm_num at h
  exact h

theorem ExponentPair.old_growth_exponent_of_watt
    (hW : ExponentPair (89/560) (369/560)) :
    zetaGrowthExponent (7/10) ≤ ((3/40 : ℝ) : EReal) :=
  zetaGrowthExponent_le_of_bound hW.old_growth_bound_of_watt

theorem ExponentPair.heathBrown_density_of_watt
    (hW : ExponentPair (89/560) (369/560)) {σ : ℝ}
    (hσ : 7/10 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((3/(10*σ-7) : ℝ) : EReal) :=
  hW.old_pair_of_watt.heathBrown_density_of_old_pair hσ hσ1

end TaoTrudgianYang2025
