import TaoTrudgianYang2025.HeathBrownBetaDeduction
import GafniTao.WooleyNative

/-!
# Heath--Brown's source beta bound from native Vinogradov mean values

The kth-derivative input is supplied by the proved Wooley/Heath--Brown
dependency, not a theorem parameter. The public beta theorem displays
the exact formula in the Tao--Trudgian--Yang source.
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem source_exponentialSum_heathBrown_bound
    {k : ℕ} (hk : 3 ≤ k) {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ),
        0 < T → 1 ≤ N → N ≤ (a : ℝ) → ((a+L : ℕ) : ℝ) ≤ 2*N →
        IsApproximateModelPhaseFunction F σ P δ →
        ‖exponentialSumAt F T N a (a+L)‖ ≤ K*heathBrownPowerMajorant k η T N :=
  source_exponentialSum_heathBrown_bound_of_derivative
    GafniTao.heathBrownKthDerivativeTheorem_native hk hσ hη

theorem isExponentSumBoundNonAsymptotic_heathBrown
    {k : ℕ} (hk : 3 ≤ k) {α : ℝ≥0} (hα : 0 < (α : ℝ)) :
    IsExponentSumBoundNonAsymptotic α (heathBrownBetaBound k α) :=
  isExponentSumBoundNonAsymptotic_heathBrown_of_derivative
    GafniTao.heathBrownKthDerivativeTheorem_native hk hα

theorem exponentSumGrowthExponent_le_heathBrown
    {k : ℕ} (hk : 3 ≤ k) {α : ℝ≥0} (hα : 0 < (α : ℝ)) :
    exponentSumGrowthExponent α ≤
      (α : ℝ) + max ((1-(k : ℝ)*(α : ℝ))/((k : ℝ)*(k-1)))
        (max (-(α : ℝ)/((k : ℝ)*(k-1)))
          (-2*(α : ℝ)/((k : ℝ)*(k-1))-
            2*(1-(k : ℝ)*(α : ℝ))/((k : ℝ)^2*(k-1)))) :=
  exponentSumGrowthExponent_le_heathBrown_of_derivative
    GafniTao.heathBrownKthDerivativeTheorem_native hk hα

end TaoTrudgianYang2025
