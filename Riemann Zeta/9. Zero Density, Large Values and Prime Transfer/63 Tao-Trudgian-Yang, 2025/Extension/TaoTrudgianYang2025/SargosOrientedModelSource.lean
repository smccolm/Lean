import TaoTrudgianYang2025.SargosSextupleOrientation
import TaoTrudgianYang2025.SargosScaledTransformedSource

/-! Every actual nonzero quartic difference has a positive-time transformed model, with exact norm entry. -/

noncomputable section

open Set Expdb GafniTao
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem sargos_scaled_oriented_sextuple_model (σ : ℝ) (hσ : 0 < σ) (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (F : ℝ → ℝ) (δ N A T : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ M → δ ≤ 1 → 0 < N → N ≤ A → A+(M:ℝ) ≤ 2*N →
      0 < T → sargosQuarticDifference q ≠ 0 →
      IsApproximateModelPhaseFunction F σ (P+7) δ →
      let τ : ℝ := (|sargosQuarticDifference q|:ℝ)/12
      IsApproximateModelPhaseFunction
        (sargosScaledTransformedModel F σ M N A (P+1) (sargosOrientedSextuple q) τ T)
        (σ+4) P ((δ+C*(H:ℝ)^6/(τ*N^2))/modelPhaseJetCoefficient σ 4) ∧
      ‖∑ m ∈ sargosSextupleInterior M q,
        fordAdditiveCharacter (sargosSextuplePhase (heathBrownPhysicalPhase F T N A 1) q m)‖ =
        ‖∑ m ∈ sargosSextupleInterior M q,
          fordAdditiveCharacter
            (sargosScaledTransformedTime σ N τ T*
              sargosScaledTransformedModel F σ M N A (P+1) (sargosOrientedSextuple q) τ T
                ((A+m)/N))‖ := by
  obtain ⟨C,hC,hmodel⟩ := sargos_scaled_positive_sextuple_model σ hσ P
  refine ⟨C,hC,?_⟩
  intro H M F δ N A T q hM hδ hN ha hb hT hq hF τ
  have ho : 0 < sargosQuarticDifference (sargosOrientedSextuple q) := by
    rw [sargosQuarticDifference_oriented]
    exact abs_pos.mpr hq
  have hh := hmodel H M F δ N A T (sargosOrientedSextuple q) hM hδ hN ha hb hT ho hF
  dsimp only at hh
  rw [sargosQuarticDifference_oriented] at hh
  simp only [Int.cast_abs] at hh
  refine ⟨hh.1,?_⟩
  have he := congrArg (fun z : ℂ => ‖z‖) hh.2
  dsimp only at he
  rw [sargos_sextuple_sum_norm_oriented,sargosSextupleInterior_oriented] at he
  exact he

end TaoTrudgianYang2025
