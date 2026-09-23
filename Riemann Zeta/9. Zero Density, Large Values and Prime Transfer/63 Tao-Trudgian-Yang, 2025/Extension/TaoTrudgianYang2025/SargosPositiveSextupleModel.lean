import TaoTrudgianYang2025.SargosTransformedSource

/-! The positive quartic-difference branch carries the actual source phase and time scale together. -/

noncomputable section

open Set Expdb GafniTao
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticDifference {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℤ :=
  sargosInitialTuplePower 4 q.1-sargosInitialTuplePower 4 q.2

theorem sargos_positive_sextuple_model (σ : ℝ) (hσ : 0 < σ) (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (F : ℝ → ℝ) (δ T : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ H → H ≤ M → δ ≤ 1 → 0 < T → 0 < sargosQuarticDifference q →
      IsApproximateModelPhaseFunction F σ (P+7) δ →
      let τ : ℝ := (sargosQuarticDifference q:ℝ)/12
      IsApproximateModelPhaseFunction (sargosTransformedModel F σ M (P+1) q τ T)
        (σ+4) P ((δ+C*(H:ℝ)^6/(τ*(M:ℝ)^2))/modelPhaseJetCoefficient σ 4) ∧
      (∑ m ∈ sargosSextupleInterior M q,
        fordAdditiveCharacter (sargosSextuplePhase (heathBrownPhysicalPhase F T M M 1) q m)) =
        ∑ m ∈ sargosSextupleInterior M q,
          fordAdditiveCharacter
            (sargosTransformedTime σ M τ T*sargosTransformedModel F σ M (P+1) q τ T
              (1+(m:ℝ)/M)) := by
  obtain ⟨C,hC,hmodel⟩ := sargosTransformedModel_approximate σ hσ P
  refine ⟨C,hC,?_⟩
  intro H M F δ T q hH hHM hδ hT hq hF τ
  have hτ : 0 < τ := by
    have hp : (0:ℝ) < sargosQuarticDifference q := by exact_mod_cast hq
    exact div_pos hp (by norm_num)
  exact ⟨hmodel H M F δ τ T q hH hHM hδ hτ hT hF,
    sargosTransformedModel_source_sum hF.1 hσ (hH.trans hHM) hτ hT (P+1) q rfl⟩

theorem sargos_remainder_error_large_frequency {H M : ℕ} {τ η : ℝ}
    (hM : 1 ≤ M) (hτ : 0 < τ)
    (hlarge : (H:ℝ)^3 ≤ τ) (hsmall : (H:ℝ)^3/(M:ℝ)^2 ≤ η) :
    (H:ℝ)^6/(τ*(M:ℝ)^2) ≤ η := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hpow : (H:ℝ)^6 = (H:ℝ)^3*(H:ℝ)^3 := by ring
  apply (div_le_iff₀ (mul_pos hτ (pow_pos hM0 2))).mpr
  have hsmall' := (div_le_iff₀ (pow_pos hM0 2)).mp hsmall
  rw [hpow]
  calc
    _ ≤ τ*((H:ℝ)^3) := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ ≤ τ*(η*(M:ℝ)^2) := mul_le_mul_of_nonneg_left hsmall' hτ.le
    _ = _ := by ring

end TaoTrudgianYang2025
