import TaoTrudgianYang2025.SargosPhaseCorrection
import TaoTrudgianYang2025.SargosModelSmoothReduction

/-! The actual constructed remainder produces a closed approximate transformed model. -/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosTransformedTime (σ : ℝ) (M : ℕ) (τ T : ℝ) : ℝ :=
  τ*T*modelPhaseJetCoefficient σ 4/(M:ℝ)^4

def sargosTransformedModel {H : ℕ} (F : ℝ → ℝ) (σ : ℝ) (M Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (τ T u : ℝ) : ℝ :=
  sargosFourthDerivativeModel F σ u+
    sargosPhysicalCorrection
      (sargosPhysicalExtendedRemainder (heathBrownPhysicalPhase F T M M 1) M Q q)
      M (sargosTransformedTime σ M τ T) u

theorem sargosTransformedTime_pos {σ τ T : ℝ} {M : ℕ}
    (hσ : 0 < σ) (hM : 1 ≤ M) (hτ : 0 < τ) (hT : 0 < T) :
    0 < sargosTransformedTime σ M τ T := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hD := modelPhaseJetCoefficient_pos hσ 4
  unfold sargosTransformedTime
  positivity

theorem sargosTransformedModel_approximate (σ : ℝ) (hσ : 0 < σ) (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (F : ℝ → ℝ) (δ τ T : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ H → H ≤ M → δ ≤ 1 → 0 < τ → 0 < T →
      IsApproximateModelPhaseFunction F σ (P+7) δ →
      IsApproximateModelPhaseFunction (sargosTransformedModel F σ M (P+1) q τ T)
        (σ+4) P ((δ+C*(H:ℝ)^6/(τ*(M:ℝ)^2))/modelPhaseJetCoefficient σ 4) := by
  obtain ⟨C,hC,hsource⟩ := sargos_model_smooth_reduction σ hσ.le (P+1) 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro H M F δ τ T q hH hHM hδ hτ hT hF
  have hM : 1 ≤ M := hH.trans hHM
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hD : 0 < modelPhaseJetCoefficient σ 4 := modelPhaseJetCoefficient_pos hσ 4
  have ht := sargosTransformedTime_pos hσ hM hτ hT
  have hsrc := hsource H M (P+7) F δ T M M hH hHM (by omega) hδ
    hM0 le_rfl (by linarith) hF
  obtain ⟨hu,_he,hjets⟩ := hsrc.1 q
  have hb : ∀ x ∈ Icc (0:ℝ) M, ∀ j ≤ P+1,
      |iteratedDeriv j (sargosPhysicalExtendedRemainder
        (heathBrownPhysicalPhase F T M M 1) M (P+1) q) x| ≤
          (C*T*(H:ℝ)^6/(60*(M:ℝ)^6))/(M:ℝ)^j := by
    intro x hx j hj
    have h := hjets x hx j hj
    rw [abs_of_pos hT] at h
    convert h using 1
    ring
  have hcor : ∀ u ∈ phaseInterval, ∀ p ≤ P,
      |iteratedDeriv (p+1)
        (sargosPhysicalCorrection
          (sargosPhysicalExtendedRemainder (heathBrownPhysicalPhase F T M M 1) M (P+1) q)
          M (sargosTransformedTime σ M τ T)) u| ≤
        C*(H:ℝ)^6/(τ*(M:ℝ)^2*modelPhaseJetCoefficient σ 4) := by
    intro u hu' p hp
    have hc := sargosPhysicalCorrection_uniform_jets hu hM0 ht hb hu' (by omega : p+1 ≤ P+1)
    have heq : (C*T*(H:ℝ)^6/(60*(M:ℝ)^6))/sargosTransformedTime σ M τ T =
        (C*(H:ℝ)^6/(τ*(M:ℝ)^2*modelPhaseJetCoefficient σ 4))/60 := by
      unfold sargosTransformedTime
      field_simp
    rw [heq] at hc
    exact hc.trans (by
      have hn : 0 ≤ C*(H:ℝ)^6/(τ*(M:ℝ)^2*modelPhaseJetCoefficient σ 4) := by positivity
      linarith)
  have hmain := sargosFourthDerivativeModel_approximate hσ
    (approximateModelPhase_mono hF (by omega : P+4 ≤ P+7) le_rfl)
  have hfinal := sargos_approximateModel_add_correction hmain
    (sargosPhysicalCorrection_contDiff hu _ _) hcor
  convert hfinal using 1
  ring

end TaoTrudgianYang2025
