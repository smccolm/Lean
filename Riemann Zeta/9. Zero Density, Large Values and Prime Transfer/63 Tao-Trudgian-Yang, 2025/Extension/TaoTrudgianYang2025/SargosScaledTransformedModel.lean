import TaoTrudgianYang2025.SargosScaledModelRemainder
import TaoTrudgianYang2025.SargosAffinePhaseCorrection

/-! The actual transformed model for arbitrary admissible real-scale source windows. -/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosScaledTransformedTime (σ N τ T : ℝ) : ℝ :=
  τ*T*modelPhaseJetCoefficient σ 4/N^4

def sargosScaledTransformedModel {H : ℕ} (F : ℝ → ℝ) (σ : ℝ) (M : ℕ)
    (N A : ℝ) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (τ T u : ℝ) : ℝ :=
  sargosFourthDerivativeModel F σ u+
    sargosAffinePhysicalCorrection
      (sargosScaledPhysicalRemainder (heathBrownPhysicalPhase F T N A 1) M N Q q)
      N A (sargosScaledTransformedTime σ N τ T) u

theorem sargosScaledTransformedTime_pos {σ N τ T : ℝ}
    (hσ : 0 < σ) (hN : 0 < N) (hτ : 0 < τ) (hT : 0 < T) :
    0 < sargosScaledTransformedTime σ N τ T := by
  have hD := modelPhaseJetCoefficient_pos hσ 4
  unfold sargosScaledTransformedTime
  positivity

theorem sargosScaledTransformedModel_approximate (σ : ℝ) (hσ : 0 < σ) (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (F : ℝ → ℝ) (δ N A τ T : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ M → δ ≤ 1 → 0 < N → N ≤ A → A+(M:ℝ) ≤ 2*N → 0 < τ → 0 < T →
      IsApproximateModelPhaseFunction F σ (P+7) δ →
      IsApproximateModelPhaseFunction (sargosScaledTransformedModel F σ M N A (P+1) q τ T)
        (σ+4) P ((δ+C*(H:ℝ)^6/(τ*N^2))/modelPhaseJetCoefficient σ 4) := by
  obtain ⟨C,hC,hsource⟩ := sargosScaledModelRemainder_uniform σ hσ.le (P+1)
  refine ⟨C,hC,?_⟩
  intro H M F δ N A τ T q hM hδ hN ha hb hτ hT hF
  have hD : 0 < modelPhaseJetCoefficient σ 4 := modelPhaseJetCoefficient_pos hσ 4
  have ht := sargosScaledTransformedTime_pos hσ hN hτ hT
  have hA : A ≤ 2*N := by
    have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
    linarith
  obtain ⟨hu,_he,hjets⟩ := hsource H M (P+7) F δ T N A q hM (by omega) hδ hN ha hb hF
  have hj : ∀ x ∈ Icc (-N) N, ∀ j ≤ P+1,
      |iteratedDeriv j (sargosScaledPhysicalRemainder
        (heathBrownPhysicalPhase F T N A 1) M N (P+1) q) x| ≤
          (C*T*(H:ℝ)^6/(60*N^6))/N^j := by
    intro x hx j hj
    have h := hjets x hx j hj
    rw [abs_of_pos hT] at h
    convert h using 1
    ring
  have hcor : ∀ u ∈ phaseInterval, ∀ p ≤ P,
      |iteratedDeriv (p+1)
        (sargosAffinePhysicalCorrection
          (sargosScaledPhysicalRemainder (heathBrownPhysicalPhase F T N A 1) M N (P+1) q)
          N A (sargosScaledTransformedTime σ N τ T)) u| ≤
        C*(H:ℝ)^6/(τ*N^2*modelPhaseJetCoefficient σ 4) := by
    intro u hu' p hp
    have hc := sargosAffinePhysicalCorrection_uniform_jets hu hN ht ha hA hj hu'
      (by omega : p+1 ≤ P+1)
    have heq : (C*T*(H:ℝ)^6/(60*N^6))/sargosScaledTransformedTime σ N τ T =
        (C*(H:ℝ)^6/(τ*N^2*modelPhaseJetCoefficient σ 4))/60 := by
      unfold sargosScaledTransformedTime
      field_simp
    rw [heq] at hc
    exact hc.trans (by
      have hn : 0 ≤ C*(H:ℝ)^6/(τ*N^2*modelPhaseJetCoefficient σ 4) := by positivity
      linarith)
  have hmain := sargosFourthDerivativeModel_approximate hσ
    (approximateModelPhase_mono hF (by omega : P+4 ≤ P+7) le_rfl)
  have hfinal := sargos_approximateModel_add_correction hmain
    (sargosAffinePhysicalCorrection_contDiff hu _ _ _) hcor
  convert hfinal using 1
  ring

end TaoTrudgianYang2025
