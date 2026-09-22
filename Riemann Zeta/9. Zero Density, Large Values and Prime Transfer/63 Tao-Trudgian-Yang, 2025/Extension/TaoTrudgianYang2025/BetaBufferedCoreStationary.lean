import TaoTrudgianYang2025.BetaBufferedCore
import TaoTrudgianYang2025.BetaBufferedStationary

/-!
# Stationary-frequency selection inside the actual physical core

The selected set is derived from the actual slope image. Its size is
controlled by T/N, independently of the much larger far-tail radius.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem modelPhaseCore_card_le
    {σ δ T N : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hT : 0 ≤ T) (hN : 0 < N) :
    ((Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)).card : ℝ) ≤
      3*(T/N)+3 := by
  have hAB := modelPhaseCoreLower_le_upper hσ hδ hT hN
  have hc := Int.card_Icc_of_le _ _ (show
    modelPhaseCoreLower σ δ T N ≤ modelPhaseCoreUpper δ T N+1 by omega)
  have he : ((Finset.Icc (modelPhaseCoreLower σ δ T N)
      (modelPhaseCoreUpper δ T N)).card : ℝ) =
        (modelPhaseCoreUpper δ T N : ℝ)+1-(modelPhaseCoreLower σ δ T N : ℝ) := by
    exact_mod_cast hc
  rw [he]
  have ha := Int.lt_floor_add_one ((T/N)*((2 : ℝ)^(-σ)-δ))
  have hb := Int.ceil_lt_add_one ((T/N)*(1+δ))
  have hs : 0 ≤ (2 : ℝ)^(-σ) := Real.rpow_nonneg (by norm_num) _
  have hTN : 0 ≤ T/N := div_nonneg hT hN.le
  have hlo : -(T/N) ≤ (T/N)*((2 : ℝ)^(-σ)-δ) := by
    have h := mul_le_mul_of_nonneg_left (show (-1 : ℝ) ≤ (2 : ℝ)^(-σ)-δ by linarith) hTN
    nlinarith
  have hhi : (T/N)*(1+δ) ≤ 2*(T/N) := by
    have h := mul_le_mul_of_nonneg_left (show 1+δ ≤ (2 : ℝ) by linarith) hTN
    nlinarith
  unfold modelPhaseCoreLower modelPhaseCoreUpper
  linarith

def modelPhaseCoreStationarySet (F : ℝ → ℝ) (σ δ T N : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)).filter
    (fun q => (q : ℝ)*N/T ∈ modelPhaseSlopeRange F)

theorem modelPhaseCoreStationarySet_mem {F : ℝ → ℝ} {σ δ T N : ℝ} {q : ℤ} :
    q ∈ modelPhaseCoreStationarySet F σ δ T N ↔
      q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N) ∧
        (q : ℝ)*N/T ∈ modelPhaseSlopeRange F := by
  classical
  exact Finset.mem_filter

theorem modelPhaseCoreStationarySet_card_le
    {F : ℝ → ℝ} {σ δ T N : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hT : 0 ≤ T) (hN : 0 < N) :
    ((modelPhaseCoreStationarySet F σ δ T N).card : ℝ) ≤ 3*(T/N)+3 := by
  have hs : modelPhaseCoreStationarySet F σ δ T N ⊆
      Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N) := by
    intro q hq
    exact (modelPhaseCoreStationarySet_mem.mp hq).1
  have hc : ((modelPhaseCoreStationarySet F σ δ T N).card : ℝ) ≤
      ((Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hs
  exact hc.trans (modelPhaseCore_card_le hσ hδ hδ₁ hT hN)

theorem modelPhaseBufferedCoreStationary_error
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
        0 < T → 0 < N →
        ‖∑ q ∈ modelPhaseCoreStationarySet F σ δ T N,
          (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
            (modelPhaseBufferedCutoff l r η (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
              modelPhaseStationaryMainTerm F T N q)‖ ≤
          C*(η⁻¹)^3*(1+N/T) := by
  obtain ⟨C,hC,hmode⟩ := modelPhaseBufferedFourierMode_stationary_uniform hσ
  refine ⟨3*C,by linarith,?_⟩
  intro l r η hl hr hη hη₁ F δ T N hδ hF hT hN
  have hb := modelPhaseCoreStationarySet_card_le (F := F) hσ.le
    (approximateModelPhase_tolerance_nonneg hF) (hδ.trans (min_le_right _ _)) hT.le hN
  calc
    _ ≤ ∑ q ∈ modelPhaseCoreStationarySet F σ δ T N, C*(η⁻¹)^3*N/T :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq =>
        hmode l r η hl hr hη hη₁ F δ T N q hδ hF hT hN
          (modelPhaseCoreStationarySet_mem.mp hq).2)
    _ = ((modelPhaseCoreStationarySet F σ δ T N).card : ℝ)*(C*(η⁻¹)^3*N/T) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (3*(T/N)+3)*(C*(η⁻¹)^3*N/T) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by field_simp

end TaoTrudgianYang2025
