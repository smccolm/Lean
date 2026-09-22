import TaoTrudgianYang2025.BetaBufferedTransitionBands
import TaoTrudgianYang2025.BetaEndpointCore

/-!
# Sharp replacement of the whole physical core by interior main terms

The actual transition bands use curvature, the deep interior uses the
logarithmic stationary error, and the remaining support-exterior modes
use reciprocal slope gaps. No inverse cutoff-width power remains.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem modelPhaseBufferedSupport_inside_core
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hflat : l+4*η < r) :
    modelPhaseCoreLower σ δ T N ≤ modelPhaseBufferedSupportLower F r η T N ∧
      modelPhaseBufferedSupportUpper F l η T N ≤ modelPhaseCoreUpper δ T N := by
  have he := modelPhaseEndpoints_inside_core hF hT.le hN
  have ha : l+η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hb : r-η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hL := mul_le_mul_of_nonneg_left
    (modelPhaseClosedSlope_deriv_bounds hσ hδ hF hb).1 (div_pos hT hN).le
  have hU := mul_le_mul_of_nonneg_left
    (modelPhaseClosedSlope_deriv_bounds hσ hδ hF ha).2 (div_pos hT hN).le
  exact ⟨he.1.trans (Int.floor_mono hL),(Int.ceil_mono hU).trans he.2⟩

theorem modelPhaseBufferedTransition_error {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < T → 0 < N →
        ‖∑ q ∈ (Finset.Icc (modelPhaseBufferedSupportLower F r η T N)
            (modelPhaseBufferedSupportUpper F l η T N)) \
          (Finset.Ioo (modelPhaseBufferedPlateauLower F r η T N)
            (modelPhaseBufferedPlateauUpper F l η T N)),
          modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
          (2*(T/N)*(σ+1)*η+6)*C*N/Real.sqrt T := by
  obtain ⟨C,hC,hmode⟩ := modelPhaseBufferedFourierMode_uniform_curvature hσ
  refine ⟨C,hC,?_⟩
  intro l r η hl hr hη hflat F δ T N hδ hF hT hN
  have hc := modelPhaseBufferedTransition_card_le hσ hδ hF hT hN hη hl hr hflat
  calc
    _ ≤ ∑ _q ∈ (Finset.Icc (modelPhaseBufferedSupportLower F r η T N)
          (modelPhaseBufferedSupportUpper F l η T N)) \
        (Finset.Ioo (modelPhaseBufferedPlateauLower F r η T N)
          (modelPhaseBufferedPlateauUpper F l η T N)), C*N/Real.sqrt T :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ =>
        hmode l r η hl hr hη F δ T N q hδ hF hT hN)
    _ ≤ _ := by
      rw [Finset.sum_const,nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (by ring)

theorem modelPhaseBufferedSupportCore_error {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ → 0 < T → 0 < N →
        let L := modelPhaseBufferedSupportLower F r η T N
        let U := modelPhaseBufferedSupportUpper F l η T N
        let A := modelPhaseBufferedPlateauLower F r η T N
        let B := modelPhaseBufferedPlateauUpper F l η T N
        ‖(∑ q ∈ Finset.Icc L U, modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q)-
          (∑ q ∈ Finset.Ioo A B, modelPhaseStationaryMainTerm F T N q)‖ ≤
          C*(1+Real.log ((B-A-1).toNat : ℝ))+
            (2*(T/N)*(σ+1)*η+6)*D*N/Real.sqrt T := by
  obtain ⟨C,hC,hinterior⟩ := modelPhaseBufferedInteriorBlock_error hσ
  obtain ⟨D,hD,htransition⟩ := modelPhaseBufferedTransition_error hσ
  refine ⟨C,hC,D,hD,?_⟩
  intro l r η hl hr hη hflat F δ T N hδ hF hT hN L U A B
  have hF₁ := approximateModelPhase_mono hF bufferedLocalStationaryOrder_pos le_rfl
  have he := modelPhaseBufferedBand_endpoints hσ hδ hF₁ hT hN hη hl hr hflat
  have hLA : L ≤ A := he.1
  have hBU : B ≤ U := he.2.2.2
  have hs : Finset.Ioo A B ⊆ Finset.Icc L U := by
    intro q hq
    simp only [Finset.mem_Ioo,Finset.mem_Icc] at hq ⊢
    omega
  let f : ℤ → ℂ := fun q => modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q
  let main : ℤ → ℂ := fun q => modelPhaseStationaryMainTerm F T N q
  have hsplit : (∑ q ∈ Finset.Icc L U, f q)-(∑ q ∈ Finset.Ioo A B, main q) =
      (∑ q ∈ Finset.Ioo A B, (f q-main q))+
        ∑ q ∈ (Finset.Icc L U) \ (Finset.Ioo A B), f q := by
    rw [← Finset.sum_sdiff hs (f := f),Finset.sum_sub_distrib]
    abel
  have hi := hinterior l r η hl hr hη hflat F δ T N A B hδ hF hT hN
    (Int.le_ceil _) (Int.floor_le _)
  have ht := htransition l r η hl hr hη hflat F δ T N hδ hF₁ hT hN
  change ‖(∑ q ∈ Finset.Icc L U, f q)-(∑ q ∈ Finset.Ioo A B, main q)‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hi ht)

theorem modelPhaseBufferedSharpCore_error {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ → 0 < T → 0 < N →
        let A := modelPhaseCoreLower σ δ T N
        let B := modelPhaseCoreUpper δ T N
        let L := modelPhaseBufferedSupportLower F r η T N
        let U := modelPhaseBufferedSupportUpper F l η T N
        let P := modelPhaseBufferedPlateauLower F r η T N
        let Q := modelPhaseBufferedPlateauUpper F l η T N
        ‖(∑ q ∈ Finset.Icc A B, modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q)-
          (∑ q ∈ Finset.Ioo P Q, modelPhaseStationaryMainTerm F T N q)‖ ≤
          C*(1+Real.log ((Q-P-1).toNat : ℝ))+
            (2*(T/N)*(σ+1)*η+6)*D*N/Real.sqrt T+
            (4/Real.pi)*(2+Real.log ((L-A).toNat : ℝ)+Real.log ((B-U).toNat : ℝ)) := by
  obtain ⟨C,hC,D,hD,hcore⟩ := modelPhaseBufferedSupportCore_error hσ
  refine ⟨C,hC,D,hD,?_⟩
  intro l r η hl hr hη hflat F δ T N hδ hF hT hN A B L U P Q
  have hF₁ := approximateModelPhase_mono hF bufferedLocalStationaryOrder_pos le_rfl
  have hi := modelPhaseBufferedSupport_inside_core hσ hδ hF₁ hT hN hη hl hr hflat
  have he := modelPhaseBufferedBand_endpoints hσ hδ hF₁ hT hN hη hl hr hflat
  have hAL : A ≤ L := hi.1
  have hUB : U ≤ B := hi.2
  have hLU : L ≤ U := he.1.trans he.2.1
  let f : ℤ → ℂ := fun q => modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q
  let main := ∑ q ∈ Finset.Ioo P Q, modelPhaseStationaryMainTerm F T N q
  have hsplit := sum_int_interval_three_parts f hAL hLU hUB
  have heq : (∑ q ∈ Finset.Icc A B, f q)-main =
      ((∑ q ∈ Finset.Icc L U, f q)-main)+
        ((∑ q ∈ Finset.Ico A L, f q)+(∑ q ∈ Finset.Ioc U B, f q)) := by
    rw [hsplit]
    abel
  have hext : ‖(∑ q ∈ Finset.Ico A L, f q)+(∑ q ∈ Finset.Ioc U B, f q)‖ ≤
      (4/Real.pi)*(2+Real.log ((L-A).toNat : ℝ)+Real.log ((B-U).toNat : ℝ)) := by
    rw [sum_int_Ico_eq_reverse_range f hAL,sum_int_Ioc_eq_forward_range f hUB]
    simpa only [f,L,U,modelPhaseBufferedSupportLower,modelPhaseBufferedSupportUpper,
      Int.cast_sub,Int.cast_add,Int.cast_natCast] using
      (norm_bufferedModes_support_blocks_le_log hσ hδ hF₁ hT hN hη hl hr
        (by linarith : l+2*η ≤ r) (L-A).toNat (B-U).toNat)
  have hc := hcore l r η hl hr hη hflat F δ T N hδ hF hT hN
  change ‖(∑ q ∈ Finset.Icc A B, f q)-main‖ ≤ _
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hc hext)

end TaoTrudgianYang2025
