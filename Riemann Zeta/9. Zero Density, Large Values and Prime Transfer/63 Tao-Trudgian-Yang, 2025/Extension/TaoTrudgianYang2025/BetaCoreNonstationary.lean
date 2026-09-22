import TaoTrudgianYang2025.BetaEndpointCore
import TaoTrudgianYang2025.BetaEndpointNonstationary
import TaoTrudgianYang2025.BetaBufferedCurvature

/-!
# Bounding the actual nonstationary complement of the core

The two nearest endpoint frequencies use the uniform curvature estimate.
Every other frequency uses the genuine endpoint gap and a harmonic sum.
No unevaluated complement, artificial endpoint gap, or width loss remains.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem modelPhaseBufferedCoreNonstationary_error {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < T → 0 < N →
        let A := modelPhaseCoreLower σ δ T N
        let B := modelPhaseCoreUpper δ T N
        let L := modelPhaseEndpointLower F T N
        let U := modelPhaseEndpointUpper F T N
        ‖∑ q ∈ (Finset.Icc A B) \ modelPhaseCoreStationarySet F σ δ T N,
          modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
            2*C*N/Real.sqrt T+
              (4/Real.pi)*(2+Real.log ((L-A).toNat : ℝ)+Real.log ((B-U).toNat : ℝ)) := by
  obtain ⟨C,hC,hmode⟩ := modelPhaseBufferedFourierMode_uniform_curvature hσ
  refine ⟨C,hC,?_⟩
  intro l r η hl hr hη F δ T N hδ hF hT hN A B L U
  let f : ℤ → ℂ := fun q => modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q
  have hb := modelPhaseEndpoints_inside_core hF hT.le hN
  have hAL : A ≤ L := hb.1
  have hUB : U ≤ B := hb.2
  have hleft : (∑ q ∈ Finset.Icc A L, f q) =
      (∑ q ∈ Finset.Ico A L, f q)+f L := by
    simpa only [Finset.Icc_self,Finset.sum_singleton,Finset.Ioc_self,
      Finset.sum_empty,add_zero] using
      (sum_int_interval_three_parts f hAL (le_refl L) (le_refl L))
  have hright : (∑ q ∈ Finset.Icc U B, f q) =
      f U+(∑ q ∈ Finset.Ioc U B, f q) := by
    simpa only [Finset.Ico_self,Finset.sum_empty,Finset.Icc_self,
      Finset.sum_singleton,zero_add] using
      (sum_int_interval_three_parts f (le_refl U) (le_refl U) hUB)
  have he : (∑ q ∈ (Finset.Icc A B) \ modelPhaseCoreStationarySet F σ δ T N, f q) =
      ((∑ q ∈ Finset.Ico A L, f q)+(∑ q ∈ Finset.Ioc U B, f q))+(f L+f U) := by
    rw [modelPhaseCore_nonstationary_sum hσ hδ hF hT hN f,hleft,hright]
    abel
  have hext : ‖(∑ q ∈ Finset.Ico A L, f q)+(∑ q ∈ Finset.Ioc U B, f q)‖ ≤
      (4/Real.pi)*(2+Real.log ((L-A).toNat : ℝ)+Real.log ((B-U).toNat : ℝ)) := by
    rw [sum_int_Ico_eq_reverse_range f hAL,sum_int_Ioc_eq_forward_range f hUB]
    simpa only [f,L,U,modelPhaseEndpointLower,modelPhaseEndpointUpper,
      Int.cast_sub,Int.cast_add,Int.cast_natCast] using
      (norm_bufferedModes_endpoint_blocks_le_log hσ hδ hF hT hN hη hl hr
        (L-A).toNat (B-U).toNat)
  have hend : ‖f L+f U‖ ≤ 2*C*N/Real.sqrt T := by
    have hL := hmode l r η hl hr hη F δ T N L hδ hF hT hN
    have hU := hmode l r η hl hr hη F δ T N U hδ hF hT hN
    exact ((norm_add_le _ _).trans (add_le_add hL hU)).trans_eq (by ring)
  change ‖∑ q ∈ (Finset.Icc A B) \ modelPhaseCoreStationarySet F σ δ T N, f q‖ ≤ _
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add hext hend)).trans_eq (by ring)

theorem modelPhaseEndpointBlockLengths_le {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    (((modelPhaseEndpointLower F T N-modelPhaseCoreLower σ δ T N).toNat : ℕ) : ℝ) ≤
        3*(T/N)+3 ∧
      (((modelPhaseCoreUpper δ T N-modelPhaseEndpointUpper F T N).toNat : ℕ) : ℝ) ≤
        3*(T/N)+3 := by
  have hb := modelPhaseEndpoints_inside_core hF hT.le hN
  have ho := modelPhaseEndpointLower_lt_upper hσ hδ hF hT hN
  have hc := modelPhaseCore_card_le hσ.le (approximateModelPhase_tolerance_nonneg hF)
    (hδ.trans (min_le_right _ _)) hT.le hN
  have hleft : (Finset.Ico (modelPhaseCoreLower σ δ T N) (modelPhaseEndpointLower F T N)).card ≤
      (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)).card := by
    apply Finset.card_le_card
    intro q hq
    simp only [Finset.mem_Ico,Finset.mem_Icc] at hq ⊢
    omega
  have hright : (Finset.Ioc (modelPhaseEndpointUpper F T N) (modelPhaseCoreUpper δ T N)).card ≤
      (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)).card := by
    apply Finset.card_le_card
    intro q hq
    simp only [Finset.mem_Ioc,Finset.mem_Icc] at hq ⊢
    omega
  rw [Int.card_Ico] at hleft
  rw [Int.card_Ioc] at hright
  exact ⟨(Nat.cast_le.mpr hleft).trans hc,(Nat.cast_le.mpr hright).trans hc⟩

theorem modelPhaseBufferedCoreNonstationary_uniform {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < T → 0 < N →
        ‖∑ q ∈ (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)) \
          modelPhaseCoreStationarySet F σ δ T N,
          modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
            2*C*N/Real.sqrt T+(8/Real.pi)*(1+Real.log (3*(T/N)+3)) := by
  obtain ⟨C,hC,herror⟩ := modelPhaseBufferedCoreNonstationary_error hσ
  refine ⟨C,hC,?_⟩
  intro l r η hl hr hη F δ T N hδ hF hT hN
  have h := herror l r η hl hr hη F δ T N hδ hF hT hN
  have hb := modelPhaseEndpointBlockLengths_le hσ hδ hF hT hN
  have hH : 1 ≤ 3*(T/N)+3 := by
    have hp := div_nonneg hT.le hN.le
    linarith
  have hlog (n : ℕ) (hn : (n : ℝ) ≤ 3*(T/N)+3) :
      Real.log (n : ℝ) ≤ Real.log (3*(T/N)+3) := by
    by_cases hz : n = 0
    · simp only [hz,Nat.cast_zero,Real.log_zero]
      exact Real.log_nonneg hH
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) hn
  have hsum := add_le_add (hlog _ hb.1) (hlog _ hb.2)
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add (show (2 : ℝ) ≤ 2 from le_rfl) hsum) (by positivity : 0 ≤ 4/Real.pi)
  dsimp only at h
  apply h.trans
  have hh : (4/Real.pi)*(2+
      Real.log ((modelPhaseEndpointLower F T N-modelPhaseCoreLower σ δ T N).toNat : ℝ)+
      Real.log ((modelPhaseCoreUpper δ T N-modelPhaseEndpointUpper F T N).toNat : ℝ)) ≤
      (8/Real.pi)*(1+Real.log (3*(T/N)+3)) := by
    convert hm using 1 <;> ring
  exact add_le_add le_rfl hh

end TaoTrudgianYang2025
