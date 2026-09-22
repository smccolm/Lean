import TaoTrudgianYang2025.BetaBufferedCoreStationary

/-!
# Actual source expansion through the stationary part of the physical core

The remaining nonstationary core modes are retained literally. No
estimate for those moving boundary modes, or for beta reflection,
is assumed or claimed here.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

def modelPhaseBufferedCoreExpansion (l r η : ℝ) (F : ℝ → ℝ)
    (σ δ T N : ℝ) : ℂ :=
  (∑ q ∈ modelPhaseCoreStationarySet F σ δ T N,
    (modelPhaseBufferedCutoff l r η (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
      modelPhaseStationaryMainTerm F T N q)+
    ∑ q ∈ (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)) \
      modelPhaseCoreStationarySet F σ δ T N,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q

theorem modelPhaseCore_sub_bufferedExpansion (l r η : ℝ) (F : ℝ → ℝ)
    (σ δ T N : ℝ) :
    (∑ q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N),
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q)-
        modelPhaseBufferedCoreExpansion l r η F σ δ T N =
      ∑ q ∈ modelPhaseCoreStationarySet F σ δ T N,
        (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
          (modelPhaseBufferedCutoff l r η (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
            modelPhaseStationaryMainTerm F T N q) := by
  classical
  have hs : modelPhaseCoreStationarySet F σ δ T N ⊆
      Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N) := by
    intro q hq
    exact (modelPhaseCoreStationarySet_mem.mp hq).1
  have he := Finset.sum_sdiff hs
    (f := fun q : ℤ => modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q)
  rw [modelPhaseBufferedCoreExpansion,← he,Finset.sum_sub_distrib]
  abel

theorem modelPhase_buffered_source_core_expansion
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 1 ≤ D ∧
      ∀ (N η : ℝ) (a b : ℕ),
        0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        ∀ (F : ℝ → ℝ) (δ T ε : ℝ),
          δ ≤ min (modelPhaseCurvatureLower σ) 1 →
          IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
          0 < T → 0 < ε →
          let A := modelPhaseCoreLower σ δ T N
          let B := modelPhaseCoreUpper δ T N
          let R : ℕ := ⌈C*(η⁻¹)^2*(1+|T|)^2/(N*ε)⌉₊+A.natAbs+B.natAbs+1
          ‖exponentialSumAt F T N a b-
            modelPhaseBufferedCoreExpansion ((a : ℝ)/N) ((b : ℝ)/N) η F σ δ T N‖ ≤
            4*N*η+2+ε+
              (4/Real.pi)*(2+Real.log ((A+(R : ℤ)).toNat : ℝ)+
                Real.log (((R : ℤ)-B).toNat : ℝ))+
              D*(η⁻¹)^3*(1+N/T) := by
  obtain ⟨C,hC,hcore⟩ := modelPhase_buffered_poisson_core_precision hσ
  obtain ⟨D,hD,hstationary⟩ := modelPhaseBufferedCoreStationary_error hσ
  refine ⟨C,hC,D,hD,?_⟩
  intro N η a b hN hη hη₁ ha hb F δ T ε hδ hF hT hε A B R
  have hF₁ := approximateModelPhase_mono hF bufferedStationaryPhaseOrder_pos le_rfl
  have hsource := (hcore N η a b hN hη hη₁ ha hb F δ T ε hδ hF₁ hT hε).2.2.2
  have hstation := hstationary ((a : ℝ)/N) ((b : ℝ)/N) η
    ((one_le_div hN).mpr ha) ((div_le_iff₀ hN).mpr hb) hη hη₁ F δ T N hδ hF hT hN
  let core := ∑ q ∈ Finset.Icc A B, modelPhaseFourierMode
    (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q
  have hdiff : ‖core-
      modelPhaseBufferedCoreExpansion ((a : ℝ)/N) ((b : ℝ)/N) η F σ δ T N‖ ≤
        D*(η⁻¹)^3*(1+N/T) := by
    rw [show core = ∑ q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N)
        (modelPhaseCoreUpper δ T N), modelPhaseFourierMode
          (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q by rfl,
      modelPhaseCore_sub_bufferedExpansion]
    exact hstation
  calc
    _ = ‖(exponentialSumAt F T N a b-core)+
        (core-modelPhaseBufferedCoreExpansion ((a : ℝ)/N) ((b : ℝ)/N) η F σ δ T N)‖ := by
      congr 1
      abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hsource hdiff)

end TaoTrudgianYang2025
