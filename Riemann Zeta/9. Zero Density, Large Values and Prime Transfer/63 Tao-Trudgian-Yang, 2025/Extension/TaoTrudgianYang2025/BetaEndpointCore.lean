import TaoTrudgianYang2025.BetaClosedSlope
import TaoTrudgianYang2025.BetaBufferedCoreStationary

/-!
# Exact integer partition of the genuine nonstationary core

The two endpoint integers are derived from the one-sided slopes of the
original phase. They are included in the nonstationary complement, even
when an endpoint slope is exactly an integer physical frequency.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

def modelPhaseEndpointLower (F : ℝ → ℝ) (T N : ℝ) : ℤ :=
  ⌊(T/N)*modelPhaseClosedSlope F 2⌋

def modelPhaseEndpointUpper (F : ℝ → ℝ) (T N : ℝ) : ℤ :=
  ⌈(T/N)*modelPhaseClosedSlope F 1⌉

theorem modelPhaseFrequency_mem_slopeRange_iff {σ δ T N q : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    q*N/T ∈ modelPhaseSlopeRange F ↔
      (T/N)*modelPhaseClosedSlope F 2 < q ∧ q < (T/N)*modelPhaseClosedSlope F 1 := by
  rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
  simp only [mem_Ioo,div_mul_eq_mul_div,lt_div_iff₀ hT,div_lt_iff₀ hT,
    lt_div_iff₀ hN,div_lt_iff₀ hN]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]

theorem modelPhaseFrequency_not_stationary_iff {σ δ T N : ℝ} {F : ℝ → ℝ} {q : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    (q : ℝ)*N/T ∉ modelPhaseSlopeRange F ↔
      q ≤ modelPhaseEndpointLower F T N ∨ modelPhaseEndpointUpper F T N ≤ q := by
  rw [modelPhaseFrequency_mem_slopeRange_iff hσ hδ hF hT hN]
  simp only [not_and_or,not_lt,modelPhaseEndpointLower,modelPhaseEndpointUpper,
    Int.le_floor,Int.ceil_le]

theorem modelPhaseEndpointLower_lt_upper {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    modelPhaseEndpointLower F T N < modelPhaseEndpointUpper F T N := by
  have hm := modelPhaseClosedSlope_strictAntiOn hσ hδ hF
    (by norm_num : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (by norm_num : (2 : ℝ) ∈ Icc (1 : ℝ) 2) (by norm_num)
  have ht := mul_lt_mul_of_pos_left hm (div_pos hT hN)
  have he := (Int.floor_le ((T/N)*modelPhaseClosedSlope F 2)).trans_lt
    (ht.trans_le (Int.le_ceil ((T/N)*modelPhaseClosedSlope F 1)))
  exact_mod_cast he

theorem modelPhaseEndpoints_inside_core {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 ≤ T) (hN : 0 < N) :
    modelPhaseCoreLower σ δ T N ≤ modelPhaseEndpointLower F T N ∧
      modelPhaseEndpointUpper F T N ≤ modelPhaseCoreUpper δ T N := by
  have hl := abs_le.mp (modelPhaseClosedSlope_model_error hF
    (show (2 : ℝ) ∈ phaseInterval by norm_num [phaseInterval]))
  have hu := abs_le.mp (modelPhaseClosedSlope_model_error hF
    (show (1 : ℝ) ∈ phaseInterval by norm_num [phaseInterval]))
  rw [Real.one_rpow] at hu
  constructor
  · exact Int.floor_mono (mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ)^(-σ)-δ ≤
      modelPhaseClosedSlope F 2) (div_nonneg hT hN.le))
  · exact Int.ceil_mono (mul_le_mul_of_nonneg_left (by linarith : modelPhaseClosedSlope F 1 ≤
      1+δ) (div_nonneg hT hN.le))

theorem modelPhaseCore_nonstationary_eq_endpoint_union {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)) \
      modelPhaseCoreStationarySet F σ δ T N =
        Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseEndpointLower F T N) ∪
        Finset.Icc (modelPhaseEndpointUpper F T N) (modelPhaseCoreUpper δ T N) := by
  classical
  have hb := modelPhaseEndpoints_inside_core hF hT.le hN
  have ho := modelPhaseEndpointLower_lt_upper hσ hδ hF hT hN
  ext q
  simp only [Finset.mem_sdiff,modelPhaseCoreStationarySet_mem]
  rw [show (q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N) ∧
      ¬(q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N) ∧
        (q : ℝ)*N/T ∈ modelPhaseSlopeRange F)) ↔
      (q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N) ∧
        (q : ℝ)*N/T ∉ modelPhaseSlopeRange F) by tauto]
  rw [modelPhaseFrequency_not_stationary_iff hσ hδ hF hT hN]
  simp only [Finset.mem_Icc,Finset.mem_union]
  omega

theorem modelPhaseCore_nonstationary_sum {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N)
    (f : ℤ → ℂ) :
    (∑ q ∈ (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)) \
      modelPhaseCoreStationarySet F σ δ T N, f q) =
        (∑ q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseEndpointLower F T N), f q)+
        ∑ q ∈ Finset.Icc (modelPhaseEndpointUpper F T N) (modelPhaseCoreUpper δ T N), f q := by
  rw [modelPhaseCore_nonstationary_eq_endpoint_union hσ hδ hF hT hN,Finset.sum_union]
  rw [Finset.disjoint_left]
  intro q hq hq'
  have hl := (Finset.mem_Icc.mp hq).2
  have hu := (Finset.mem_Icc.mp hq').1
  have ho := modelPhaseEndpointLower_lt_upper hσ hδ hF hT hN
  omega

theorem modelPhaseCoreStationarySet_eq_endpoint_Ioo {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    modelPhaseCoreStationarySet F σ δ T N =
      Finset.Ioo (modelPhaseEndpointLower F T N) (modelPhaseEndpointUpper F T N) := by
  have hb := modelPhaseEndpoints_inside_core hF hT.le hN
  ext q
  have hm : (q : ℝ)*N/T ∈ modelPhaseSlopeRange F ↔
      modelPhaseEndpointLower F T N < q ∧ q < modelPhaseEndpointUpper F T N := by
    simpa only [not_not,not_or,not_le] using
      not_congr (modelPhaseFrequency_not_stationary_iff (q := q) hσ hδ hF hT hN)
  rw [modelPhaseCoreStationarySet_mem,hm]
  simp only [Finset.mem_Icc,Finset.mem_Ioo]
  omega

end TaoTrudgianYang2025
