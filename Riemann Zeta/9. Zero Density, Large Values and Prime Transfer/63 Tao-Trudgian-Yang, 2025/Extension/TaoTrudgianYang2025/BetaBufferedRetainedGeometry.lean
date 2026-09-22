import TaoTrudgianYang2025.BetaBufferedPowerError

/-!
# Geometry of every actually retained stationary frequency

The floor/ceiling rounding supplies a full integer frequency gap.
The actual critical point and its endpoint margins are then derived,
including for the global source comparison's error-paid short branch.
The positive slope window below is fixed in sigma, not a shrinking
reference-interior window.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem modelPhaseBufferedPlateau_frequency_gaps
    {F : ℝ → ℝ} {l r η T N : ℝ} {q : ℤ}
    (hT : 0 < T) (hN : 0 < N)
    (hq : q ∈ Finset.Ioo
      (modelPhaseBufferedPlateauLower F r η T N)
      (modelPhaseBufferedPlateauUpper F l η T N)) :
    deriv F (r-2*η)+N/T ≤ (q : ℝ)*N/T ∧
      (q : ℝ)*N/T+N/T ≤ deriv F (l+2*η) := by
  have hi := Finset.mem_Ioo.mp hq
  have hL : (modelPhaseBufferedPlateauLower F r η T N : ℝ)+1 ≤ (q : ℝ) := by
    exact_mod_cast (show modelPhaseBufferedPlateauLower F r η T N+1 ≤ q by omega)
  have hU : (q : ℝ)+1 ≤ (modelPhaseBufferedPlateauUpper F l η T N : ℝ) := by
    exact_mod_cast (show q+1 ≤ modelPhaseBufferedPlateauUpper F l η T N by omega)
  have hceil := Int.le_ceil ((T/N)*deriv F (r-2*η))
  have hfloor := Int.floor_le ((T/N)*deriv F (l+2*η))
  have hlow : (T/N)*deriv F (r-2*η)+1 ≤ (q : ℝ) := by
    dsimp [modelPhaseBufferedPlateauLower] at hL
    linarith
  have hupp : (q : ℝ)+1 ≤ (T/N)*deriv F (l+2*η) := by
    dsimp [modelPhaseBufferedPlateauUpper] at hU
    linarith
  have hs : 0 ≤ N/T := (div_pos hN hT).le
  have he (x : ℝ) : (T/N*x+1)*(N/T) = x+N/T := by field_simp
  constructor
  · have h := mul_le_mul_of_nonneg_right hlow hs
    rw [he] at h
    convert h using 1
    ring
  · have h := mul_le_mul_of_nonneg_right hupp hs
    have hc (x : ℝ) : (T/N*x)*(N/T) = x := by field_simp
    rw [hc] at h
    convert h using 1
    ring

theorem modelPhaseBufferedPlateau_critical_geometry
    {F : ℝ → ℝ} {σ δ l r η T N : ℝ} {q : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hflat : l+4*η < r)
    (hq : q ∈ Finset.Ioo
      (modelPhaseBufferedPlateauLower F r η T N)
      (modelPhaseBufferedPlateauUpper F l η T N)) :
    (q : ℝ)*N/T ∈ modelPhaseSlopeRange F ∧
      l+2*η+N/(T*(σ+1)) ≤ modelPhaseInverseSlope F ((q : ℝ)*N/T) ∧
      modelPhaseInverseSlope F ((q : ℝ)*N/T)+N/(T*(σ+1)) ≤ r-2*η := by
  have hg := modelPhaseBufferedPlateau_frequency_gaps hT hN hq
  have ha : l+2*η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hb : r-2*η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hw : 0 < N/T := div_pos hN hT
  have hv : (q : ℝ)*N/T ∈ modelPhaseSlopeRange F := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    have hba := modelPhaseClosedSlope_deriv_bounds hσ hδ hF ha
    have hbb := modelPhaseClosedSlope_deriv_bounds hσ hδ hF hb
    constructor <;> linarith [hba.2,hbb.1]
  have hi := modelPhaseInverseSlope_interior_of_gap hσ hδ hF hv ha hb hw hg.2 hg.1
  refine ⟨hv,?_⟩
  simpa only [div_div] using hi

theorem modelPhaseSharpStationarySet_critical_geometry
    {F : ℝ → ℝ} {σ δ T N : ℝ} {a b : ℕ} {q : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hq : q ∈ modelPhaseSharpStationarySet F T N a b) :
    (q : ℝ)*N/T ∈ modelPhaseSlopeRange F ∧
      (a : ℝ)/N+2*(Real.sqrt T)⁻¹+N/(T*(σ+1)) ≤
        modelPhaseInverseSlope F ((q : ℝ)*N/T) ∧
      modelPhaseInverseSlope F ((q : ℝ)*N/T)+N/(T*(σ+1)) ≤
        (b : ℝ)/N-2*(Real.sqrt T)⁻¹ := by
  by_cases hlong : (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N
  · rw [modelPhaseSharpStationarySet_of_long hlong] at hq
    exact modelPhaseBufferedPlateau_critical_geometry hσ hδ hF hT hN
      (by positivity) ((one_le_div hN).mpr ha) ((div_le_iff₀ hN).mpr hb) hlong hq
  · rw [modelPhaseSharpStationarySet_of_short (le_of_not_gt hlong)] at hq
    simp at hq

theorem modelPhaseSlopeRange_positive_window
    {F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ} {v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    v ∈ Icc ((2 : ℝ)^(-σ)/2) 2 := by
  have hu := modelPhaseInverseSlope_mem hv
  have he := approximateModelPhase_firstDeriv_bounds hσ hF hu
  rw [deriv_modelPhaseInverseSlope_apply hv] at he
  have hd₁ := hδ.trans (min_le_left _ _)
  have hd₂ := hδ.trans (min_le_right _ _)
  constructor <;> linarith [he.1,he.2]

end TaoTrudgianYang2025
