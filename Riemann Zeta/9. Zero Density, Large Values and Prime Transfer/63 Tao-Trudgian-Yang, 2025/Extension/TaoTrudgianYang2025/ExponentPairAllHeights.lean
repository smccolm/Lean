import TaoTrudgianYang2025.ExponentPairLowFrequency
import TaoTrudgianYang2025.ExponentPairTransition

/-!
# Exponent-pair estimates at every positive physical height

The low, transition, bounded and large-height regimes are proved from
the actual phase and the analytic exponent-pair predicate. Constants and
finite model order precede every source datum.
-/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem ExponentPair.allPositiveHeight_bound
    {k l σ ε : ℝ} (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
        0 < T → 1 ≤ N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        IsApproximateModelPhaseFunction F σ P δ →
        ‖exponentialSumAt F T N a b‖ ≤
          C*((T/N)^(k+ε)*N^(l+ε)+N/T) := by
  obtain ⟨d,hd,P,hP,B,hB,hlarge⟩ :=
    (isExponentPairEstimate_iff_nonAsymptotic.mp hkl.estimate) ε hε σ hσ
  let ds : ℝ := min ((2 : ℝ)^(-σ)/2) 1
  let dc : ℝ := min (modelPhaseCurvatureLower σ) 1
  let δ := min d (min ds dc)
  have hds : 0 < ds := by dsimp [ds]; positivity
  have hdc : 0 < dc := lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one
  have hδ : 0 < δ := lt_min hd (lt_min hds hdc)
  have hδd : δ ≤ d := min_le_left _ _
  have hδs : δ ≤ ds := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ ≤ dc := (min_le_right _ _).trans (min_le_right _ _)
  let C₀ := modelPhaseFirstDerivativeConstant σ
  let C₁ := 3*modelPhaseSumConstant σ*(4 : ℝ)^(k+ε)
  have hC₀ : 0 < C₀ := modelPhaseFirstDerivativeConstant_pos _
  have hC₁ : 0 < C₁ := mul_pos (mul_pos (by norm_num)
    (modelPhaseSumConstant_pos hσ)) (Real.rpow_pos_of_pos (by norm_num) _)
  let C := 3*B+11+C₀+C₁
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCB : B ≤ C := by dsimp [C]; linarith
  have hCsmall : 2*B+1 ≤ C := by dsimp [C]; linarith
  have hC₉ : 9 ≤ C := by dsimp [C]; linarith
  have hCC₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hCC₁ : C₁ ≤ C := by dsimp [C]; linarith
  refine ⟨δ,hδ,P,hP,C,hC,?_⟩
  intro T N F a b hT hN ha hb hF
  have hNpos := zero_lt_one.trans_le hN
  have hmain : 0 ≤ (T/N)^(k+ε)*N^(l+ε) := by positivity
  have hratio : 0 ≤ N/T := by positivity
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  have hcard : ‖exponentialSumAt F T N a b‖ ≤ 2*N+1 :=
    (norm_exponentialSumAt_le_add_one F T N a b).trans (by linarith)
  by_cases hNT : N ≤ T
  · have hbase : 1 ≤ T/N := (le_div_iff₀ hNpos).mpr (by simpa using hNT)
    have hp₁ := Real.one_le_rpow hbase (show 0 ≤ k+ε by linarith [hkl.inTriangle.1])
    have hp₂ := Real.one_le_rpow hN (show 0 ≤ l+ε by linarith [hkl.inTriangle.2.2.1])
    have hone : 1 ≤ (T/N)^(k+ε)*N^(l+ε) := by nlinarith
    by_cases hBT : B ≤ T
    · have hh := hlarge T N F a b
        ⟨hBT,hN,hNT,approximateModelPhase_mono hF le_rfl hδd,ha,hb⟩
      calc
        _ ≤ B*((T/N)^(k+ε)*N^(l+ε)) := by simpa only [mul_assoc] using hh
        _ ≤ C*((T/N)^(k+ε)*N^(l+ε)) :=
          mul_le_mul_of_nonneg_right hCB hmain
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hratio)
          (zero_le_one.trans hC)
    · have hNC : N ≤ B := hNT.trans (le_of_not_ge hBT)
      have hh : ‖exponentialSumAt F T N a b‖ ≤ C := hcard.trans (by linarith)
      exact hh.trans (le_mul_of_one_le_right (zero_le_one.trans hC) (by linarith))
  · have hTN : T ≤ N := le_of_not_ge hNT
    have hratio₁ : 1 ≤ N/T := (le_div_iff₀ hT).mpr (by simpa using hTN)
    by_cases hlow : T ≤ N/4
    · have hh := norm_exponentialSumAt_le_firstDerivative hσ hT hNpos hδs hδc
        hF₁ ha hb hlow
      calc
        _ ≤ C₀*(N/T) := hh
        _ ≤ C*(N/T) := mul_le_mul_of_nonneg_right hCC₀ hratio
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hmain)
          (zero_le_one.trans hC)
    · by_cases hfour : 4 ≤ N
      · have hh := norm_exponentialSumAt_le_transition hkl.inTriangle.1
          hkl.inTriangle.2.2.1 hε.le hσ hfour hδc hF₁ ha hb
          (le_of_not_ge hlow) hTN
        calc
          _ ≤ C₁*((T/N)^(k+ε)*N^(l+ε)) := hh
          _ ≤ C*((T/N)^(k+ε)*N^(l+ε)) :=
            mul_le_mul_of_nonneg_right hCC₁ hmain
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hratio)
            (zero_le_one.trans hC)
      · have hsmall : ‖exponentialSumAt F T N a b‖ ≤ C :=
          hcard.trans (by linarith)
        exact hsmall.trans (le_mul_of_one_le_right (zero_le_one.trans hC) (by linarith))

end TaoTrudgianYang2025
