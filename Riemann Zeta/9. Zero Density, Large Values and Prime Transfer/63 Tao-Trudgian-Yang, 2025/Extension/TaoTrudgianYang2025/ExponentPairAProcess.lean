import TaoTrudgianYang2025.ExponentPairOptimizedSource

/-!
# The classical A-process for the paper's analytic exponent pairs

The finite source proof derives the shift models, all-height correlation
bounds, summed differencing, actual integer optimization and epsilon losses.
No transformed-phase estimate or optimization certificate is assumed.
-/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem InExponentPairTriangle.aProcess {k l : ℝ}
    (h : InExponentPairTriangle k l) :
    InExponentPairTriangle (k/(2*k+2)) (l/(2*k+2)+1/2) := by
  have hk := h.1
  have hl := h.2.2.1
  have hl₁ := h.2.2.2.1
  have hd : 0 < 2*k+2 := by linarith
  have hkhalf : k/(2*k+2) ≤ 1/2 := (div_le_iff₀ hd).mpr (by linarith)
  have hlpos : 0 ≤ l/(2*k+2) := div_nonneg (by linarith) hd.le
  have hlhalf : l/(2*k+2) ≤ 1/2 := (div_le_iff₀ hd).mpr (by linarith)
  have hsum : k/(2*k+2)+l/(2*k+2) ≤ 1/2 := by
    rw [← add_div]
    exact (div_le_iff₀ hd).mpr (by linarith)
  exact ⟨div_nonneg hk hd.le,hkhalf,by linarith,by linarith,by linarith⟩

theorem isExponentPairEstimateNonAsymptotic_aProcess
    {k l : ℝ} (hkl : ExponentPair k l) :
    IsExponentPairEstimateNonAsymptotic (k/(2*k+2)) (l/(2*k+2)+1/2) := by
  intro ε hε σ hσ
  obtain ⟨δ,hδ,P,hP,D,hD,hbound⟩ := source_exponentialSum_aProcess_bound hkl hσ hε
  let C := D+5
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCD : D ≤ C^2 := by dsimp [C]; nlinarith
  have hC₅ : 5 ≤ C := by dsimp [C]; linarith
  have ht := hkl.inTriangle.aProcess
  refine ⟨δ,hδ,P,by omega,C,hC,?_⟩
  intro T N F a b hsetup
  have hN := hsetup.one_le_scale
  have hNpos := zero_lt_one.trans_le hN
  have hNT := hsetup.scale_le_param
  have hratio : 1 ≤ T/N := (le_div_iff₀ hNpos).mpr (by simpa using hNT)
  let Y := (T/N)^(k/(2*k+2)+ε)*N^(l/(2*k+2)+1/2+ε)
  have hY : 1 ≤ Y := by
    have h₁ := Real.one_le_rpow hratio (show 0 ≤ k/(2*k+2)+ε by linarith [ht.1])
    have h₂ := Real.one_le_rpow hN (show 0 ≤ l/(2*k+2)+1/2+ε by linarith [ht.2.2.1])
    dsimp [Y]
    nlinarith
  change ‖exponentialSumAt F T N a b‖ ≤ C*(T/N)^(k/(2*k+2)+ε)*N^(l/(2*k+2)+1/2+ε)
  rw [mul_assoc]
  change ‖exponentialSumAt F T N a b‖ ≤ C*Y
  by_cases hab : a ≤ b
  · by_cases hN₂ : 2 ≤ N
    · obtain ⟨L,hL⟩ := Nat.exists_eq_add_of_le hab
      have hb : b = a+L := hL
      have hs := hbound F T N a L hN₂ hNT hsetup.scale_le_start
        (by rw [← hb]; exact hsetup.end_le_two_mul_scale) hsetup.isApproximateModelPhase
      rw [← hb] at hs
      change ‖exponentialSumAt F T N a b‖^2 ≤ D*Y^2 at hs
      have hsq := mul_le_mul_of_nonneg_right hCD (sq_nonneg Y)
      have hpositive : 0 ≤ C*Y := mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hY)
      nlinarith
    · have hc := norm_exponentialSumAt_le_add_one F T N a b
      have hb := hsetup.end_le_two_mul_scale
      have hsmall : ‖exponentialSumAt F T N a b‖ ≤ C := by linarith
      exact hsmall.trans (le_mul_of_one_le_right (zero_le_one.trans hC) hY)
  · rw [exponentialSumAt_of_lt (by omega) F T N,norm_zero]
    exact mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hY)

theorem ExponentPair.aProcess {k l : ℝ} (h : ExponentPair k l) :
    ExponentPair (k/(2*k+2)) (l/(2*k+2)+1/2) :=
  ⟨h.inTriangle.aProcess,isExponentPairEstimate_iff_nonAsymptotic.mpr
    (isExponentPairEstimateNonAsymptotic_aProcess h)⟩

end TaoTrudgianYang2025
