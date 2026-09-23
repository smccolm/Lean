import TaoTrudgianYang2025.SargosCProcessHighSource
import TaoTrudgianYang2025.SargosCProcessLowComparison

/-!
# Sargos's C-process for the actual analytic exponent-pair predicate

The source proof derives signed-frequency counting, the real-scale transformed
model, finite differencing, integer optimization, low-height input and all
source-window branches. No optimization or transformed-sum certificate is assumed.
-/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem isExponentPairEstimateNonAsymptotic_cProcess {k l : ℝ} (hkl : ExponentPair k l) :
    IsExponentPairEstimateNonAsymptotic (sargosCProcessK k) (sargosCProcessL k l) := by
  intro ε hε σ hσ
  obtain ⟨δL,hδL,PL,hPL,CL,hCL,hlow⟩ := sargos_low_height_model_bound hkl.inTriangle hσ hε
  obtain ⟨δH,hδH,PH,hPH,N₀,hN₀,CH,hCH,hhigh⟩ := sargos_high_height_source_bound hkl hσ hε
  let C := max CL (max CH (3*N₀+3))
  have hCLC : CL ≤ C := le_max_left _ _
  have hCHC : CH ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hNC : 3*N₀+3 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 1 ≤ C := hCL.trans hCLC
  refine ⟨min δL δH,lt_min hδL hδH,max PL PH,hPL.trans (le_max_left _ _),C,hC,?_⟩
  intro T N F a b hsetup
  have hN := hsetup.one_le_scale
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hNT := hsetup.scale_le_param
  have hTp : 0 < T := hNp.trans_le hNT
  have hU : 1 ≤ T/N := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNT)
  have ht := hkl.inTriangle.sargosCProcess
  let Y := (T/N)^(sargosCProcessK k+ε)*N^(sargosCProcessL k l+ε)
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hU (show 0 ≤ sargosCProcessK k+ε by linarith [ht.1]))
    (Real.one_le_rpow hN (show 0 ≤ sargosCProcessL k l+ε by linarith [ht.2.2.1]))
  have hFL : IsApproximateModelPhaseFunction F σ PL δL :=
    approximateModelPhase_mono hsetup.isApproximateModelPhase (le_max_left _ _) (min_le_left _ _)
  have hFH : IsApproximateModelPhaseFunction F σ PH δH :=
    approximateModelPhase_mono hsetup.isApproximateModelPhase (le_max_right _ _) (min_le_right _ _)
  change ‖exponentialSumAt F T N a b‖ ≤ C*(T/N)^(sargosCProcessK k+ε)*N^(sargosCProcessL k l+ε)
  rw [mul_assoc]
  change ‖exponentialSumAt F T N a b‖ ≤ C*Y
  by_cases hlargeN : N₀ ≤ N
  · by_cases hlowT : T ≤ N^(sargosCProcessThreshold k l)
    · have hs := hlow T N F a b
        ⟨hCLC.trans hsetup.threshold_le_param,hN,hNT,hFL,
          hsetup.scale_le_start,hsetup.end_le_two_mul_scale⟩ hlowT
      have hh : ‖exponentialSumAt F T N a b‖ ≤ CL*Y := by
        simpa only [Y,mul_assoc] using hs
      exact hh.trans (mul_le_mul_of_nonneg_right hCLC (zero_le_one.trans hY))
    · by_cases hab : a ≤ b
      · obtain ⟨M,hM⟩ := Nat.exists_eq_add_of_le hab
        have hb : (a:ℝ)+M ≤ 2*N := by
          have hh := hsetup.end_le_two_mul_scale
          rw [hM] at hh
          simpa only [Nat.cast_add] using hh
        have hs := hhigh F T N a M hlargeN hNT hsetup.scale_le_start hb
          (le_of_not_ge hlowT) hFH
        rw [← hM] at hs
        change ‖exponentialSumAt F T N a b‖^12 ≤ CH*Y^12 at hs
        have hpower : CH ≤ C^12 := hCHC.trans (le_self_pow₀ hC (by norm_num))
        have hh : ‖exponentialSumAt F T N a b‖^12 ≤ (C*Y)^12 := by
          calc
            _ ≤ CH*Y^12 := hs
            _ ≤ C^12*Y^12 := mul_le_mul_of_nonneg_right hpower (by positivity)
            _ = _ := (mul_pow _ _ _).symm
        exact (pow_le_pow_iff_left₀ (norm_nonneg _)
          (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hY)) (by norm_num : 12 ≠ 0)).mp hh
      · rw [exponentialSumAt_of_lt (by omega) F T N,norm_zero]
        exact mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hY)
  · have hn : N ≤ N₀ := le_of_not_ge hlargeN
    have hs := norm_exponentialSumAt_le_add_one F T N a b
    have hb := hsetup.end_le_two_mul_scale
    have hh : ‖exponentialSumAt F T N a b‖ ≤ C := by linarith
    exact hh.trans (le_mul_of_one_le_right (zero_le_one.trans hC) hY)

theorem ExponentPair.cProcess {k l : ℝ} (h : ExponentPair k l) :
    ExponentPair (k/(12*(1+4*k))) ((11*(1+4*k)+l)/(12*(1+4*k))) :=
  ⟨h.inTriangle.sargosCProcess,isExponentPairEstimate_iff_nonAsymptotic.mpr
    (isExponentPairEstimateNonAsymptotic_cProcess h)⟩

end TaoTrudgianYang2025
