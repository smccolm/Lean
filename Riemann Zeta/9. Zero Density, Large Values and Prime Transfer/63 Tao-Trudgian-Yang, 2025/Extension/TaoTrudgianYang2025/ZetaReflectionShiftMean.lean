import TaoTrudgianYang2025.ZetaReflectionShiftMass

/-! A common shift with only logarithmic loss from the actual positive kernel. -/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Classical Interval
namespace TaoTrudgianYang2025

theorem integral_reflection_commonShift_kernel {T : ℝ} (hT : 0 < T) :
    (∫ u : ℝ in Icc (-(2*T)) (2*T), (1 : ℝ)/(1+|u|)) ≤ zetaMomentLogLoss T := by
  have hmass := integral_zetaMomentKernel (a := -(2*T)) (t := 0) (b := 2*T)
    (by linarith) (by linarith)
  have he : (∫ u : ℝ in Icc (-(2*T)) (2*T), (1 : ℝ)/(1+|u|)) =
      2*Real.log (1+2*T) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith)]
    simpa only [zetaMomentKernel,sub_zero,add_zero,sub_neg_eq_add,two_mul] using hmass
  rw [he]
  have hlog := Real.log_le_log (by linarith : 0 < 1+2*T)
    (show 1+2*T ≤ (Nat.ceil (2*T) : ℝ)+1 by linarith [Nat.le_ceil (2*T)])
  unfold zetaMomentLogLoss
  linarith

theorem exists_reflection_common_shift (W : Finset ℝ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) {T L : ℝ} (hT : 0 < T) (hL : 0 < L)
    (hW : ∀ t ∈ W, t ∈ Icc T (2*T))
    (hlarge : L ≤ ∑ t ∈ W, zetaReflectionConvolution S T t) :
    ∃ u ∈ Icc (-(2*T)) (2*T),
      L/(2*zetaMomentLogLoss T) ≤ reflectionShiftMass W S T u := by
  have hlog := zetaMomentLogLoss_pos T
  have hi := integrable_reflectionShiftMass_weighted W S hS T
  have hk : IntegrableOn (fun u : ℝ => (1 : ℝ)/(1+|u|)) (Icc (-(2*T)) (2*T)) := by
    have hc : Continuous (fun u : ℝ => (1 : ℝ)/(1+|u|)) :=
      continuous_const.div (by fun_prop) (fun u => ne_of_gt (by positivity : 0 < 1+|u|))
    exact hc.continuousOn.integrableOn_Icc
  by_contra hex
  push Not at hex
  have hbound :
      (∫ u : ℝ in Icc (-(2*T)) (2*T), reflectionShiftMass W S T u/(1+|u|)) ≤ L/2 := by
    calc
      _ ≤ ∫ u : ℝ in Icc (-(2*T)) (2*T),
          (L/(2*zetaMomentLogLoss T))*((1 : ℝ)/(1+|u|)) := by
        apply integral_mono_ae hi.integrableOn (hk.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        have h := div_le_div_of_nonneg_right (hex u hu).le (show 0 ≤ 1+|u| by positivity)
        convert h using 1
        ring
      _ = (L/(2*zetaMomentLogLoss T))*
          ∫ u : ℝ in Icc (-(2*T)) (2*T), (1 : ℝ)/(1+|u|) := integral_const_mul _ _
      _ ≤ (L/(2*zetaMomentLogLoss T))*zetaMomentLogLoss T :=
        mul_le_mul_of_nonneg_left (integral_reflection_commonShift_kernel hT) (by positivity)
      _ = _ := by field_simp
  rw [← sum_reflectionConvolution_eq_commonShift_integral W S hS hT hW] at hbound
  linarith

end TaoTrudgianYang2025
