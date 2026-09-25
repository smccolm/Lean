import TaoTrudgianYang2025.IvicSixthExcessSource
import TaoTrudgianYang2025.ZetaPerronAboveOne

/-! Actual truncated convolution entries and separated sixth-power counting. -/

noncomputable section
open MeasureTheory Set Finset
namespace TaoTrudgianYang2025

theorem ivicSixth_convolution_split {T U t : ℝ}
    (hT : 0 < T) (hU : 0 ≤ U) (ht : t ∈ Icc T (2*T)) :
    zetaMomentConvolution T t ≤ U*zetaMomentLogLoss T+
      ∫ u in T/2..3*T, zetaMomentKernel t u*ivicSixthExcess U u := by
  have hk := continuous_zetaMomentKernel t
  have hf := continuous_zetaMomentCriticalNorm
  have hg := continuous_ivicSixthExcess U
  have hab : T/2 ≤ 3*T := by linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    ((hk.mul hf).intervalIntegrable (T/2) (3*T))
    ((hk.mul (continuous_const.add hg)).intervalIntegrable (T/2) (3*T))
    (fun u _ => mul_le_mul_of_nonneg_left
      (zetaMomentCriticalNorm_le_threshold_add_excess U u) (zetaMomentKernel_pos t u).le)
  have he : (∫ u in T/2..3*T, zetaMomentKernel t u*(U+ivicSixthExcess U u)) =
      U*(∫ u in T/2..3*T, zetaMomentKernel t u)+
        ∫ u in T/2..3*T, zetaMomentKernel t u*ivicSixthExcess U u := by
    simp_rw [mul_add]
    rw [intervalIntegral.integral_add (μ := volume)
      (f := fun u => zetaMomentKernel t u*U)
      (g := fun u => zetaMomentKernel t u*ivicSixthExcess U u)
      ((hk.mul_const U).intervalIntegrable (T/2) (3*T))
      ((hk.mul hg).intervalIntegrable (T/2) (3*T)),
      intervalIntegral.integral_mul_const]
    ring
  dsimp only [Pi.mul_apply,Pi.add_apply] at hi
  rw [he] at hi
  exact hi.trans (add_le_add
    (mul_le_mul_of_nonneg_left (integral_zetaMomentKernel_source_mass hT ht).2 hU) le_rfl)

theorem ZetaLargeValuePattern.ivicSixth_truncated_cardinality
    (P : ZetaLargeValuePattern) {C U : ℝ} (hC : 0 < C) (hU : 0 ≤ U)
    (hEntry : ∀ t ∈ P.ordinates,
      P.V ≤ C*P.N^(1/2:ℝ)*zetaMomentConvolution P.T t)
    (hsmall : 2*(C*P.N^(1/2:ℝ))*U*zetaMomentLogLoss P.T ≤ P.V) :
    (P.ordinates.card : ℝ)*P.V^6 ≤
      (2*C)^6*P.N^3*zetaMomentLogLoss P.T^6*
        ∫ u in P.T/2..3*P.T, ivicSixthExcess U u^6 := by
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  let F := 2*(C*P.N^(1/2:ℝ))
  have hF : 0 < F := by dsimp [F]; positivity
  have hRange (t : ℝ) (ht : t ∈ P.ordinates) : t ∈ Icc P.T (2*P.T) := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hlarge (t : ℝ) (ht : t ∈ P.ordinates) :
      P.V/F ≤ ∫ u in P.T/2..3*P.T, zetaMomentKernel t u*ivicSixthExcess U u := by
    apply (div_le_iff₀ hF).2
    have hs := mul_le_mul_of_nonneg_left
      (ivicSixth_convolution_split P.T_pos hU (hRange t ht))
      (by positivity : 0 ≤ C*P.N^(1/2:ℝ))
    have he := (hEntry t ht).trans hs
    dsimp [F]
    nlinarith
  have hsum := sum_convolution_realMoment_le_moment P.ordinates P.T_pos
    (by norm_num : (1:ℝ) ≤ 6) P.ordinates_oneSeparated hRange
    (ivicSixthExcess U) (continuous_ivicSixthExcess U) (ivicSixthExcess_nonneg U)
  norm_num only [Real.rpow_ofNat] at hsum
  have hlo : (P.ordinates.card : ℝ)*(P.V/F)^6 ≤
      ∑ t ∈ P.ordinates,
        (∫ u in P.T/2..3*P.T, zetaMomentKernel t u*ivicSixthExcess U u)^6 := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      Finset.sum_le_sum (fun t ht =>
        pow_le_pow_left₀ (div_nonneg P.V_pos.le hF.le) (hlarge t ht) 6)
  have hb := mul_le_mul_of_nonneg_left (hlo.trans hsum) (pow_nonneg hF.le 6)
  have he : F^6*((P.ordinates.card : ℝ)*(P.V/F)^6) = (P.ordinates.card : ℝ)*P.V^6 := by
    field_simp [hF.ne']
  have hscale : F^6 = (2*C)^6*P.N^3 := by
    dsimp [F]
    rw [show 2*(C*P.N^(1/2:ℝ)) = (2*C)*P.N^(1/2:ℝ) by ring,mul_pow,
      ← Real.rpow_mul_natCast hN.le]
    norm_num
  rw [he,hscale] at hb
  simpa only [mul_assoc] using hb

end TaoTrudgianYang2025
