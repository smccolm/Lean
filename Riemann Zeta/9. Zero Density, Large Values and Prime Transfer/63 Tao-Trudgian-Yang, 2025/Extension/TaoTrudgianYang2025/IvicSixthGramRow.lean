import TaoTrudgianYang2025.IvicSixthTraceMellin
import TaoTrudgianYang2025.IvicSixthWindowOverlap
import TaoTrudgianYang2025.BourgainSmoothedMoments

/-! Actual smooth Gram rows split at the restricted-sixth threshold. -/

noncomputable section
open Finset MeasureTheory Set
namespace TaoTrudgianYang2025

theorem ivicSixth_local_integral_split {H : ℝ} (hH : 0 ≤ H) (U t : ℝ) :
    (∫ u in -H..H,zetaMomentCriticalNorm (u+t)) ≤
      2*H*U+(∫ u in -H..H,ivicSixthExcess U (t+u)) := by
  have hnorm : Continuous (fun u => zetaMomentCriticalNorm (u+t)) :=
    continuous_zetaMomentCriticalNorm.comp (continuous_id.add continuous_const)
  have hexcess : Continuous (fun u => ivicSixthExcess U (t+u)) :=
    (continuous_ivicSixthExcess U).comp (continuous_const.add continuous_id)
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -H ≤ H)
    (hnorm.intervalIntegrable (-H) H)
    ((continuous_const.add hexcess).intervalIntegrable (-H) H)
    (fun u _ => by
      simpa only [add_comm u t] using zetaMomentCriticalNorm_le_threshold_add_excess U (u+t))
  dsimp only [Pi.add_apply] at hm
  rw [intervalIntegral.integral_add (μ := volume)
    (f := fun _ => U) (g := fun u => ivicSixthExcess U (t+u))
    (continuous_const.intervalIntegrable (-H) H) (hexcess.intervalIntegrable (-H) H),
    intervalIntegral.integral_const] at hm
  simpa only [smul_eq_mul,sub_neg_eq_add,← two_mul] using hm

theorem LargeValuePattern.difference_abs_le_height (P : LargeValuePattern)
    {t u : ℝ} (ht : t ∈ P.ordinates) (hu : u ∈ P.ordinates) :
    |u-t| ≤ P.T := by
  have htr := P.ordinates_in_interval t ht
  have hur := P.ordinates_in_interval u hu
  apply abs_le.mpr
  constructor <;> linarith [P.interval_length,htr.1,htr.2,hur.1,hur.2]

theorem exists_ivicSixth_gram_row_split {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : LargeValuePattern, P.ordinates.Nonempty →
      ∀ H U : ℝ, 0 ≤ H → ∃ t ∈ P.ordinates,
      (P.ordinates.card:ℝ)*P.V^2 ≤ 2*P.N*C*
        (4*P.N+Real.sqrt P.N*
          (2*H*U*(P.ordinates.card:ℝ)+
            ∑ u ∈ P.ordinates, ∫ v in -H..H,ivicSixthExcess U (u-t+v))+
          (P.ordinates.card:ℝ)*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
  obtain ⟨C,hC,hbound⟩ := ivicSixthSmoothTrace_localized (2*q)
  refine ⟨C,hC,?_⟩
  intro P hne H U hH
  obtain ⟨t,ht,hrow⟩ := P.exists_large_smooth_sixth_gram_row hne
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hQ : 0 < P.scale := by
    have hh : (0:ℝ) < P.scale := by simpa only [P.N_eq_scale] using hN
    exact_mod_cast hh
  have hpole := bourgain_sum_reciprocal_pow_le_four P.ordinates t P.ordinates_oneSeparated hq
  have hpoint (u : ℝ) (hu : u ∈ P.ordinates) :
      ‖ivicSixthSmoothTrace P.scale (u-t)‖ ≤ C*
        (P.N/(1+|u-t|)^(2*q)+
          Real.sqrt P.N*(2*H*U+(∫ v in -H..H,ivicSixthExcess U (u-t+v)))+
          Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
    have hh := hbound P.scale hQ (u-t) H hH
    rw [← P.N_eq_scale] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply add_le_add
    · exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (ivicSixth_local_integral_split hH U (u-t))
          (Real.sqrt_nonneg _))
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (by linarith [P.difference_abs_le_height ht hu]) (Real.sqrt_nonneg _)
  have hsum := Finset.sum_le_sum hpoint
  have he : (∑ u ∈ P.ordinates,C*
        (P.N/(1+|u-t|)^(2*q)+
          Real.sqrt P.N*(2*H*U+(∫ v in -H..H,ivicSixthExcess U (u-t+v)))+
          Real.sqrt P.N*(1+P.T)/(1+H)^(2*q))) =
      C*(P.N*(∑ u ∈ P.ordinates,1/(1+|u-t|)^(2*q))+
        Real.sqrt P.N*(2*H*U*(P.ordinates.card:ℝ)+
          ∑ u ∈ P.ordinates, ∫ v in -H..H,ivicSixthExcess U (u-t+v))+
        (P.ordinates.card:ℝ)*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
    simp only [div_eq_mul_inv,one_mul,Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,nsmul_eq_mul]
    ring
  rw [he] at hsum
  have hp := mul_le_mul_of_nonneg_left hpole hN.le
  have htot : (∑ u ∈ P.ordinates,‖ivicSixthSmoothTrace P.scale (u-t)‖) ≤
      C*(4*P.N+Real.sqrt P.N*
        (2*H*U*(P.ordinates.card:ℝ)+
          ∑ u ∈ P.ordinates, ∫ v in -H..H,ivicSixthExcess U (u-t+v))+
        (P.ordinates.card:ℝ)*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
    apply hsum.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact add_le_add (add_le_add (by nlinarith [hp]) le_rfl) le_rfl
  refine ⟨t,ht,?_⟩
  have hh := hrow.trans (mul_le_mul_of_nonneg_left htot (by positivity))
  simpa only [mul_assoc] using hh

theorem LargeValuePattern.ivicSixth_difference_window_sixth (P : LargeValuePattern)
    {t H : ℝ} (ht : t ∈ P.ordinates) (hH : 0 ≤ H) (U : ℝ) :
    (∑ u ∈ P.ordinates, (∫ v in -H..H,ivicSixthExcess U (u-t+v))^6) ≤
      (2*H)^5*(2*H+1)*
        (∫ v in -(P.T+H)..P.T+H,ivicSixthExcess U v^6) := by
  classical
  let W := P.ordinates.image (fun u => u-t)
  have hsep : IsOneSeparated W := by
    intro x hx y hy hxy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := by intro he; exact hxy (by rw [he])
    simpa only [sub_sub_sub_cancel_right] using P.ordinates_oneSeparated u hu v hv huv
  have hRange : ∀ x ∈ W, -P.T ≤ x ∧ x ≤ P.T := by
    intro x hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    exact abs_le.mp (P.difference_abs_le_height ht hu)
  have hh := ivicSixth_sum_real_window_sixth_le W hsep (ivicSixthExcess U)
    (continuous_ivicSixthExcess U) (ivicSixthExcess_nonneg U)
    hH (by linarith [P.T_pos] : -P.T ≤ P.T) hRange
  dsimp only [W] at hh
  rw [Finset.sum_image (fun u _ v _ huv => by linarith)] at hh
  simpa only [show -P.T-H = -(P.T+H) by ring] using hh

end TaoTrudgianYang2025
