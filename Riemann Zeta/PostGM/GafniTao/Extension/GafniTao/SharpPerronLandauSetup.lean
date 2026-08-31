import GafniTao.SharpPerronRightEdge
import GafniTao.StrongPNTPrefix

/-!
# A normalized zeta disk for the good-height argument

The disk and constants are aligned with the already kernel-checked Jensen
circle in the frozen Guth--Maynard foundation.  This file supplies the exact
analyticity, centre lower bound, and polynomial majorant needed by the
generic `FinalBound` logarithmic-derivative theorem.
-/

open Complex Set Metric
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

noncomputable def sharpLandauCenter (t : ℝ) : ℂ :=
  2 + I * (t + 1 / 2)

noncomputable def sharpLandauMap (t : ℝ) (w : ℂ) : ℂ :=
  sharpLandauCenter t + (7 / 4 : ℝ) * w

noncomputable def sharpLandauNormalized (t : ℝ) (w : ℂ) : ℂ :=
  (riemannZeta (sharpLandauCenter t))⁻¹ *
    riemannZeta (sharpLandauMap t w)

theorem sharpLandauCenter_lower_bound (t : ℝ) :
    (3 / 5 : ℝ) ≤ ‖riemannZeta (sharpLandauCenter t)‖ := by
  convert euler_product_lower_bound_2 t using 1
  all_goals norm_num [sharpLandauCenter, mul_comm]

theorem sharpLandauCenter_ne_zero (t : ℝ) :
    riemannZeta (sharpLandauCenter t) ≠ 0 := by
  intro h
  have hlower := sharpLandauCenter_lower_bound t
  rw [h, norm_zero] at hlower
  norm_num at hlower

theorem sharpLandau_disk_avoids_one
    {T t : ℝ} (hT : 8 ≤ T) (ht : t ∈ Set.Icc (T - 1) (2 * T)) :
    (1 : ℂ) ∉ Metric.closedBall (sharpLandauCenter t) (7 / 4) := by
  intro h
  rw [Metric.mem_closedBall, Complex.dist_eq] at h
  have him := Complex.abs_im_le_norm ((1 : ℂ) - sharpLandauCenter t)
  have himEq : ((1 : ℂ) - sharpLandauCenter t).im = -(t + 1 / 2) := by
    simp [sharpLandauCenter]
  rw [himEq, abs_neg, abs_of_nonneg (by linarith [ht.1])] at him
  linarith [ht.1]

theorem analyticOnNhd_riemannZeta_sharpLandau_disk
    {T t : ℝ} (hT : 8 ≤ T) (ht : t ∈ Set.Icc (T - 1) (2 * T)) :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall (sharpLandauCenter t) (7 / 4)) := by
  exact analyticOn_riemannZeta.mono (fun s hs => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    subst s
    exact sharpLandau_disk_avoids_one hT ht hs)

theorem norm_riemannZeta_le_on_sharpLandau_disk
    {T t : ℝ} (hT : 8 ≤ T) (ht : t ∈ Set.Icc (T - 1) (2 * T))
    {s : ℂ} (hs : s ∈ Metric.closedBall (sharpLandauCenter t) (7 / 4)) :
    ‖riemannZeta s‖ ≤ 100 * T ^ (3 : ℝ) := by
  apply AnalyticOn.norm_le_of_norm_le_on_sphere le_rfl
      (analyticOnNhd_riemannZeta_sharpLandau_disk hT ht).analyticOn
  · intro z hz
    simpa [sharpLandauCenter, mul_comm] using
      zeta_jensen_sphere_bound T t hT ht z (by simpa [sharpLandauCenter] using hz)
  · exact hs

theorem analyticOnNhd_sharpLandauNormalized
    {T t : ℝ} (hT : 8 ≤ T) (ht : t ∈ Set.Icc (T - 1) (2 * T)) :
    AnalyticOnNhd ℂ (sharpLandauNormalized t)
      (Metric.closedBall (0 : ℂ) 1) := by
  intro w hw
  have hwNorm : ‖w‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hw
  have hmapMem : sharpLandauMap t w ∈
      Metric.closedBall (sharpLandauCenter t) (7 / 4) := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    simp only [sharpLandauMap, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num :
        (0 : ℝ) ≤ 7 / 4)]
    nlinarith
  have hmapAnalytic : AnalyticAt ℂ (sharpLandauMap t) w := by
    unfold sharpLandauMap
    fun_prop
  exact analyticAt_const.mul
    (((analyticOnNhd_riemannZeta_sharpLandau_disk hT ht)
      (sharpLandauMap t w) hmapMem).comp hmapAnalytic)

theorem sharpLandauNormalized_zero (t : ℝ) :
    sharpLandauNormalized t 0 = 1 := by
  rw [sharpLandauNormalized, sharpLandauMap]
  simp only [mul_zero, add_zero]
  exact inv_mul_cancel₀ (sharpLandauCenter_ne_zero t)

/-- A deliberately simple polynomial disk bound; constants are explicit so
that no asymptotic oracle enters the later good-height theorem. -/
theorem norm_sharpLandauNormalized_le
    {T t : ℝ} (hT : 8 ≤ T) (ht : t ∈ Set.Icc (T - 1) (2 * T))
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖sharpLandauNormalized t w‖ ≤ 200 * T ^ (3 : ℝ) := by
  have hT0 : 0 ≤ T := by linarith
  have hmapMem : sharpLandauMap t w ∈
      Metric.closedBall (sharpLandauCenter t) (7 / 4) := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    simp only [sharpLandauMap, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num :
        (0 : ℝ) ≤ 7 / 4)]
    nlinarith
  have hzeta := norm_riemannZeta_le_on_sharpLandau_disk hT ht hmapMem
  have hcenter := sharpLandauCenter_lower_bound t
  have hcenterPos : 0 < ‖riemannZeta (sharpLandauCenter t)‖ :=
    lt_of_lt_of_le (by norm_num) hcenter
  have hinv : ‖(riemannZeta (sharpLandauCenter t))⁻¹‖ ≤ 5 / 3 := by
    rw [norm_inv]
    rw [inv_le_iff_one_le_mul₀ hcenterPos]
    nlinarith
  rw [sharpLandauNormalized, norm_mul]
  have hpow : 0 ≤ T ^ (3 : ℝ) := Real.rpow_nonneg hT0 3
  calc
    ‖(riemannZeta (sharpLandauCenter t))⁻¹‖ *
        ‖riemannZeta (sharpLandauMap t w)‖
        ≤ (5 / 3 : ℝ) * (100 * T ^ (3 : ℝ)) := by
          exact mul_le_mul hinv hzeta (norm_nonneg _) (by norm_num)
    _ ≤ 200 * T ^ (3 : ℝ) := by nlinarith

end GafniTao
