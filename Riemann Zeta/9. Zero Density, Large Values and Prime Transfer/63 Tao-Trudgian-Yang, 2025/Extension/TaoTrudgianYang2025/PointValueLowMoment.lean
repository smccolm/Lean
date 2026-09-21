import TaoTrudgianYang2025.PointValueHighMoment

/-!
# The low-value reduction to the genuine fourth moment

The high-value twelfth moment is already proved. On its complement the
actual twelfth power is at most V^8 times the actual fourth power.
The final full-moment deduction states its remaining fourth-moment input
explicitly; that source theorem is not postulated or declared proved here.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Interval

namespace TaoTrudgianYang2025

theorem zeta_twelfth_low_integral_le_fourth (H V : ℝ) :
    (∫ t in Icc H (2*H) \ pointValueSuperlevel H V, zetaMomentCriticalNorm t^12) ≤
      V^8*(∫ t in Icc H (2*H), zetaMomentCriticalNorm t^4) := by
  have h4 : IntegrableOn (fun t => zetaMomentCriticalNorm t^4) (Icc H (2*H)) :=
    (continuous_zetaMomentCriticalNorm.pow 4).continuousOn.integrableOn_Icc
  have h12 : IntegrableOn (fun t => zetaMomentCriticalNorm t^12) (Icc H (2*H)) :=
    (continuous_zetaMomentCriticalNorm.pow 12).continuousOn.integrableOn_Icc
  have hpoint : ∀ t ∈ Icc H (2*H) \ pointValueSuperlevel H V,
      zetaMomentCriticalNorm t^12 ≤ V^8*zetaMomentCriticalNorm t^4 := by
    intro t ht
    have hlt : zetaMomentCriticalNorm t < V := by
      by_contra hh
      exact ht.2 ⟨ht.1.1,ht.1.2,le_of_not_gt hh⟩
    have hp := pow_le_pow_left₀
      (show 0 ≤ zetaMomentCriticalNorm t from norm_nonneg _) hlt.le 8
    have hm := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ zetaMomentCriticalNorm t^4 by positivity)
    simpa only [← pow_add] using hm
  have hmeas : MeasurableSet (Icc H (2*H) \ pointValueSuperlevel H V) :=
    measurableSet_Icc.diff (measurableSet_pointValueSuperlevel H V)
  calc
    _ ≤ ∫ t in Icc H (2*H) \ pointValueSuperlevel H V,
        V^8*zetaMomentCriticalNorm t^4 :=
      setIntegral_mono_on (h12.mono_set diff_subset)
        ((h4.mono_set diff_subset).const_mul (V^8)) hmeas hpoint
    _ = V^8*(∫ t in Icc H (2*H) \ pointValueSuperlevel H V, zetaMomentCriticalNorm t^4) :=
      integral_const_mul _ _
    _ ≤ V^8*(∫ t in Icc H (2*H), zetaMomentCriticalNorm t^4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_mono_set h4
        (Filter.Eventually.of_forall (fun _ => by positivity))
        (Filter.Eventually.of_forall diff_subset)

theorem zeta_twelfth_integral_le_high_add_fourth {H V : ℝ}
    (hH : 0 ≤ H) :
    (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤
      (∫ t in pointValueSuperlevel H V, zetaMomentCriticalNorm t^12) +
        V^8*(∫ t in H..2*H, zetaMomentCriticalNorm t^4) := by
  have h12 : IntegrableOn (fun t => zetaMomentCriticalNorm t^12) (Icc H (2*H)) :=
    (continuous_zetaMomentCriticalNorm.pow 12).continuousOn.integrableOn_Icc
  have he := setIntegral_diff (measurableSet_pointValueSuperlevel H V) h12
    (pointValueSuperlevel_subset_Icc H V)
  have hlow := zeta_twelfth_low_integral_le_fourth H V
  rw [he] at hlow
  rw [intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc]
  linarith

theorem zeta_twelfth_dyadic_of_fourth
    (hFourth : ∀ η : ℝ, 0 < η → ∃ C H₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η)) :
    ∀ ε : ℝ, 0 < ε → ∃ D H₀ : ℝ, 0 ≤ D ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤ D*H^(2+ε) := by
  intro ε hε
  let η : ℝ := ε/20
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨B,hB,hhigh⟩ := exists_zeta_twelfth_high_integral_le hη
  obtain ⟨C,B₁,hC,hfourth⟩ := hFourth η hη
  refine ⟨1+C,max B B₁,by positivity,?_⟩
  intro H hH hH0
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  have hHB₁ : B₁ ≤ H := (le_max_right _ _).trans hH
  have hH1 : 1 ≤ H := by linarith [hB.trans hHB]
  have hsplit := zeta_twelfth_integral_le_high_add_fourth
    (V := H^(1/8+η)) hH0.le
  have hv : (H^(1/8+η))^8*H^(1+η) = H^(2+9*η) := by
    rw [← Real.rpow_mul_natCast hH0.le,← Real.rpow_add hH0]
    congr 1
    norm_num
    ring
  have he1 : 2+η ≤ 2+ε := by dsimp only [η]; linarith
  have he9 : 2+9*η ≤ 2+ε := by dsimp only [η]; linarith
  calc
    (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤
        (∫ t in pointValueSuperlevel H (H^(1/8+η)), zetaMomentCriticalNorm t^12) +
          (H^(1/8+η))^8*(∫ t in H..2*H, zetaMomentCriticalNorm t^4) := hsplit
    _ ≤ H^(2+η)+(H^(1/8+η))^8*(C*H^(1+η)) := by
      exact add_le_add (hhigh H hHB)
        (mul_le_mul_of_nonneg_left (hfourth H hHB₁ hH0) (by positivity))
    _ = H^(2+η)+C*H^(2+9*η) := by
      rw [mul_left_comm _ C,hv]
    _ ≤ H^(2+ε)+C*H^(2+ε) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hH1 he1)
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 he9) hC)
    _ = (1+C)*H^(2+ε) := by ring

end TaoTrudgianYang2025
