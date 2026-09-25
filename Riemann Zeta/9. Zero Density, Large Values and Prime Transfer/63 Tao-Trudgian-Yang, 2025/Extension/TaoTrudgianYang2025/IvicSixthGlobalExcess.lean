import TaoTrudgianYang2025.IvicSixthExcessSource
import TaoTrudgianYang2025.BourgainFourthMoment

/-! Actual restricted sixth moments on full symmetric height intervals. -/

noncomputable section
open Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem ivicSixthExcess_antitone_threshold {U V : ℝ} (hUV : U ≤ V) (t : ℝ) :
    ivicSixthExcess V t ≤ ivicSixthExcess U t :=
  max_le_max le_rfl (sub_le_sub_left hUV _)

theorem ivicSixthExcess_neg (U t : ℝ) :
    ivicSixthExcess U (-t) = ivicSixthExcess U t := by
  simp only [ivicSixthExcess,zetaMomentCriticalNorm_neg]

/-- A moving threshold gives one continuous majorant, independent of the
eventual terminal height, so its compact initial integral is uniform. -/
def ivicSixthMovingExcess (η t : ℝ) : ℝ :=
  ivicSixthExcess ((2*|t|)^(11/72+η)) t

theorem continuous_ivicSixthMovingExcess {η : ℝ} (hη : 0 ≤ η) :
    Continuous (ivicSixthMovingExcess η) := by
  apply continuous_const.max
  exact continuous_zetaMomentCriticalNorm.sub
    ((continuous_abs.const_mul 2).rpow_const (fun _ => Or.inr (by linarith)))

theorem exists_ivicSixthMovingExcess_dyadic {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 40000 ≤ B ∧ ∀ H : ℝ, B ≤ H →
      (∫ t in H..2*H, ivicSixthMovingExcess η t^6) ≤ H^(1+η) := by
  obtain ⟨B,hB,hbound⟩ := exists_ivicSixthExcess_dyadic_bound hη
  refine ⟨B,hB,?_⟩
  intro H hH
  have hH0 : 0 < H := by linarith
  apply le_trans _ (hbound H (H^(11/72+η)) hH le_rfl)
  apply intervalIntegral.integral_mono_on (by linarith)
    ((continuous_ivicSixthMovingExcess hη.le).pow 6 |>.intervalIntegrable _ _)
    ((continuous_ivicSixthExcess _).pow 6 |>.intervalIntegrable _ _)
  intro t ht
  apply pow_le_pow_left₀ (ivicSixthExcess_nonneg _ _) _ 6
  apply ivicSixthExcess_antitone_threshold
  exact Real.rpow_le_rpow hH0.le (by linarith [le_abs_self t,ht.1]) (by linarith)

theorem exists_ivicSixthExcess_zero_moment {η : ℝ} (hη : 0 < η) :
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T U : ℝ, B ≤ T →
      (2*T)^(11/72+η) ≤ U →
      (∫ t in 0..T, ivicSixthExcess U t^6) ≤ C*T^(1+η) := by
  obtain ⟨B,hB,hdyad⟩ := exists_ivicSixthMovingExcess_dyadic hη
  obtain ⟨C,hC,hglobal⟩ := integral_zero_le_of_dyadic
    (fun t => ivicSixthMovingExcess η t^6)
    ((continuous_ivicSixthMovingExcess hη.le).pow 6)
    (fun _ => pow_nonneg (ivicSixthExcess_nonneg _ _) _)
    (by linarith : 1 ≤ 1+η) (by linarith : 1 ≤ B)
    (by norm_num : (0:ℝ) ≤ 1) (by simpa only [one_mul] using hdyad)
  refine ⟨C,B,hC,hB,?_⟩
  intro T U hT hU
  have hT0 : 0 < T := by linarith
  apply le_trans _ (hglobal T hT)
  apply intervalIntegral.integral_mono_on hT0.le
    ((continuous_ivicSixthExcess U).pow 6 |>.intervalIntegrable _ _)
    ((continuous_ivicSixthMovingExcess hη.le).pow 6 |>.intervalIntegrable _ _)
  intro t ht
  apply pow_le_pow_left₀ (ivicSixthExcess_nonneg _ _) _ 6
  apply ivicSixthExcess_antitone_threshold
  apply le_trans _ hU
  rw [abs_of_nonneg ht.1]
  exact Real.rpow_le_rpow (mul_nonneg (by norm_num) ht.1)
    (by linarith [ht.2]) (by linarith)

theorem exists_ivicSixthExcess_symmetric_moment {η : ℝ} (hη : 0 < η) :
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T U : ℝ, B ≤ T →
      (2*T)^(11/72+η) ≤ U →
      (∫ t in -T..T, ivicSixthExcess U t^6) ≤ C*T^(1+η) := by
  obtain ⟨C,B,hC,hB,hzero⟩ := exists_ivicSixthExcess_zero_moment hη
  refine ⟨2*C,B,by positivity,hB,?_⟩
  intro T U hT hU
  have hi := (continuous_ivicSixthExcess U).pow 6
  have heven : (∫ t in -T..0, ivicSixthExcess U t^6) =
      ∫ t in 0..T, ivicSixthExcess U t^6 := by
    have hs := intervalIntegral.integral_comp_neg (fun t => ivicSixthExcess U t^6)
      (a := (0:ℝ)) (b := T)
    simpa only [ivicSixthExcess_neg,neg_zero] using hs.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (-T) 0)
    (hi.intervalIntegrable 0 T),heven]
  have hz := hzero T U hT hU
  nlinarith

end TaoTrudgianYang2025
