import TaoTrudgianYang2025.BourgainFourthMoment
import TaoTrudgianYang2025.PointMeanLemmaThreeTail

/-!
# Genuine zeta-amplitude bands

The amplitude interval is left closed and right open. Its spatial support
is a closed symmetric interval, which does not change its Lebesgue mass
relative to the corresponding open interval. The measure estimate uses
the proved fourth moment, not a supplied superlevel estimate.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace TaoTrudgianYang2025

/-- A spatially truncated dyadic amplitude band of the actual zeta norm. -/
def bourgainZetaBand (T V : ℝ) : Set ℝ :=
  Icc (-T) T ∩ {t | V ≤ zetaMomentCriticalNorm t ∧ zetaMomentCriticalNorm t < 2*V}

theorem mem_bourgainZetaBand (T V t : ℝ) :
    t ∈ bourgainZetaBand T V ↔
      -T ≤ t ∧ t ≤ T ∧ V ≤ zetaMomentCriticalNorm t ∧
        zetaMomentCriticalNorm t < 2*V := by
  simp only [bourgainZetaBand, mem_inter_iff, mem_Icc, mem_setOf_eq]
  tauto

theorem bourgainZetaBand_subset_Icc (T V : ℝ) :
    bourgainZetaBand T V ⊆ Icc (-T) T :=
  inter_subset_left

theorem measurableSet_bourgainZetaBand (T V : ℝ) :
    MeasurableSet (bourgainZetaBand T V) := by
  exact measurableSet_Icc.inter ((measurableSet_le measurable_const
    continuous_zetaMomentCriticalNorm.measurable).inter
    (measurableSet_lt continuous_zetaMomentCriticalNorm.measurable measurable_const))

theorem bourgainZetaBand_measure_lt_top (T V : ℝ) :
    volume (bourgainZetaBand T V) < ⊤ :=
  lt_of_le_of_lt (measure_mono (bourgainZetaBand_subset_Icc T V)) measure_Icc_lt_top

/-- The fourth-power mass of a genuine band is bounded by the actual
fourth-moment integral on its spatial support. -/
theorem bourgainZetaBand_fourth_mass_le {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V^4 * volume.real (bourgainZetaBand T V) ≤
      ∫ t in -T..T, zetaMomentCriticalNorm t^4 := by
  have hi : IntegrableOn (fun t => zetaMomentCriticalNorm t^4) (Icc (-T) T) :=
    (continuous_zetaMomentCriticalNorm.pow 4).continuousOn.integrableOn_Icc
  have hc : IntegrableOn (fun _ : ℝ => V^4) (bourgainZetaBand T V) :=
    integrableOn_const (bourgainZetaBand_measure_lt_top T V).ne
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ _ in bourgainZetaBand T V, V^4 := by simp [mul_comm]
    _ ≤ ∫ t in bourgainZetaBand T V, zetaMomentCriticalNorm t^4 :=
      setIntegral_mono_on hc (hi.mono_set (bourgainZetaBand_subset_Icc T V))
        (measurableSet_bourgainZetaBand T V) (fun t ht =>
          pow_le_pow_left₀ hV ((mem_bourgainZetaBand T V t).mp ht).2.2.1 4)
    _ ≤ _ := setIntegral_mono_set hi
      (Filter.Eventually.of_forall (fun _ => by positivity))
      (Filter.Eventually.of_forall (bourgainZetaBand_subset_Icc T V))

/-- Uniform fourth-moment control of every actual amplitude band. -/
theorem bourgainZetaBand_fourth_bound {η : ℝ} (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T V : ℝ, T₀ ≤ T → 0 ≤ V →
      V^4 * volume.real (bourgainZetaBand T V) ≤ C*T^(1+η) := by
  obtain ⟨C, T₀, hC, hT₀, hfourth⟩ := zeta_fourth_symmetric hη
  exact ⟨C, T₀, hC, hT₀, fun T V hT hV =>
    (bourgainZetaBand_fourth_mass_le (by linarith) hV).trans (hfourth T hT)⟩

/-- A uniform linear growth majorant for the actual critical-line norm. -/
theorem exists_zetaMomentCriticalNorm_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      zetaMomentCriticalNorm t ≤ C*(1+|t|) := by
  obtain ⟨D, hD, hbound⟩ := exists_zetaMomentCriticalNorm_sq_le_quadratic
  refine ⟨Real.sqrt D, Real.sqrt_pos.mpr hD, ?_⟩
  intro t
  have hs : (Real.sqrt D)^2 = D := Real.sq_sqrt hD.le
  have ha : 0 ≤ |t| := abs_nonneg t
  have ht : |t|^2 = t^2 := sq_abs t
  have hp : 0 ≤ Real.sqrt D*(1+|t|) := by positivity
  have hn : 0 ≤ zetaMomentCriticalNorm t := norm_nonneg _
  have hm := hbound t
  nlinarith [sq_nonneg (zetaMomentCriticalNorm t - Real.sqrt D*(1+|t|)),
    mul_nonneg hD.le ha]

end TaoTrudgianYang2025
