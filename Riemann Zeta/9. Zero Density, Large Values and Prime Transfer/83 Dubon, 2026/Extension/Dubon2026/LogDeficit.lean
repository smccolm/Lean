import Dubon2026.ExponentialTailIntegral
import Dubon2026.UniformVerticalSublevel

/-! # Uniform logarithmic deficits derived from actual small-value bounds -/

namespace Dubon2026

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Positive logarithmic deficit below the scale `η * exp (-K * R)`, divided by `K`. -/
def logDeficit (K : ℕ) (η R : ℝ) (w : ℂ) : ℝ :=
  max 0 ((Real.log η - Real.log ‖w‖) / K - R)

theorem integrable_logDeficit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℂ} (hf : Integrable (fun x => Real.log ‖f x‖) μ)
    (K : ℕ) (η R : ℝ) : Integrable (fun x => logDeficit K η R (f x)) μ :=
  (integrable_const (0 : ℝ)).sup
    ((((integrable_const (Real.log η)).sub hf).div_const K).sub (integrable_const R))

theorem logDeficit_level_subset {K : ℕ} (hK : 0 < K) {η R t : ℝ} (hη : 0 < η)
    (ht : 0 < t) {w : ℂ} (hw : w ≠ 0) (hlevel : t < logDeficit K η R w) :
    ‖w‖ ≤ η * Real.exp (-(R + t)) ^ K := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hx : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hlevel' : t < (Real.log η - Real.log ‖w‖) / K - R :=
    (lt_max_iff.mp hlevel).resolve_left (not_lt_of_ge ht.le)
  have hmul : (R + t) * (K : ℝ) < Real.log η - Real.log ‖w‖ :=
    (lt_div_iff₀ hk).mp (by linarith)
  have hlog : Real.log (η * Real.exp (-(R + t)) ^ K) =
      Real.log η - (K : ℝ) * (R + t) := by
    rw [Real.log_mul hη.ne' (pow_pos (Real.exp_pos _) K).ne', Real.log_pow, Real.log_exp]
    ring
  apply (Real.log_le_log_iff hx (mul_pos hη (pow_pos (Real.exp_pos _) K))).mp
  rw [hlog]
  nlinarith

theorem integral_logDeficit_le_of_sublevel {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℂ}
    (hf : Integrable (fun x => Real.log ‖f x‖) μ) (hne : ∀ᵐ x ∂μ, f x ≠ 0)
    {K : ℕ} (hK : 0 < K) {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hsub : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      μ {x | ‖f x‖ ≤ η * δ ^ K} ≤ ENNReal.ofReal (C * δ))
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ x, logDeficit K η R (f x) ∂μ ≤ C * Real.exp (-R) := by
  apply integral_le_of_exponential_tail (integrable_logDeficit hf K η R)
    (Filter.Eventually.of_forall (fun x => le_max_left _ _))
    (mul_nonneg hC (Real.exp_pos _).le)
  intro t ht
  have hδ1 : Real.exp (-(R + t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  calc
    μ {x | t < logDeficit K η R (f x)} ≤
        μ {x | ‖f x‖ ≤ η * Real.exp (-(R + t)) ^ K} := by
      apply measure_mono_ae
      filter_upwards [hne] with x hx
      exact fun h => logDeficit_level_subset hK hη ht hx h
    _ ≤ ENNReal.ofReal (C * Real.exp (-(R + t))) := hsub _ (Real.exp_pos _) hδ1
    _ = ENNReal.ofReal (C * Real.exp (-R) * Real.exp (-t)) := by
      rw [neg_add, Real.exp_add, mul_assoc]

theorem integrableOn_verticalFamily_log (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    (z : PrimeTorus N) {left right : ℝ} (hlr : left ≤ right) :
    IntegrableOn (fun t => Real.log ‖verticalFamily a N σ z t‖) (Icc left right) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hlr).mp
    (intervalIntegrable_vertical_log (twistedCoefficients a N z) N σ left right)

theorem exists_uniform_vertical_logDeficit_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    ∃ (K : ℕ) (η C : ℝ), 0 < K ∧ 0 < η ∧ 0 < C ∧
      ∀ z : PrimeTorus N, ∀ R : ℝ, 0 ≤ R →
        (∫ t in Icc (0 : ℝ) 1, logDeficit K η R (verticalFamily a N σ z t)) ≤
          C * Real.exp (-R) := by
  obtain ⟨K, η, C, hK, hη, hC, hb⟩ := exists_uniform_vertical_sublevel_bound hN ha σ
  refine ⟨K, η, C, hK, hη, hC, ?_⟩
  intro z R hR
  apply integral_logDeficit_le_of_sublevel
    (integrableOn_verticalFamily_log a N σ z zero_le_one)
    (ae_restrict_of_ae (verticalFamily_ne_zero_ae hN ha σ z)) hK hη hC.le ?_ hR
  intro δ hδ hδ1
  have hc : Continuous (fun t => ‖verticalFamily a N σ z t‖) :=
    (continuous_iff_continuousAt.mpr
      (fun t => (analyticAt_verticalFamily a N σ z t).continuousAt)).norm
  rw [Measure.restrict_apply (isClosed_le hc continuous_const).measurableSet]
  convert hb z δ hδ hδ1 using 1
  congr 1
  ext t
  exact and_comm

theorem log_truncation_eq_mul_logDeficit {K : ℕ} (hK : 0 < K) {η : ℝ} (hη : 0 < η)
    (R : ℝ) {w : ℂ} (hw : w ≠ 0) :
    Real.log (max ‖w‖ (η * Real.exp (-(K : ℝ) * R))) - Real.log ‖w‖ =
      (K : ℝ) * logDeficit K η R w := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hx : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have he : 0 < η * Real.exp (-(K : ℝ) * R) := mul_pos hη (Real.exp_pos _)
  have hlog : Real.log (η * Real.exp (-(K : ℝ) * R)) = Real.log η - (K : ℝ) * R := by
    rw [Real.log_mul hη.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hmax : Real.log (max ‖w‖ (η * Real.exp (-(K : ℝ) * R))) =
      max (Real.log ‖w‖) (Real.log η - (K : ℝ) * R) := by
    rcases le_total ‖w‖ (η * Real.exp (-(K : ℝ) * R)) with h | h
    · rw [max_eq_right h, max_eq_right (hlog ▸ Real.log_le_log hx h), hlog]
    · rw [max_eq_left h, max_eq_left (hlog ▸ Real.log_le_log he h)]
  rw [hmax, logDeficit, mul_max_of_nonneg _ _ hk.le, mul_zero]
  have hdiv : (K : ℝ) * ((Real.log η - Real.log ‖w‖) / K - R) =
      Real.log η - (K : ℝ) * R - Real.log ‖w‖ := by field_simp; ring
  rw [hdiv, ← max_sub_sub_right, sub_self]

end

end Dubon2026
