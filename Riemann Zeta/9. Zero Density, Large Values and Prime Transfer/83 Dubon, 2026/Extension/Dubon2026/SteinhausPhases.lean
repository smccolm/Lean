import Dubon2026.SteinhausLogScale
import Mathlib.MeasureTheory.Group.Integral

/-! # Absorbing actual complex coefficient phases by product Haar translation -/

namespace Dubon2026

open MeasureTheory

noncomputable section

instance steinhausHaar_isAddHaarMeasure {κ : Type*} [Fintype κ] :
    Measure.IsAddHaarMeasure (steinhausHaar κ) := by
  unfold steinhausHaar
  infer_instance

/-- The circle shift corresponding to the principal argument of a coefficient. -/
def steinhausPhase (d : ℂ) : UnitAddCircle := ((d.arg / (2 * Real.pi) : ℝ) : UnitAddCircle)

theorem steinhaus_coefficient_phase (d : ℂ) (z : UnitAddCircle) :
    d * fourier 1 z = (‖d‖ : ℂ) * fourier 1 (z + steinhausPhase d) := by
  rw [circle_fourier_shift, steinhausPhase, circle_fourier_angle]
  calc
    d * fourier 1 z = ((‖d‖ : ℂ) * Complex.exp ((d.arg : ℂ) * Complex.I)) * fourier 1 z := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    _ = _ := by ring

theorem complex_steinhaus_phase_sum {κ : Type*} [Fintype κ]
    (d : κ → ℂ) (z : κ → UnitAddCircle) :
    (∑ i, d i * fourier 1 (z i)) =
      steinhausSum (fun i => ‖d i‖) (z + fun i => steinhausPhase (d i)) := by
  unfold steinhausSum
  apply Finset.sum_congr rfl
  intro i _
  exact steinhaus_coefficient_phase (d i) (z i)

theorem exists_uniform_complex_steinhaus_log {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (d : κ → ℂ), (∀ i, d i ≠ 0) → 5 ≤ Fintype.card κ →
      steinhausMaxCoefficient (fun i => ‖d i‖) / steinhausMinCoefficient (fun i => ‖d i‖) ≤ K →
      ∀ a : ℂ,
      Integrable (fun z : κ → UnitAddCircle => Real.log ‖a + ∑ i, d i * fourier 1 (z i)‖)
        (steinhausHaar κ) ∧
      Real.log (Real.sqrt (∑ i, ‖d i‖ ^ 2)) - C ≤
        ∫ z : κ → UnitAddCircle, Real.log ‖a + ∑ i, d i * fourier 1 (z i)‖ ∂steinhausHaar κ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_steinhaus_log hK
  refine ⟨C, hC, ?_⟩
  intro κ _ _ d hd hm hcomp a
  obtain ⟨hi, he⟩ := hbound κ (fun i => ‖d i‖) (fun i => norm_pos_iff.mpr (hd i)) hm hcomp a
  simp_rw [complex_steinhaus_phase_sum]
  refine ⟨hi.comp_add_right _, ?_⟩
  rw [integral_add_right_eq_self
    (fun z : κ → UnitAddCircle => Real.log ‖a + steinhausSum (fun i => ‖d i‖) z‖)
    (fun i => steinhausPhase (d i))]
  exact he

end

end Dubon2026
