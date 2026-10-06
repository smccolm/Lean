import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod

/-! # The exact planar polar factor and radial integrability transfer -/

namespace Dubon2026

open MeasureTheory Set

theorem lintegral_complex_radial {g : ℝ → ℝ} (hg : Continuous g) :
    (∫⁻ z : ℂ, ENNReal.ofReal (g ‖z‖)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r * g r) := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have he : (∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 • ENNReal.ofReal (g ‖Complex.polarCoord.symm p‖)) =
      ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (p.1 * g p.1) := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    dsimp only
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul,
      ← ENNReal.ofReal_mul hp.1.le]
  rw [he]
  change (∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal (p.1 * g p.1) ∂(volume.prod volume)) = _
  rw [setLIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (s := Ioi 0) (t := Ioo (-Real.pi) Real.pi)
    (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * g p.1)) (by fun_prop)]
  have hv : volume (Ioo (-Real.pi) Real.pi) = ENNReal.ofReal (2 * Real.pi) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  simp only [lintegral_const, Measure.restrict_apply_univ, hv]
  rw [lintegral_mul_const _ (by fun_prop), mul_comm]

theorem integrable_complex_radial {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ r, 0 ≤ r → 0 ≤ g r) (hi : IntegrableOn (fun r : ℝ => r * g r) (Ioi 0)) :
    Integrable (fun z : ℂ => g ‖z‖) := by
  have hgn : 0 ≤ᵐ[volume] (fun z : ℂ => g ‖z‖) :=
    Filter.Eventually.of_forall (fun z => hg0 ‖z‖ (norm_nonneg z))
  have hfn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun r : ℝ => r * g r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg hr.le (hg0 r hr.le)
  apply (lintegral_ofReal_ne_top_iff_integrable
    (hg.comp continuous_norm).aestronglyMeasurable hgn).1
  change (∫⁻ z : ℂ, ENNReal.ofReal (g ‖z‖)) ≠ ⊤
  rw [lintegral_complex_radial hg]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hfn).2 hi)

theorem integral_complex_radial {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ r, 0 ≤ r → 0 ≤ g r) :
    (∫ z : ℂ, g ‖z‖) = (2 * Real.pi) * ∫ r : ℝ in Ioi 0, r * g r := by
  have hgn : 0 ≤ᵐ[volume] (fun z : ℂ => g ‖z‖) :=
    Filter.Eventually.of_forall (fun z => hg0 ‖z‖ (norm_nonneg z))
  have hfn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun r : ℝ => r * g r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg hr.le (hg0 r hr.le)
  rw [integral_eq_lintegral_of_nonneg_ae hgn (hg.comp continuous_norm).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hfn (continuous_id.mul hg).aestronglyMeasurable,
    lintegral_complex_radial hg, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end Dubon2026
