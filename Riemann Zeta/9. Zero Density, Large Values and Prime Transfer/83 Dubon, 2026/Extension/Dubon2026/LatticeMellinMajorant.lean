import Dubon2026.LatticeEpsteinMellin

/-! # Actual positive Mellin majorants for the entire lattice tail -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Set

noncomputable section

/-- At a real parameter the actual positive theta kernel is the coercion of its real norm. -/
theorem latticeThetaMellinKernel_real (z : ℍ) (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    latticeThetaMellinKernel z (σ : ℂ) t =
      (‖latticeThetaMellinKernel z (σ : ℂ) t‖ : ℂ) := by
  rw [norm_latticeThetaMellinKernel z (σ : ℂ) ht, Complex.ofReal_re,
    latticeThetaMellinKernel, Complex.ofReal_mul]
  congr 1
  rw [Complex.ofReal_cpow ht.le, Complex.ofReal_sub, Complex.ofReal_one]

/-- The full norm integral is exactly twice the real completed lattice value in its convergence half-plane. -/
theorem integral_norm_latticeThetaMellinKernel (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    (∫ t : ℝ in Ioi 0, ‖latticeThetaMellinKernel z (σ : ℂ) t‖) =
      2 * (latticeCompletedMellin z (σ : ℂ)).re := by
  have hi := integrableOn_latticeThetaMellinKernel_full z (s := (σ : ℂ)) hσ
  have he : (∫ t : ℝ in Ioi 0, ‖latticeThetaMellinKernel z (σ : ℂ) t‖) =
      (∫ t : ℝ in Ioi 0, latticeThetaMellinKernel z (σ : ℂ) t).re := by
    change _ = RCLike.re (∫ t : ℝ in Ioi 0, latticeThetaMellinKernel z (σ : ℂ) t)
    rw [← integral_re hi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change ‖latticeThetaMellinKernel z (σ : ℂ) t‖ = (latticeThetaMellinKernel z (σ : ℂ) t).re
    conv_rhs => rw [latticeThetaMellinKernel_real z σ ht]
    rfl
  rw [he, latticeCompletedMellin_eq_integral z (s := (σ : ℂ)) hσ]
  simp only [Complex.div_ofNat_re]
  ring

/-- Increasing the real Mellin exponent on t>=1 gives a pointwise majorant for every complex parameter. -/
theorem norm_latticeThetaMellinKernel_le_real (z : ℍ) {s : ℂ} {σ t : ℝ}
    (hs : s.re ≤ σ) (ht : 1 ≤ t) :
    ‖latticeThetaMellinKernel z s t‖ ≤ ‖latticeThetaMellinKernel z (σ : ℂ) t‖ := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [norm_latticeThetaMellinKernel z s ht0,
    norm_latticeThetaMellinKernel z (σ : ℂ) ht0, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht (sub_le_sub_right hs 1))
    (latticeThetaRemainder_nonneg z t)

/-- The actual entire theta tail has a locally uniform parameter bound by a convergent positive lattice value. -/
theorem norm_latticeThetaMellinTail_le_completed (z : ℍ) {s : ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hs : s.re ≤ σ) :
    ‖latticeThetaMellinTail z s‖ ≤ 2 * (latticeCompletedMellin z (σ : ℂ)).re := by
  calc
    _ ≤ ∫ t : ℝ in Ioi 1, ‖latticeThetaMellinKernel z s t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 1, ‖latticeThetaMellinKernel z (σ : ℂ) t‖ := by
      apply integral_mono_ae (integrableOn_latticeThetaMellinKernel z s).norm
        (integrableOn_latticeThetaMellinKernel z (σ : ℂ)).norm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_latticeThetaMellinKernel_le_real z hs (le_of_lt ht)
    _ ≤ ∫ t : ℝ in Ioi 0, ‖latticeThetaMellinKernel z (σ : ℂ) t‖ :=
      setIntegral_mono_set (integrableOn_latticeThetaMellinKernel_full z (s := (σ : ℂ)) hσ).norm
        (ae_of_all _ (fun _ => norm_nonneg _))
        (ae_of_all _ (fun _ ht => lt_trans zero_lt_one ht))
    _ = _ := integral_norm_latticeThetaMellinKernel z hσ

end
end Dubon2026
