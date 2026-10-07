import Dubon2026.GammaRieszWindow

/-! # A fixed compact-height majorant for the genuine Riesz Gamma kernel -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- The literal integral of the genuine Gamma amplitude up to the fixed admissible height. -/
def gammaRieszCompactMass (k r : ℝ) : ℝ :=
  ∫ t in 0..gammaRieszBaseHeight k,
    doubleGammaAmplitude (1 - gammaRieszLine r) (gammaRieszLine r + r + 1)
      (k - gammaRieszLine r) (gammaRieszLine r + k - 1) t

/-- The actual modulus separates into its exact real Mellin power and genuine Gamma amplitude. -/
theorem norm_gammaRieszIntegrand_eq {x : ℝ} (hx : 0 < x) (k r t : ℝ) :
    ‖gammaRieszIntegrand k r x t‖ = x ^ gammaRieszLine r *
      doubleGammaAmplitude (1 - gammaRieszLine r) (gammaRieszLine r + r + 1)
        (k - gammaRieszLine r) (gammaRieszLine r + k - 1) t := by
  rw [gammaRieszIntegrand_eq hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hx _)]
  have he : ‖Complex.exp (I * ((Real.log x * t : ℝ) : ℂ))‖ = 1 := by simp [Complex.norm_exp]
  simp only [norm_mul, he, one_mul, doubleGammaAmplitude]

/-- The genuine compact amplitude mass is nonnegative. -/
theorem gammaRieszCompactMass_nonneg (k r : ℝ) : 0 ≤ gammaRieszCompactMass k r := by
  apply intervalIntegral.integral_nonneg (by linarith [(gammaRieszBaseHeight_properties k).1])
  intro t _
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The compact-height contribution is uniformly bounded by its genuine fixed amplitude integral. -/
theorem norm_gammaRieszIntegrand_compact_integral_le {x : ℝ} (hx : 0 < x) (k r : ℝ) :
    ‖∫ t in 0..gammaRieszBaseHeight k, gammaRieszIntegrand k r x t‖ ≤
      gammaRieszCompactMass k r * x ^ gammaRieszLine r := by
  calc
    _ ≤ ∫ t in 0..gammaRieszBaseHeight k, ‖gammaRieszIntegrand k r x t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith [(gammaRieszBaseHeight_properties k).1])
    _ = _ := by
      rw [intervalIntegral.integral_congr (fun t _ => norm_gammaRieszIntegrand_eq hx k r t),
        intervalIntegral.integral_const_mul]
      exact mul_comm _ _

end
end Dubon2026
