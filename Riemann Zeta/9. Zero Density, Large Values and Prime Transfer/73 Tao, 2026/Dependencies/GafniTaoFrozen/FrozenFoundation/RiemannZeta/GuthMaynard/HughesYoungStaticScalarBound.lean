import RiemannZeta.GuthMaynard.HughesYoungCentralDifferentiation

open Complex

noncomputable section

namespace RiemannZeta.GuthMaynard

/-! # Elementary bound for the localized Hughes--Young scalar -/

/-- The static Hughes--Young localization factor retains the two
critical-line weights exactly.  This isolated version keeps the quantitative
central-contour chain independent of the later global moment assembly. -/
theorem norm_hughesYoungLocalizedStaticScalar_eq_coefficients_mul_rpow
    {T : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungLocalizedStaticScalar T h k‖ =
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        (h : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-(1 / 2 : ℝ)) *
          (1 / Real.pi) := by
  have hlogh :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (h : ℝ)‖ =
        (h : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hh)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hh)]
    norm_num
  have hlogk :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (k : ℝ)‖ =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hk)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
    norm_num
  unfold hughesYoungLocalizedStaticScalar
  simp only [norm_mul, hlogh, hlogk, norm_div, norm_one, norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

end RiemannZeta.GuthMaynard
