import TaoTrudgianYang2025.ZetaSquareGammaPhase

/-!
# A uniform inverse bound for the actual Gamma normalization

Euler reflection and the positive-line Gamma integral give the deliberately
coarse exponential bound needed on the far Gaussian contour. In contrast
to a fixed-height continuity argument, the constant is uniform in height.
-/

noncomputable section

open Complex
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem norm_complex_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have hraw : ‖(2 : ℂ) * Complex.sin z‖ ≤
      Real.exp z.im + Real.exp (-z.im) := by
    rw [Complex.two_sin]
    calc
      _ = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ := by simp
      _ ≤ ‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖ := norm_sub_le _ _
      _ = _ := by rw [Complex.norm_exp, Complex.norm_exp]; simp
  simp only [norm_mul, Complex.norm_ofNat] at hraw
  have hplus := Real.exp_le_exp.mpr (le_abs_self z.im)
  have hminus := Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith

theorem norm_inv_gamma_critical_half_le (t : ℝ) :
    ‖(Complex.Gamma (afeCriticalPoint t / 2))⁻¹‖ ≤
      (Real.Gamma (3 / 4) / Real.pi) * Real.exp (Real.pi * |t| / 2) := by
  let p := afeCriticalPoint t / 2
  have hp : 0 < p.re := by norm_num [p, afeCriticalPoint]
  have hq : 0 < (1 - p).re := by norm_num [p, afeCriticalPoint]
  have hGp : Complex.Gamma p ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hp
  have hGq : Complex.Gamma (1 - p) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hq
  have href := Complex.Gamma_mul_Gamma_one_sub p
  have hsin : Complex.sin ((Real.pi : ℂ) * p) ≠ 0 := by
    intro h
    rw [h, div_zero] at href
    exact mul_ne_zero hGp hGq href
  have hid : (Complex.Gamma p)⁻¹ =
      Complex.Gamma (1 - p) * Complex.sin ((Real.pi : ℂ) * p) / (Real.pi : ℂ) := by
    have h := (eq_div_iff hsin).mp href
    rw [mul_comm (Real.pi : ℂ) p] at h
    field_simp
    linear_combination -h
  have hg : ‖Complex.Gamma (1 - p)‖ ≤ Real.Gamma (3 / 4) := by
    convert norm_Gamma_le_realGamma_re hq using 1
    norm_num [p, afeCriticalPoint]
  have hs : ‖Complex.sin ((Real.pi : ℂ) * p)‖ ≤ Real.exp (Real.pi * |t| / 2) := by
    have h := norm_complex_sin_le_exp_abs_im ((Real.pi : ℂ) * p)
    simpa [p, afeCriticalPoint, abs_mul, abs_div, abs_of_pos Real.pi_pos, mul_div_assoc] using h
  change ‖(Complex.Gamma p)⁻¹‖ ≤ _
  rw [hid, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ (Real.Gamma (3 / 4) * Real.exp (Real.pi * |t| / 2)) / Real.pi := by gcongr
    _ = _ := by ring

theorem exists_norm_inv_gammaReal_critical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(Complex.Gammaℝ (afeCriticalPoint t))⁻¹‖ ≤ C * Real.exp (Real.pi * |t| / 2) := by
  let P : ℝ := Real.pi ^ (-(1 / 4 : ℝ))
  have hP : 0 < P := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨P⁻¹ * (Real.Gamma (3 / 4) / Real.pi),
    mul_pos (inv_pos.mpr hP) (div_pos (Real.Gamma_pos_of_pos (by norm_num)) Real.pi_pos), ?_⟩
  intro t
  have hn : ‖Complex.Gammaℝ (afeCriticalPoint t)‖ = P * ‖Complex.Gamma (afeCriticalPoint t / 2)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    norm_num [afeCriticalPoint, P]
  rw [norm_inv, hn, mul_inv_rev]
  have h := mul_le_mul_of_nonneg_left (norm_inv_gamma_critical_half_le t) (inv_nonneg.mpr hP.le)
  rw [norm_inv] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- One height-independent constant for the exact normalization used by
the source identity, including height zero and both signs of the height. -/
theorem exists_norm_inv_zetaSquareGammaNormalization_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(zetaSquareGammaNormalization t)⁻¹‖ ≤ C * Real.exp (Real.pi * |t|) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_inv_gammaReal_critical_le
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro t
  rw [zetaSquareGammaNormalization, mul_inv_rev, norm_mul]
  have hminus := hbound (-t)
  rw [abs_neg] at hminus
  calc
    _ ≤ (C * Real.exp (Real.pi * |t| / 2)) * (C * Real.exp (Real.pi * |t| / 2)) :=
      mul_le_mul hminus (hbound t) (norm_nonneg _) (by positivity)
    _ = C ^ 2 * (Real.exp (Real.pi * |t| / 2) * Real.exp (Real.pi * |t| / 2)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end TaoTrudgianYang2025
