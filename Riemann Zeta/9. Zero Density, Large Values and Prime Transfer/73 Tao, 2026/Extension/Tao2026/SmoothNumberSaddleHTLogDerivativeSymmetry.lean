import Tao2026.SmoothNumberSaddleHTLogDerivativeLandau
import GafniTao.SharpPerronHorizontalSymmetry

/-!
# Symmetric VK logarithmic-derivative bounds

Complex conjugation transfers the arbitrary-positive-height Landau estimate
to negative height.  The final theorem packages both signs using the
absolute ordinate itself as the frozen Landau scale, eliminating the
unit-interval bookkeeping from later contour applications.
-/

open Complex Set
open RiemannZeta.GuthMaynard

namespace Tao2026

noncomputable section

/-- Conjugate form of the VK-separated Landau estimate. -/
theorem norm_riemannZeta_logDeriv_negative_height_le_of_vK
    {c H eta T sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hT : 8 ≤ T) (hHeight : H ≤ 3 * T) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * T))
    (hR : R ∈ Set.Icc T (T + 1))
    (hSigmaIcc : sigma ∈ Set.Icc (1 / 2) 2)
    (hSigma : 1 - eta ≤ sigma) :
    ‖deriv riemannZeta ((sigma : ℂ) - (R : ℂ) * Complex.I) /
        riemannZeta ((sigma : ℂ) - (R : ℂ) * Complex.I)‖ ≤
      (4 / 7 : ℝ) *
        (GafniTao.sharpLandauPartialFractionConstant *
            Real.log (200 * T ^ (3 : ℝ)) +
          (7 / (4 * eta)) * GafniTao.sharpLandauZeroMass T hT) := by
  have hconj : starRingEnd ℂ
      ((sigma : ℂ) + (R : ℂ) * Complex.I) =
      (sigma : ℂ) - (R : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [← hconj, GafniTao.norm_riemannZeta_logDeriv_conj]
  exact norm_riemannZeta_logDeriv_positive_height_le_of_vK
    hZeroFree hT hHeight heta hWidth hR hSigmaIcc hSigma

/-- Sign-uniform physical logarithmic-derivative bound.  The absolute
ordinate is used directly as the Landau scale. -/
theorem norm_riemannZeta_logDeriv_abs_height_le_of_vK
    {c H eta sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hR : 8 ≤ |R|) (hHeight : H ≤ 3 * |R|) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * |R|))
    (hSigmaIcc : sigma ∈ Set.Icc (1 / 2) 2)
    (hSigma : 1 - eta ≤ sigma) :
    ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      (4 / 7 : ℝ) *
        (GafniTao.sharpLandauPartialFractionConstant *
            Real.log (200 * |R| ^ (3 : ℝ)) +
          (7 / (4 * eta)) *
            GafniTao.sharpLandauZeroMass |R| hR) := by
  have hIcc : |R| ∈ Set.Icc |R| (|R| + 1) := ⟨le_rfl, by linarith⟩
  by_cases hRnonneg : 0 ≤ R
  · have hT : 8 ≤ R := by simpa [abs_of_nonneg hRnonneg] using hR
    have hHeight' : H ≤ 3 * R := by
      simpa [abs_of_nonneg hRnonneg] using hHeight
    have hWidth' : 2 * eta ≤
        c / GafniTao.vinogradovKorobovDenominator (3 * R) := by
      simpa [abs_of_nonneg hRnonneg] using hWidth
    have hIcc' : R ∈ Set.Icc R (R + 1) := ⟨le_rfl, by linarith⟩
    have h := norm_riemannZeta_logDeriv_positive_height_le_of_vK
      hZeroFree hT hHeight' heta hWidth' hIcc' hSigmaIcc hSigma
    simpa only [abs_of_nonneg hRnonneg] using h
  · have hRneg : R < 0 := lt_of_not_ge hRnonneg
    have hpoint :
        ((sigma : ℂ) + (R : ℂ) * Complex.I) =
          (sigma : ℂ) - ((|R| : ℝ) : ℂ) * Complex.I := by
      rw [abs_of_neg hRneg]
      push_cast
      ring
    rw [hpoint]
    exact norm_riemannZeta_logDeriv_negative_height_le_of_vK
      hZeroFree hR hHeight heta hWidth hIcc hSigmaIcc hSigma

/-- A source-friendly logarithmic form of the sign-uniform estimate. -/
theorem norm_riemannZeta_logDeriv_abs_height_le_log_of_vK
    {c H eta sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hR : 8 ≤ |R|) (hHeight : H ≤ 3 * |R|) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * |R|))
    (hSigmaIcc : sigma ∈ Set.Icc (1 / 2) 2)
    (hSigma : 1 - eta ≤ sigma) :
    ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      (4 / 7 : ℝ) *
        (202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / (4 * eta)) * GafniTao.sharpLandauMassConstant) *
            Real.log |R| := by
  have hraw := norm_riemannZeta_logDeriv_abs_height_le_of_vK
    hZeroFree hR hHeight heta hWidth hSigmaIcc hSigma
  have hlog := GafniTao.log_two_hundred_mul_rpow_le hR
  have hmass := GafniTao.sharpLandauZeroMass_le_log hR
  have hA : 0 ≤ GafniTao.sharpLandauPartialFractionConstant :=
    GafniTao.sharpLandauPartialFractionConstant_pos.le
  have hetaCoeff : 0 ≤ 7 / (4 * eta) := by positivity
  calc
    ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      (4 / 7 : ℝ) *
        (GafniTao.sharpLandauPartialFractionConstant *
            Real.log (200 * |R| ^ (3 : ℝ)) +
          (7 / (4 * eta)) *
            GafniTao.sharpLandauZeroMass |R| hR) := hraw
    _ ≤ (4 / 7 : ℝ) *
        (GafniTao.sharpLandauPartialFractionConstant *
            (202 * Real.log |R|) +
          (7 / (4 * eta)) *
            (GafniTao.sharpLandauMassConstant * Real.log |R|)) := by
      gcongr
    _ = (4 / 7 : ℝ) *
        (202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / (4 * eta)) * GafniTao.sharpLandauMassConstant) *
            Real.log |R| := by ring

end

end Tao2026
