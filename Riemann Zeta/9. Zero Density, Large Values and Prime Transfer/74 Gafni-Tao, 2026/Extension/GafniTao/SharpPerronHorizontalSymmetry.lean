import GafniTao.SharpPerronPhysicalHorizontal
import PrimeNumberTheoremAnd.ZetaConj

/-!
# Conjugate Perron horizontal edge

Complex conjugation transfers the selected positive-height estimate to the
negative edge without a second zero-selection argument.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

theorem norm_riemannZeta_logDeriv_conj (s : ℂ) :
    ‖deriv riemannZeta (starRingEnd ℂ s) /
        riemannZeta (starRingEnd ℂ s)‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ := by
  have h := logDerivZeta_conj s
  change deriv riemannZeta (starRingEnd ℂ s) /
      riemannZeta (starRingEnd ℂ s) =
        starRingEnd ℂ (deriv riemannZeta s / riemannZeta s) at h
  rw [h, norm_conj]

theorem norm_riemannZeta_logDeriv_negative_horizontal_le
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2) 2)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    ‖deriv riemannZeta ((σ : ℂ) - (R : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) - (R : ℂ) * Complex.I)‖ ≤
      (4 / 7 : ℝ) *
        (202 * sharpLandauPartialFractionConstant +
          (7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
            sharpLandauMassConstant) * Real.log T ^ 2 := by
  have hconj : starRingEnd ℂ
      ((σ : ℂ) + (R : ℂ) * Complex.I) =
      (σ : ℂ) - (R : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [← hconj, norm_riemannZeta_logDeriv_conj]
  exact norm_riemannZeta_logDeriv_positive_horizontal_le hT hR hσ hfar

end GafniTao
