import Dubon2026.GammaRatioAmplitude
import TaoTrudgianYang2025.ZetaSquareGammaInverse

/-! # Uniform exponential reciprocal-Gamma growth on a genuine positive strip -/

namespace Dubon2026

open Complex
open scoped ComplexConjugate

noncomputable section

/-- The already proved reflection estimate gives a height-uniform reciprocal Gamma bound on the quarter line. -/
theorem norm_inv_Gamma_quarter_le (t : ℝ) :
    ‖(Gamma (gammaVerticalPoint (1 / 4) t))⁻¹‖ ≤
      (Real.Gamma (3 / 4) / Real.pi) * Real.exp (Real.pi * |t|) := by
  have h := TaoTrudgianYang2025.norm_inv_gamma_critical_half_le (2 * t)
  have he : RiemannZeta.GuthMaynard.afeCriticalPoint (2 * t) / 2 =
      gammaVerticalPoint (1 / 4) t := by
    unfold RiemannZeta.GuthMaynard.afeCriticalPoint gammaVerticalPoint
    push_cast
    ring
  rw [he] at h
  convert h using 1
  congr 2
  rw [abs_mul]
  norm_num
  ring

/-- The genuine reciprocal Gamma has one fixed exponential bound throughout each strip [1/4,B] at positive height. -/
theorem norm_inv_Gamma_strip_pos_le {B u t : ℝ} (hu : 1 / 4 ≤ u) (hB : u ≤ B) (ht : 1 ≤ t) :
    ‖(Gamma (gammaVerticalPoint u t))⁻¹‖ ≤
      (Real.exp ((4 + B) * (B - 1 / 4)) * (Real.Gamma (3 / 4) / Real.pi)) *
        Real.exp (Real.pi * t) := by
  have hu0 : 0 < u := by linarith
  have hratio := norm_reflectedGammaRatio_le (show (0 : ℝ) < 1 / 4 by norm_num) hu0 ht
  have hpow : t ^ ((1 / 4 : ℝ) - u) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
  have hconst : Real.exp ((4 + max (1 / 4) u) * |1 / 4 - u|) ≤
      Real.exp ((4 + B) * (B - 1 / 4)) := by
    apply Real.exp_le_exp.mpr
    rw [max_eq_right hu, abs_of_nonpos (by linarith)]
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hratio' : ‖reflectedGammaRatio (1 / 4) u t‖ ≤ Real.exp ((4 + B) * (B - 1 / 4)) := by
    apply hratio.trans
    calc
      _ ≤ Real.exp ((4 + B) * (B - 1 / 4)) * 1 :=
        mul_le_mul hconst hpow (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
      _ = _ := mul_one _
  have hq : Gamma (gammaVerticalPoint (1 / 4) t) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by rw [gammaVerticalPoint_re]; norm_num)
  have he : ‖(Gamma (gammaVerticalPoint u t))⁻¹‖ =
      ‖reflectedGammaRatio (1 / 4) u t‖ * ‖(Gamma (gammaVerticalPoint (1 / 4) t))⁻¹‖ := by
    rw [norm_reflectedGammaRatio_eq, norm_inv, norm_inv]
    field_simp [norm_ne_zero_iff.mpr hq]
  rw [he]
  have hqbound := norm_inv_Gamma_quarter_le t
  rw [abs_of_nonneg (by linarith : 0 ≤ t)] at hqbound
  calc
    _ ≤ Real.exp ((4 + B) * (B - 1 / 4)) *
        ((Real.Gamma (3 / 4) / Real.pi) * Real.exp (Real.pi * t)) :=
      mul_le_mul hratio' hqbound (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- Conjugation supplies the same actual reciprocal Gamma bound at both signs of the height. -/
theorem norm_inv_Gamma_strip_le {B u t : ℝ} (hu : 1 / 4 ≤ u) (hB : u ≤ B) (ht : 1 ≤ |t|) :
    ‖(Gamma (gammaVerticalPoint u t))⁻¹‖ ≤
      (Real.exp ((4 + B) * (B - 1 / 4)) * (Real.Gamma (3 / 4) / Real.pi)) *
        Real.exp (Real.pi * |t|) := by
  rcases le_total 0 t with ht0 | ht0
  · simpa only [abs_of_nonneg ht0] using
      norm_inv_Gamma_strip_pos_le hu hB (by simpa only [abs_of_nonneg ht0] using ht)
  · have hh := norm_inv_Gamma_strip_pos_le hu hB
      (show 1 ≤ -t by simpa only [abs_of_nonpos ht0] using ht)
    simpa only [gammaVerticalPoint_neg, Gamma_conj, norm_inv, norm_conj,
      abs_of_nonpos ht0] using hh

end
end Dubon2026
