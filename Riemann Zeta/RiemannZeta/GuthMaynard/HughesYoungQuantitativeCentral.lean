import RiemannZeta.GuthMaynard.HughesYoungCentralDifferentiation
import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds
import RiemannZeta.GuthMaynard.HughesYoungSharpGammaRatio

open Complex MeasureTheory Metric Set
open scoped BigOperators Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative central-source estimates

This file turns the cancellation-preserving Hughes--Young central contour
identity into bounds with constants uniform in the physical height.  The
first step records the exact real-power content of the reduced Mellin
factor; retaining this identity is what produces the summable
`gcd(h,k)/(hk)` weight at the moving pole.
-/

/-- Exact norm of the reduced Mellin factor after the DFI coprime
normalization.  The ordinate variables contribute only phases. -/
theorem norm_inv_reduced_mul_hughesYoungReducedMellinStaticComplex_eq
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (T t c u : ℝ) :
    ‖((((hughesYoungReducedLeft h k : ℕ) : ℂ) *
          (hughesYoungReducedRight h k : ℕ))⁻¹ *
        hughesYoungReducedMellinStaticComplex T t h k
          ((c : ℂ) + (u : ℂ) * I))‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
        (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2) := by
  have ha : 0 < hughesYoungReducedLeft h k :=
    hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k :=
    hughesYoungReducedRight_pos hh hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have haR : (0 : ℝ) < hughesYoungReducedLeft h k := by exact_mod_cast ha
  have hbR : (0 : ℝ) < hughesYoungReducedRight h k := by exact_mod_cast hb
  have hExpA :
      ‖Complex.exp
          ((afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) *
            (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ))‖ =
        (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) := by
    have hReA :
        (((afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) *
          (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ)).re) =
            (1 / 2 + c) * Real.log (hughesYoungReducedLeft h k : ℝ) := by
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp [afeCriticalPoint]
    rw [Complex.norm_exp]
    rw [hReA]
    rw [Real.rpow_def_of_pos haR]
    congr 1
    ring
  have hExpB :
      ‖Complex.exp
          ((afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) *
            (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ))‖ =
        (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c) := by
    have hReB :
        (((afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) *
          (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ)).re) =
            (1 / 2 + c) * Real.log (hughesYoungReducedRight h k : ℝ) := by
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp [afeCriticalPoint]
    rw [Complex.norm_exp]
    rw [hReB]
    rw [Real.rpow_def_of_pos hbR]
    congr 1
    ring
  have hPowH :
      ‖((h : ℂ) ^ (-afeCriticalPoint t))‖ =
        (h : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Complex.ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos hhR]
    simp [afeCriticalPoint]
  have hPowK :
      ‖((k : ℂ) ^ (-afeCriticalPoint (-t)))‖ =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Complex.ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos hkR]
    simp [afeCriticalPoint]
  have hAcombine :
      (hughesYoungReducedLeft h k : ℝ)⁻¹ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) =
        (hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) := by
    rw [← Real.rpow_neg_one (hughesYoungReducedLeft h k : ℝ),
      ← Real.rpow_add haR]
    congr 1
    ring
  have hBcombine :
      (hughesYoungReducedRight h k : ℝ)⁻¹ *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c) =
        (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2) := by
    rw [← Real.rpow_neg_one (hughesYoungReducedRight h k : ℝ),
      ← Real.rpow_add hbR]
    congr 1
    ring
  unfold hughesYoungReducedMellinStaticComplex
  dsimp only
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
    norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
    hPowH, hPowK, hExpA, hExpB]
  simp only [norm_div, norm_one, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  rw [norm_hughesYoungLocalizedStaticScalar_eq_coefficients_mul_rpow hh hk]
  rw [mul_inv_rev]
  rw [← hAcombine, ← hBcombine]
  ring

end RiemannZeta.GuthMaynard
