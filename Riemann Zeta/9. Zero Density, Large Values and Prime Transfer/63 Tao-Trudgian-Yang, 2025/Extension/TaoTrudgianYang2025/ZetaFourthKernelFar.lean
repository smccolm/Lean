import TaoTrudgianYang2025.ZetaFourthKernelBasic
import TaoTrudgianYang2025.ZetaSquareGammaInverse

/-!
# The large-ordinate part of the normalized fourth-moment kernel

Beyond t/4 the actual Gaussian dominates the inverse Gamma normalization.
This bound covers the whole complementary ordinate range for any fixed
positive contour real part, not just a finite Mellin window.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem norm_zetaSquarePoleShift_le_polynomial
    {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) (u : ℝ) :
    ‖zetaSquarePoleShift t ((c:ℂ)+(u:ℂ)*I)‖ ≤
      16*(3+c+t+|u|)^4 := by
  let w : ℂ := (c:ℂ)+(u:ℂ)*I
  let s : ℂ := afeCriticalPoint (-t)+w
  let R : ℝ := 3+c+t+|u|
  have hcrit : ‖afeCriticalPoint (-t)‖ ≤ 1/2+t := by
    simpa [afeCriticalPoint,abs_of_nonneg ht] using
      norm_add_le (1/2:ℂ) (((-t:ℝ):ℂ)*I)
  have hw : ‖w‖ ≤ c+|u| := norm_vertical_shift_le hc u
  have hs : ‖s‖ ≤ 1/2+t+c+|u| :=
    (norm_add_le _ _).trans (by linarith)
  have hsR : ‖s‖ ≤ R := hs.trans (by dsimp [R]; linarith)
  have hsub : ‖1-s‖ ≤ R := (norm_sub_le _ _).trans (by
    rw [norm_one]
    dsimp [R]
    linarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  rw [zetaSquarePoleShift_eq_source, norm_div, norm_pow, norm_mul]
  change (‖s‖*‖1-s‖)^2/‖zetaSquarePoleNormalization t‖ ≤ 16*R^4
  calc
    _ ≤ (R*R)^2/(1/16) := by
      gcongr
      exact zetaSquarePoleNormalization_norm_lower t
    _ = _ := by ring

theorem exists_norm_zetaFourthKernel_far_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ,
      0 ≤ t → t ≤ 4*|u| →
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤
        K*Real.exp (-99*u^2) := by
  obtain ⟨C,hC,hInv⟩ := exists_norm_inv_zetaSquareGammaNormalization_le
  let G : ℝ := Real.pi^(-(1/2+c)/2)*Real.Gamma ((1/2+c)/2)
  have hG : 0 < G := mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by linarith))
  let A : ℝ := 10000*G^2*C/c
  let Q : ℝ := 12*(c+3)+(60+4*Real.pi)^2/4
  let K : ℝ := A*Real.exp (100*c^2)*Real.exp Q
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro t u ht hu
  let w : ℂ := (c:ℂ)+(u:ℂ)*I
  let R : ℝ := 3+c+t+|u|
  let B : ℝ := c+3+5*|u|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg u]
  have hw := norm_vertical_shift_le hc.le u
  have hwlower := vertical_shift_re_le_norm hc.le u
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625*R^8 :=
    norm_hughesYoungAuxiliaryZero_le_polynomial hR (hw.trans (by dsimp [R]; linarith))
  have hpole : ‖zetaSquarePoleShift t w‖ ≤ 16*R^4 :=
    norm_zetaSquarePoleShift_le_polynomial ht hc.le u
  have hg : ‖Complex.Gammaℝ (afeCriticalPoint (-t)+w)‖ ≤ G := by
    have hre : (afeCriticalPoint (-t)+w).re = 1/2+c := by
      norm_num [afeCriticalPoint,w]
    simpa only [hre,G] using norm_GammaR_le_realGamma_re
      (show 0 < (afeCriticalPoint (-t)+w).re by rw [hre]; linarith)
  have hgamma :
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ ≤
        G^2*(C*Real.exp (Real.pi*t)) := by
    rw [← norm_gammaSquare_div_zetaSquareGammaNormalization,
      div_eq_mul_inv, norm_mul, norm_pow]
    have hi := hInv t
    rw [abs_of_nonneg ht] at hi
    gcongr
  have hRB : R ≤ B := by dsimp [R,B]; linarith
  have hpoly : B^12*Real.exp ((4*Real.pi)*|u|) ≤ Real.exp Q*Real.exp (u^2) := by
    have hp := abs_polynomial_mul_exp_le_gaussian
      (by linarith : 0 ≤ c+3) (by norm_num : (0:ℝ) ≤ 5) (4*Real.pi) 12 u
    norm_num at hp
    exact hp
  have htime : Real.exp (Real.pi*t) ≤ Real.exp ((4*Real.pi)*|u|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hu Real.pi_pos.le]
  have he : Real.exp (100*c^2-100*u^2) =
      Real.exp (100*c^2)*Real.exp (-100*u^2) := by rw [← Real.exp_add]; congr 1; ring
  have hgauss : Real.exp (u^2)*Real.exp (-100*u^2) = Real.exp (-99*u^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [norm_zetaFourthKernel_vertical]
  change Real.exp (100*c^2-100*u^2)*‖hughesYoungAuxiliaryZero w‖*
    ‖zetaSquarePoleShift t w‖*
    ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
      Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖/‖w‖ ≤ _
  calc
    _ ≤ Real.exp (100*c^2-100*u^2)*(625*R^8)*(16*R^4)*
        (G^2*(C*Real.exp (Real.pi*t)))/c := by gcongr
    _ = A*R^12*Real.exp (100*c^2-100*u^2)*Real.exp (Real.pi*t) := by dsimp [A]; ring
    _ ≤ A*B^12*Real.exp (100*c^2-100*u^2)*Real.exp ((4*Real.pi)*|u|) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hRB 12) hA.le)
          (Real.exp_pos _).le)
        htime (Real.exp_pos _).le (by positivity)
    _ = A*Real.exp (100*c^2)*
        (B^12*Real.exp ((4*Real.pi)*|u|))*Real.exp (-100*u^2) := by rw [he]; ring
    _ ≤ A*Real.exp (100*c^2)*(Real.exp Q*Real.exp (u^2))*Real.exp (-100*u^2) := by
      gcongr
    _ = K*(Real.exp (u^2)*Real.exp (-100*u^2)) := by dsimp [K]; ring
    _ = _ := by rw [hgauss]

end TaoTrudgianYang2025
