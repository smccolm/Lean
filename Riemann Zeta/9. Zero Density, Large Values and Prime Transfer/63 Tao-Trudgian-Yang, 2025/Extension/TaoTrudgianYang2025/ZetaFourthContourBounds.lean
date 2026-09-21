import TaoTrudgianYang2025.ZetaFourthKernel

/-!
# Uniform contour-strip domination for the fourth-moment kernel

The real part varies over a compact positive interval. The bound is used
only to justify line shifts and dominated convergence; its height-dependent
bound is not presented as a moment estimate.
-/

noncomputable section

open Complex Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem exists_norm_zetaFourthKernel_strip_le
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) :
    ∃ K : ℝ, 0 < K ∧ ∀ c ∈ Icc a b, ∀ u : ℝ,
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤ K*Real.exp (-99*u^2) := by
  obtain ⟨G,hG,hGamma⟩ := exists_uniform_norm_GammaR_vertical_strip (c₁ := b) ha
  let D : ℝ := ‖(zetaSquareGammaNormalization t)⁻¹‖
  have hD : 0 < D := norm_pos_iff.mpr
    (inv_ne_zero (zetaSquareGammaNormalization_ne_zero t))
  let A : ℝ := 10000*G^2*D/a
  let Q : ℝ := 12*(3+b+t)+36
  let K : ℝ := A*Real.exp (100*b^2)*Real.exp Q
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro c hc u
  have hc0 : 0 < c := ha.trans_le hc.1
  have hb : 0 < b := ha.trans_le hab
  let w : ℂ := (c:ℂ)+(u:ℂ)*I
  let R : ℝ := 3+c+t+|u|
  let B : ℝ := 3+b+t+|u|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg u]
  have hw := norm_vertical_shift_le hc0.le u
  have hwlower : a ≤ ‖w‖ := hc.1.trans (vertical_shift_re_le_norm hc0.le u)
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625*R^8 :=
    norm_hughesYoungAuxiliaryZero_le_polynomial hR
      (hw.trans (by dsimp [R]; linarith))
  have hpole : ‖zetaSquarePoleShift t w‖ ≤ 16*R^4 :=
    norm_zetaSquarePoleShift_le_polynomial ht hc0.le u
  have hg : ‖Complex.Gammaℝ (afeCriticalPoint (-t)+w)‖ ≤ G := by
    have heq : afeCriticalPoint (-t)+w =
        ((1/2+c:ℝ):ℂ)+((-t+u:ℝ):ℂ)*I := by
      dsimp [afeCriticalPoint,w]
      push_cast
      ring
    rw [heq]
    exact hGamma c (-t+u) hc
  have hgamma :
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ ≤ G^2*D := by
    rw [← norm_gammaSquare_div_zetaSquareGammaNormalization,
      div_eq_mul_inv, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hg 2) (norm_nonneg _)
  have hRB : R ≤ B := by dsimp [R,B]; linarith [hc.2]
  have hpoly : B^12 ≤ Real.exp Q*Real.exp (u^2) := by
    have hp := abs_polynomial_mul_exp_le_gaussian
      (by positivity : 0 ≤ 3+b+t) (by norm_num : (0:ℝ) ≤ 1) 0 12 u
    norm_num at hp
    exact hp
  have hexp : Real.exp (100*c^2-100*u^2) ≤ Real.exp (100*b^2-100*u^2) := by
    apply Real.exp_le_exp.mpr
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0.le hc.2 2) (by norm_num)) _
  have he : Real.exp (100*b^2-100*u^2) =
      Real.exp (100*b^2)*Real.exp (-100*u^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
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
    _ ≤ Real.exp (100*c^2-100*u^2)*(625*R^8)*(16*R^4)*(G^2*D)/a := by
      gcongr
    _ = A*R^12*Real.exp (100*c^2-100*u^2) := by dsimp [A]; ring
    _ ≤ A*B^12*Real.exp (100*b^2-100*u^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans (by norm_num) hR) hRB 12) hA.le)
        hexp (Real.exp_pos _).le (by positivity)
    _ = A*Real.exp (100*b^2)*B^12*Real.exp (-100*u^2) := by rw [he]; ring
    _ ≤ A*Real.exp (100*b^2)*(Real.exp Q*Real.exp (u^2))*Real.exp (-100*u^2) := by
      gcongr
    _ = K*(Real.exp (u^2)*Real.exp (-100*u^2)) := by dsimp [K]; ring
    _ = _ := by rw [hgauss]

end TaoTrudgianYang2025
