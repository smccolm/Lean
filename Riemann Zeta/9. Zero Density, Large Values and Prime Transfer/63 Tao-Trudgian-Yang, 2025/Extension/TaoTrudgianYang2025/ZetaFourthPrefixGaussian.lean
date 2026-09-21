import TaoTrudgianYang2025.ZetaFourthTruncation
import TaoTrudgianYang2025.ZetaFourthCoefficients
import TaoTrudgianYang2025.DirichletPrefixBounded
import TaoTrudgianYang2025.WeightedIntegralSquare

/-!
# The actual contour prefix bounded by a Gaussian polynomial mean square

The genuine kernel is dominated, not replaced. All whole-line
integrability hypotheses in the weighted square inequality are derived
from the actual finite polynomial and the proved Gaussian bound.
-/

noncomputable section

open Complex Filter MeasureTheory

namespace TaoTrudgianYang2025

theorem exists_norm_sq_fourthPrefix_le_gaussian {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*c ≤ t → ∀ N : ℕ,
      ‖zetaFourthPrefix t c (Finset.range (N+1))‖^2 ≤ K*t^(2*c)*
        ∫ u : ℝ, Real.exp (-98*u^2)*
          ‖dirichletPrefix N (zetaFourthCoeff c) (u-t)‖^2 := by
  obtain ⟨A,hA,hkernel⟩ := exists_norm_zetaFourthKernel_le hc
  let B : ℝ := ‖(1/(2*Real.pi):ℂ)‖
  have hB : 0 < B := by
    apply norm_pos_iff.mpr
    exact one_div_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  let G : ℝ := Real.sqrt (Real.pi/98)
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨(B*A)^2*G,by positivity,?_⟩
  intro t ht hct N
  let p : ℝ → ℂ := fun u => dirichletPrefix N (zetaFourthCoeff c) (u-t)
  let g : ℝ → ℝ := fun u => Real.exp (-98*u^2)
  have hg : Integrable g := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<98)
  have hgp : Integrable (fun u => g u*‖p u‖) := by
    simpa only [pow_one] using
      integrable_gaussian_dirichletPrefix_norm_pow (by norm_num : (0:ℝ)<98)
        N (zetaFourthCoeff c) t 1
  have hgp2 : Integrable (fun u => g u*‖p u‖^2) :=
    integrable_gaussian_dirichletPrefix_norm_pow (by norm_num : (0:ℝ)<98)
      N (zetaFourthCoeff c) t 2
  have hmass : (∫ u : ℝ, g u) = G := integral_gaussian 98
  have hcs : (∫ u : ℝ, g u*‖p u‖)^2 ≤ G*(∫ u : ℝ, g u*‖p u‖^2) := by
    have h := integral_weighted_sq_le g (fun u => ‖p u‖)
      (fun u => (Real.exp_pos _).le) hg hgp hgp2 (hmass.symm ▸ hG)
    simpa only [hmass] using h
  have hpoint (u : ℝ) :
      ‖p u*zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤ (A*t^c)*(g u*‖p u‖) := by
    rw [norm_mul]
    calc
      _ ≤ ‖p u‖*(A*t^c*Real.exp (-98*u^2)) :=
        mul_le_mul_of_nonneg_left (hkernel t u ht hct) (norm_nonneg _)
      _ = _ := by dsimp [g]; ring
  have hdom := hgp.const_mul (A*t^c)
  have hprod : Integrable (fun u : ℝ =>
      p u*zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)) :=
    hdom.mono'
      (((continuous_dirichletPrefix_reflected N (zetaFourthCoeff c) t).mul
        (continuous_zetaFourthKernel_vertical t hc)).aestronglyMeasurable)
      (Eventually.of_forall hpoint)
  have hsource : zetaFourthPrefix t c (Finset.range (N+1)) =
      (1/(2*Real.pi):ℂ)*(∫ u : ℝ, p u*zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)) := by
    rw [zetaFourthPrefix_eq_integral (by linarith : 0 ≤ t) hc]
    simp_rw [sum_fourth_divisorTerm_eq_prefix]
    rfl
  have hnorm : ‖zetaFourthPrefix t c (Finset.range (N+1))‖ ≤
      B*(A*t^c)*(∫ u : ℝ, g u*‖p u‖) := by
    rw [hsource,norm_mul]
    calc
      _ ≤ B*(∫ u : ℝ, ‖p u*zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hB.le
      _ ≤ B*(∫ u : ℝ, (A*t^c)*(g u*‖p u‖)) :=
        mul_le_mul_of_nonneg_left (integral_mono hprod.norm hdom hpoint) hB.le
      _ = _ := by rw [integral_const_mul]; ring
  calc
    _ ≤ (B*(A*t^c)*(∫ u : ℝ, g u*‖p u‖))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (B*A)^2*(t^c)^2*(∫ u : ℝ, g u*‖p u‖)^2 := by ring
    _ ≤ (B*A)^2*(t^c)^2*(G*(∫ u : ℝ, g u*‖p u‖^2)) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ t)]
      have heq : c*(2:ℝ) = 2*c := by ring
      norm_num only [Nat.cast_ofNat]
      rw [heq]
      dsimp [p,g]
      ring

end TaoTrudgianYang2025
