import TaoTrudgianYang2025.ZetaFourthKernelNear
import TaoTrudgianYang2025.ZetaFourthKernelFar

/-!
# Whole-line fourth-moment kernel bounds

Both ordinate ranges are covered. For each fixed c>0 the exact normalized
kernel is bounded by K(c) t^c times a Gaussian on the entire vertical line.
This supplies absolute integrability and the explicit contour mass.
-/

noncomputable section

open Complex MeasureTheory

namespace TaoTrudgianYang2025

theorem exists_norm_zetaFourthKernel_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ,
      4 ≤ t → 4*c ≤ t →
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤
        K*t^c*Real.exp (-98*u^2) := by
  obtain ⟨A,hA,hnear⟩ := exists_norm_zetaFourthKernel_near_le hc
  obtain ⟨B,hB,hfar⟩ := exists_norm_zetaFourthKernel_far_le hc
  refine ⟨A+B,by positivity,?_⟩
  intro t u ht hct
  have ht0 : 0 < t := by linarith
  by_cases hu : |u| ≤ t/4
  · exact (hnear t u ht hct hu).trans (by gcongr; linarith)
  · have htu : t ≤ 4*|u| := by linarith [lt_of_not_ge hu]
    have hp : 1 ≤ t^c := Real.one_le_rpow (by linarith) hc.le
    calc
      _ ≤ B*Real.exp (-99*u^2) := hfar t u ht0.le htu
      _ ≤ B*Real.exp (-98*u^2) := by
        gcongr
        nlinarith [sq_nonneg u]
      _ ≤ B*t^c*Real.exp (-98*u^2) := by gcongr; nlinarith
      _ ≤ (A+B)*t^c*Real.exp (-98*u^2) := by gcongr; linarith

theorem integrable_zetaFourthKernel_vertical {t c : ℝ}
    (hc : 0 < c) (ht : 4 ≤ t) (hct : 4*c ≤ t) :
    Integrable (fun u : ℝ => zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)) := by
  obtain ⟨K,_,hK⟩ := exists_norm_zetaFourthKernel_le hc
  have hg : Integrable (fun u : ℝ => K*t^c*Real.exp (-98*u^2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 98)).const_mul (K*t^c)
  exact hg.mono' (continuous_zetaFourthKernel_vertical t hc).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => hK t u ht hct))

theorem exists_integral_norm_zetaFourthKernel_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      4 ≤ t → 4*c ≤ t →
      (∫ u : ℝ, ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖) ≤
        K*t^c*Real.sqrt (Real.pi/98) := by
  obtain ⟨K,hK,hbound⟩ := exists_norm_zetaFourthKernel_le hc
  refine ⟨K,hK,?_⟩
  intro t ht hct
  have hg : Integrable (fun u : ℝ => K*t^c*Real.exp (-98*u^2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 98)).const_mul (K*t^c)
  calc
    _ ≤ ∫ u : ℝ, K*t^c*Real.exp (-98*u^2) :=
      integral_mono (integrable_zetaFourthKernel_vertical hc ht hct).norm hg
        (fun u => hbound t u ht hct)
    _ = _ := by rw [integral_const_mul, integral_gaussian]

end TaoTrudgianYang2025
