import TaoTrudgianYang2025.SargosQuarticMomentIntegration

/-! Exact linear integration of genuine measurable nonnegative rectangle integrands. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargos_rectangle_lintegral_linear (F G H : ℝ × ℝ → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H)
    (K L a b c d : ℝ) :
    (∫⁻ x in Icc a b, ∫⁻ y in Icc c d,
      ENNReal.ofReal K*(ENNReal.ofReal L*(F (x,y)+G (x,y))+H (x,y))) =
      ENNReal.ofReal K*(ENNReal.ofReal L*
        ((∫⁻ x in Icc a b, ∫⁻ y in Icc c d, F (x,y))+
          (∫⁻ x in Icc a b, ∫⁻ y in Icc c d, G (x,y)))+
            (∫⁻ x in Icc a b, ∫⁻ y in Icc c d, H (x,y))) := by
  have hsum : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal K*(ENNReal.ofReal L*(F p+G p)+H p)) :=
    measurable_const.mul ((measurable_const.mul (hF.add hG)).add hH)
  rw [← lintegral_prod _ hsum.aemeasurable,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left (measurable_const.mul (hF.add hG)),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left hF G,
    lintegral_prod F hF.aemeasurable,lintegral_prod G hG.aemeasurable,
    lintegral_prod H hH.aemeasurable]

end TaoTrudgianYang2025
