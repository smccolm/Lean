import TaoTrudgianYang2025.ZetaFourthTerm
import TaoTrudgianYang2025.ZetaFourthContourBounds

/-!
# Actual divisor-term domination and disappearing horizontal sides

Each coefficient remains the ordinary divisor coefficient. Domination
holds on the whole positive contour strip, and therefore justifies both
vertical integrability and the vanishing horizontal sides.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem continuous_zetaFourthTerm_vertical (t : ℝ) (n : ℕ)
    {c : ℝ} (hc : 0 < c) :
    Continuous (fun u : ℝ => zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hw : 0 < ((c:ℂ)+(u:ℂ)*I).re := by simpa using hc
  have hline : ContinuousAt (fun v : ℝ => (c:ℂ)+(v:ℂ)*I) u := by fun_prop
  exact (differentiableAt_zetaFourthTerm t n hw).continuousAt.comp
    (f := fun v : ℝ => (c:ℂ)+(v:ℂ)*I) hline

theorem exists_norm_zetaFourthTerm_strip_le
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ Icc a b, ∀ u : ℝ,
      ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖ ≤ C*Real.exp (-99*u^2) := by
  obtain ⟨K,hK,hbound⟩ := exists_norm_zetaFourthKernel_strip_le ha hab ht
  refine ⟨K*((n.divisors.card:ℝ)+1),by positivity,?_⟩
  intro c hc u
  have hD := norm_fourth_divisorTerm_le_card (ha.le.trans hc.1) t u n
  rw [zetaFourthTerm,norm_mul]
  calc
    _ ≤ (n.divisors.card:ℝ)*(K*Real.exp (-99*u^2)) :=
      mul_le_mul hD (hbound c hc u) (norm_nonneg _) (by positivity)
    _ ≤ K*((n.divisors.card:ℝ)+1)*Real.exp (-99*u^2) := by
      nlinarith [mul_nonneg hK.le (Real.exp_pos (-99*u^2)).le]

theorem integrable_zetaFourthTerm_vertical {t c : ℝ}
    (ht : 0 ≤ t) (hc : 0 < c) (n : ℕ) :
    Integrable (fun u : ℝ => zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)) := by
  obtain ⟨K,_,hK⟩ := exists_norm_zetaFourthTerm_strip_le hc le_rfl ht n
  have hg : Integrable (fun u : ℝ => K*Real.exp (-99*u^2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 99)).const_mul K
  exact hg.mono' (continuous_zetaFourthTerm_vertical t n hc).aestronglyMeasurable
    (Eventually.of_forall (fun u => hK c ⟨le_rfl,le_rfl⟩ u))

theorem tendsto_zetaFourthTerm_horizontal_of_sq_eq
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) (n : ℕ)
    (v : ℝ → ℝ) (hv : ∀ H : ℝ, (v H)^2 = H^2) :
    Tendsto (fun H : ℝ =>
      ∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(v H:ℂ)*I)) atTop (𝓝 0) := by
  obtain ⟨K,_,hK⟩ := exists_norm_zetaFourthTerm_strip_le ha hab ht n
  have hbnd : ∀ H : ℝ,
      ‖∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(v H:ℂ)*I)‖ ≤
        (K*Real.exp (-99*H^2))*|b-a| := by
    intro H
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Icc a b := by
      rw [← uIcc_of_le hab]
      exact uIoc_subset_uIcc hx
    simpa only [hv H] using hK x hx' (v H)
  have hp : Tendsto (fun H : ℝ => H^2) atTop atTop :=
    tendsto_pow_atTop (by decide : 2 ≠ 0)
  have hm : Tendsto (fun H : ℝ => 99*H^2) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 99) hp
  have he : Tendsto (fun H : ℝ => Real.exp (-99*H^2)) atTop (𝓝 0) := by
    simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hbnd
  simpa using (he.const_mul K).mul_const |b-a|

end TaoTrudgianYang2025
