import TaoTrudgianYang2025.BourgainCriticalMellin
import TaoTrudgianYang2025.ZetaMomentTransfer
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Quantitative localization of the critical Mellin kernel

Every constant depends only on the fixed test profile and the requested
decay order. Neither the physical dilation nor the ordinate nor the
localization radius enters the constant.
-/

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
open scoped Interval

noncomputable section

namespace TaoTrudgianYang2025

/-- Every polynomial moment of the actual fixed-profile Mellin kernel is
integrable. This supplies quantitative tails without a truncation premise. -/
theorem bourgain_integrable_mellin_weight {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) (σ : ℝ) :
    Integrable (fun u : ℝ =>
      (1+|u|)^q * ‖mellin g ((σ : ℂ)+(u : ℂ)*I)‖) := by
  obtain ⟨C, _, hC⟩ := hg.exists_mellin_one_add_abs_pow_line_bound (q+2) σ
  have hi : Integrable (fun u : ℝ => 1 / (1+|u|)^2) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
    apply h.congr
    filter_upwards with u
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  have hc : Continuous (fun u : ℝ =>
      (1+|u|)^q * ‖mellin g ((σ : ℂ)+(u : ℂ)*I)‖) :=
    ((continuous_const.add continuous_abs).pow q).mul
      (hg.differentiable_mellin.continuous.comp (by fun_prop)).norm
  apply (hi.const_mul C).mono' hc.aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hu : 0 < (1+|u|)^2 := by positivity
  rw [mul_one_div, le_div_iff₀ hu]
  simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using hC u

/-- The norm of the critical zeta/Mellin integrand after removal of the
unit-modulus dilation factor. -/
def bourgainZetaMellinNorm (g : ℝ → ℂ) (t u : ℝ) : ℝ :=
  zetaMomentCriticalNorm (u+t) * ‖mellin g ((u : ℂ)*I)‖

theorem bourgainZetaMellinNorm_nonneg (g : ℝ → ℂ) (t u : ℝ) :
    0 ≤ bourgainZetaMellinNorm g t u := by
  unfold bourgainZetaMellinNorm zetaMomentCriticalNorm
  positivity

theorem continuous_bourgainZetaMellinNorm {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (t : ℝ) :
    Continuous (bourgainZetaMellinNorm g t) :=
  (continuous_zetaMomentCriticalNorm.comp (continuous_id.add continuous_const)).mul
    (hg.differentiable_mellin.continuous.comp (by fun_prop)).norm

/-- The genuine zeta factor costs only one polynomial weight. -/
theorem bourgainZetaMellinNorm_le (g : ℝ → ℂ) (t u : ℝ) :
    bourgainZetaMellinNorm g t u ≤
      6*(1+|t|)*((1+|u|)*‖mellin g ((u : ℂ)*I)‖) := by
  have hz := norm_zeta_mellin_boundary (Or.inl rfl) (u+t)
  have hw : 1+|u+t| ≤ (1+|t|)*(1+|u|) := by
    nlinarith [abs_add_le u t, abs_nonneg u, abs_nonneg t,
      mul_nonneg (abs_nonneg t) (abs_nonneg u)]
  unfold bourgainZetaMellinNorm zetaMomentCriticalNorm
  have hb := mul_le_mul_of_nonneg_right
    (hz.trans (mul_le_mul_of_nonneg_left hw (by norm_num)))
    (norm_nonneg (mellin g ((u : ℂ)*I)))
  convert hb using 1
  ring

theorem integrable_bourgainZetaMellinNorm {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (t : ℝ) :
    Integrable (bourgainZetaMellinNorm g t) := by
  have hi : Integrable (fun u : ℝ => (1+|u|)*‖mellin g ((u : ℂ)*I)‖) := by
    simpa using bourgain_integrable_mellin_weight hg 1 0
  apply (hi.const_mul (6*(1+|t|))).mono'
    (continuous_bourgainZetaMellinNorm hg t).aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (bourgainZetaMellinNorm_nonneg g t u)]
  exact bourgainZetaMellinNorm_le g t u

/-- Arbitrary-order tail decay, uniform in the ordinate and the physical
scale. The radius may be zero; no discarded integral is assumed small. -/
theorem bourgainZetaMellinNorm_tail {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t H : ℝ, 0 ≤ H →
      (∫ u in (Ioc (-H) H)ᶜ, bourgainZetaMellinNorm g t u) ≤
        C*(1+|t|)/(1+H)^q := by
  let w : ℝ → ℝ := fun u => (1+|u|)^(q+1)*‖mellin g ((u : ℂ)*I)‖
  have hi : Integrable w := by
    simpa [w] using bourgain_integrable_mellin_weight hg (q+1) 0
  have hw0 (u : ℝ) : 0 ≤ w u := by dsimp [w]; positivity
  let A : ℝ := ∫ u, w u
  have hA : 0 ≤ A := integral_nonneg hw0
  refine ⟨6*(A+1), by positivity, ?_⟩
  intro t H hH
  have hHp : 0 < (1+H)^q := by positivity
  apply (le_div_iff₀ hHp).2
  rw [← integral_mul_const]
  have hm : (∫ u in (Ioc (-H) H)ᶜ,
      bourgainZetaMellinNorm g t u * (1+H)^q) ≤
      ∫ u in (Ioc (-H) H)ᶜ, 6*(1+|t|)*w u := by
    apply setIntegral_mono_on
      (((integrable_bourgainZetaMellinNorm hg t).mul_const _).integrableOn)
      ((hi.const_mul _).integrableOn) measurableSet_Ioc.compl
    intro u hu
    have hHu : H ≤ |u| := by
      have hn : ¬ (-H < u ∧ u ≤ H) := hu
      by_cases hl : u ≤ -H
      · exact le_trans (by linarith : H ≤ -u) (neg_le_abs u)
      · have hr : H < u := lt_of_not_ge (fun hh => hn ⟨lt_of_not_ge hl, hh⟩)
        exact hr.le.trans (le_abs_self u)
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+H)
      (show 1+H ≤ 1+|u| by linarith) q
    calc
      _ ≤ (6*(1+|t|)*((1+|u|)*‖mellin g ((u : ℂ)*I)‖)) * (1+H)^q :=
        mul_le_mul_of_nonneg_right (bourgainZetaMellinNorm_le g t u) (by positivity)
      _ ≤ (6*(1+|t|)*((1+|u|)*‖mellin g ((u : ℂ)*I)‖)) * (1+|u|)^q :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by dsimp [w]; rw [pow_succ]; ring
  calc
    _ ≤ _ := hm
    _ ≤ ∫ u, 6*(1+|t|)*w u :=
      setIntegral_le_integral (hi.const_mul _) (Eventually.of_forall (fun u => by
        exact mul_nonneg (by positivity) (hw0 u)))
    _ = 6*(1+|t|)*A := by rw [integral_const_mul]
    _ ≤ _ := by nlinarith [abs_nonneg t]

/-- Norm estimate for the exact Mellin entry. The prefactor is bounded by
one, and the residue is not lost. -/
theorem bourgainCriticalWeight_norm_le_mellin {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    ‖∑' n : ℕ, bourgainCriticalWeight g L n * dirichletPhase n t‖ ≤
      ‖mellin (bourgainCriticalWeight g L) (1-(t : ℂ)*I)‖ +
        ∫ u, bourgainZetaMellinNorm g t u := by
  rw [smooth_dirichlet_sum_eq_critical_zeta_mellin
    (bourgainCriticalWeightTest hg hL) t]
  have hnorm (u : ℝ) :
      ‖riemannZeta (((1/2 : ℝ) : ℂ)+((u+t : ℝ) : ℂ)*I) *
        mellin (bourgainCriticalWeight g L) (((1/2 : ℝ) : ℂ)+(u : ℂ)*I)‖ =
        bourgainZetaMellinNorm g t u := by
    rw [norm_mul]
    have hk : ‖mellin (bourgainCriticalWeight g L) (((1/2 : ℝ) : ℂ)+(u : ℂ)*I)‖ =
        ‖mellin g ((u : ℂ)*I)‖ := by
      simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
        norm_bourgainCriticalWeight_mellin_critical g hL u
    rw [hk]
    rfl
  have hfactor : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul]
    norm_num only [norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    exact (div_le_one (by positivity)).2 (by nlinarith [Real.pi_gt_three])
  have hint : ‖∫ u : ℝ,
      riemannZeta (((1/2 : ℝ) : ℂ)+((u+t : ℝ) : ℂ)*I) *
        mellin (bourgainCriticalWeight g L) (((1/2 : ℝ) : ℂ)+(u : ℂ)*I)‖ ≤
        ∫ u, bourgainZetaMellinNorm g t u := by
    simpa only [hnorm] using norm_integral_le_integral_norm (fun u : ℝ =>
      riemannZeta (((1/2 : ℝ) : ℂ)+((u+t : ℝ) : ℂ)*I) *
        mellin (bourgainCriticalWeight g L) (((1/2 : ℝ) : ℂ)+(u : ℂ)*I))
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul]
      exact add_le_add le_rfl ((mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans
        (by simpa only [one_mul] using hint))

/-- Actual finite-window localization, with uniform constants and separate
residue, local zeta, and arbitrary-order tail terms. -/
theorem bourgainCriticalWeight_localized {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ t H : ℝ, 0 ≤ H →
      ‖∑' n : ℕ, bourgainCriticalWeight g L n * dirichletPhase n t‖ ≤
        C * (Real.sqrt L / (1+|t|)^q +
          (∫ u in -H..H, zetaMomentCriticalNorm (u+t)) +
          (1+|t|)/(1+H)^q) := by
  obtain ⟨C₀,hC₀,hzero⟩ := hg.exists_mellin_one_add_abs_pow_line_bound 0 0
  obtain ⟨C₁,hC₁,hres⟩ := bourgainCriticalWeight_mellin_bounds hg q
  obtain ⟨C₂,hC₂,htail⟩ := bourgainZetaMellinNorm_tail hg q
  refine ⟨C₀+C₁+C₂+1, by positivity, ?_⟩
  intro L hL t H hH
  have horder : -H ≤ H := by linarith
  have hi := integrable_bourgainZetaMellinNorm hg t
  have hzcont : Continuous (fun u : ℝ => zetaMomentCriticalNorm (u+t)) :=
    continuous_zetaMomentCriticalNorm.comp (continuous_id.add continuous_const)
  have hlocal : (∫ u in Ioc (-H) H, bourgainZetaMellinNorm g t u) ≤
      C₀ * ∫ u in -H..H, zetaMomentCriticalNorm (u+t) := by
    rw [← intervalIntegral.integral_of_le horder, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on horder hi.intervalIntegrable
      ((hzcont.const_mul C₀).intervalIntegrable _ _)
    intro u hu
    have h := hzero u
    simp only [pow_zero, one_mul, ofReal_zero, zero_add] at h
    simpa only [bourgainZetaMellinNorm, mul_comm] using
      mul_le_mul_of_nonneg_left h (show 0 ≤ zetaMomentCriticalNorm (u+t) from norm_nonneg _)
  have hr : ‖mellin (bourgainCriticalWeight g L) (1-(t : ℂ)*I)‖ ≤
      C₁ * (Real.sqrt L / (1+|t|)^q) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < (1+|t|)^q)]
    simpa only [mul_comm] using (hres L hL t).2
  have htot : (∫ u, bourgainZetaMellinNorm g t u) ≤
      C₀ * (∫ u in -H..H, zetaMomentCriticalNorm (u+t)) +
        C₂*((1+|t|)/(1+H)^q) := by
    rw [← integral_add_compl measurableSet_Ioc hi]
    exact add_le_add hlocal (by simpa only [mul_div_assoc] using htail t H hH)
  have hmain := (bourgainCriticalWeight_norm_le_mellin hg hL t).trans (add_le_add hr htot)
  have ha : 0 ≤ Real.sqrt L / (1+|t|)^q := by positivity
  have hb : 0 ≤ ∫ u in -H..H, zetaMomentCriticalNorm (u+t) :=
    intervalIntegral.integral_nonneg horder (fun _ _ => norm_nonneg _)
  have hc : 0 ≤ (1+|t|)/(1+H)^q := by positivity
  nlinarith [mul_nonneg hC₀ ha, mul_nonneg hC₀ hc,
    mul_nonneg hC₁.le hb, mul_nonneg hC₁.le hc,
    mul_nonneg hC₂.le ha, mul_nonneg hC₂.le hb]

end TaoTrudgianYang2025
