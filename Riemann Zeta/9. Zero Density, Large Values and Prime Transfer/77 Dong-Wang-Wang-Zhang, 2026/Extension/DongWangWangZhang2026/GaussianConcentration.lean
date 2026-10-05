import DongWangWangZhang2026.GaussianTransform
import DongWangWangZhang2026.DilationLipschitz

/-!
# Gaussian concentration at the actual maximizing twist

The first-moment Gaussian majorant is integrable. Rescaling it gives the
one-third continuity error at the linked logarithmic scale, with an
absolute constant. No concentration or large-sum conclusion is assumed.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex MeasureTheory Real
open scoped Topology

/-- Fixed, integrable majorant for the rescaled one-third continuity error. -/
def gaussianMomentMajorant (w : ℝ) : ℝ := (1 + |w|) * Real.exp (-w ^ 2 / 2)

/-- The fixed Gaussian first absolute moment is finite. -/
theorem integrable_gaussianMomentMajorant : Integrable gaussianMomentMajorant := by
  have h₀ := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have h₁ := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).norm
  convert h₀.add h₁ using 1
  ext w
  simp only [gaussianMomentMajorant, Pi.add_apply, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  rw [show -(1 / 2 : ℝ) * w ^ 2 = -w ^ 2 / 2 by ring]
  ring

/-- A single absolute constant for the Gaussian error, independent of every source scale. -/
def gaussianMomentConstant : ℝ := ∫ w : ℝ, gaussianMomentMajorant w

theorem gaussianMomentConstant_nonneg : 0 ≤ gaussianMomentConstant :=
  integral_nonneg (fun w => by dsimp [gaussianMomentMajorant]; positivity)

/-- The source Hölder weight is bounded by a linear weight after the Gaussian rescaling. -/
theorem holder_weight_rescaled_le {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hr1 : r ≤ 1) (y : ℝ) :
    ((1 + |y - L|) / L) ^ (1 / 3 : ℝ) ≤
      (1 + |r * (y - L)|) / (r * L) ^ (1 / 3 : ℝ) := by
  have hbase : (1 + |y - L|) / L ≤ (1 + |r * (y - L)|) / (r * L) := by
    rw [div_le_div_iff₀ hL (mul_pos hr hL), abs_mul, abs_of_pos hr]
    nlinarith
  calc
    _ ≤ ((1 + |r * (y - L)|) / (r * L)) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    _ = (1 + |r * (y - L)|) ^ (1 / 3 : ℝ) / (r * L) ^ (1 / 3 : ℝ) :=
      Real.div_rpow (by positivity) (by positivity) _
    _ ≤ _ := div_le_div_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by linarith [abs_nonneg (r * (y - L))]) (by norm_num))
      (Real.rpow_nonneg (by positivity) _)

/-- Translation and dilation evaluate the rescaled majorant's full integral. -/
theorem integral_gaussianMomentMajorant_scaled {r : ℝ} (hr : 0 < r) (L : ℝ) :
    (∫ y : ℝ, gaussianMomentMajorant (r * (y - L))) = gaussianMomentConstant / r := by
  rw [integral_sub_right_eq_self (fun y : ℝ => gaussianMomentMajorant (r * y)) L,
    Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hr)]
  simp [gaussianMomentConstant, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Integrability is retained under the same nonzero dilation and translation. -/
theorem integrable_gaussianMomentMajorant_scaled {r : ℝ} (hr : 0 < r) (L : ℝ) :
    Integrable (fun y : ℝ => gaussianMomentMajorant (r * (y - L))) :=
  (integrable_gaussianMomentMajorant.comp_mul_left' hr.ne').comp_sub_right L

/-- The actual source continuity weight has an integrable Gaussian majorant. -/
theorem integrable_holder_gaussian {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hr1 : r ≤ 1) :
    Integrable (fun y : ℝ => ((1 + |y - L|) / L) ^ (1 / 3 : ℝ) *
      Real.exp (-(r * (y - L)) ^ 2 / 2)) := by
  apply ((integrable_gaussianMomentMajorant_scaled hr L).div_const
    ((r * L) ^ (1 / 3 : ℝ))).mono' (by fun_prop)
  filter_upwards with y
  rw [Real.norm_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_right (holder_weight_rescaled_le hL hr hr1 y)
    (Real.exp_pos (-(r * (y - L)) ^ 2 / 2)).le
  simpa only [gaussianMomentMajorant, div_mul_eq_mul_div] using h

/-- Quantitative Gaussian integration of the source one-third continuity weight. -/
theorem integral_holder_gaussian_le {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hr1 : r ≤ 1) :
    (∫ y : ℝ, ((1 + |y - L|) / L) ^ (1 / 3 : ℝ) *
      Real.exp (-(r * (y - L)) ^ 2 / 2)) ≤
        gaussianMomentConstant / r / (r * L) ^ (1 / 3 : ℝ) := by
  calc
    _ ≤ ∫ y : ℝ, gaussianMomentMajorant (r * (y - L)) /
        (r * L) ^ (1 / 3 : ℝ) := by
      apply integral_mono (integrable_holder_gaussian hL hr hr1)
        ((integrable_gaussianMomentMajorant_scaled hr L).div_const _)
      intro y
      have h := mul_le_mul_of_nonneg_right (holder_weight_rescaled_le hL hr hr1 y)
        (Real.exp_pos (-(r * (y - L)) ^ 2 / 2)).le
      simpa only [gaussianMomentMajorant, div_mul_eq_mul_div] using h
    _ = _ := by rw [integral_div, integral_gaussianMomentMajorant_scaled hr]


/-- The original normalized sum has an absolutely integrable centered Gaussian error. -/
theorem integrable_normalized_zetaSum_gaussian_difference
    {L r : ℝ} (hr : 0 < r) (t : ℝ) :
    Integrable (fun y : ℝ =>
      (zetaSum (Real.exp y) t / (Real.exp y : ℂ) -
        zetaSum (Real.exp L) t / (Real.exp L : ℂ)) *
        (Real.exp (-(r * (y - L)) ^ 2 / 2) : ℂ)) := by
  have hg : Integrable (fun w : ℝ => Real.exp (-w ^ 2 / 2)) := by
    simpa only [show -(1 / 2 : ℝ) = -1 / 2 by ring, div_mul_eq_mul_div,
      neg_one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  apply (((hg.comp_mul_left' hr.ne').comp_sub_right L).const_mul 2).mono'
  · apply Measurable.aestronglyMeasurable
    exact ((((measurable_zetaSum t).comp Real.measurable_exp).div
      (by fun_prop)).sub measurable_const).mul (by fun_prop)
  filter_upwards with y
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (norm_sub_le _ _).trans (by
    linarith [norm_normalized_zetaSum_exp_le_one y t,
      norm_normalized_zetaSum_exp_le_one L t])

/-- The actual maximizing twist supplies Gaussian concentration; no continuity premise remains. -/
theorem exists_maximizingTwist_gaussian_concentration :
    ∃ L₀ : ℝ, 16 ≤ L₀ ∧ ∀ x t t₀ : ℝ, 1 < x → L₀ ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ‖∫ y : ℝ, (zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ) -
          zetaSum (Real.exp (Real.log x)) (t - t₀) / (Real.exp (Real.log x) : ℂ)) *
          (Real.exp (-(r * (y - Real.log x)) ^ 2 / 2) : ℂ)‖ ≤
        dilationLipschitzConstant * gaussianMomentConstant / r /
          (r * Real.log x) ^ (1 / 3 : ℝ) := by
  obtain ⟨L₀, hL₀, hlip⟩ := exists_maximizingTwist_uniform_lipschitz
  refine ⟨L₀, hL₀, ?_⟩
  intro x t t₀ hx hlog hmax ht₀ r hr hr1
  have hL : 0 < Real.log x := Real.log_pos hx
  have hbound := norm_integral_le_of_norm_le
    (f := fun y : ℝ => (zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ) -
      zetaSum (Real.exp (Real.log x)) (t - t₀) / (Real.exp (Real.log x) : ℂ)) *
      (Real.exp (-(r * (y - Real.log x)) ^ 2 / 2) : ℂ))
    ((integrable_holder_gaussian hL hr hr1).const_mul dilationLipschitzConstant)
    (ae_of_all _ (fun y => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_right
        (hlip x t t₀ hx hlog hmax ht₀ y) (Real.exp_pos _).le).trans_eq (by ring)))
  calc
    _ ≤ _ := hbound
    _ = dilationLipschitzConstant * (∫ y : ℝ,
        ((1 + |y - Real.log x|) / Real.log x) ^ (1 / 3 : ℝ) *
          Real.exp (-(r * (y - Real.log x)) ^ 2 / 2)) := integral_const_mul _ _
    _ ≤ _ := (mul_le_mul_of_nonneg_left (integral_holder_gaussian_le hL hr hr1)
      (by linarith [dilationLipschitzConstant_ge_four])).trans_eq (by ring)

/-- Exact mass of the centered Gaussian, with the same rescaling used for its error. -/
theorem integral_centered_gaussian {r : ℝ} (hr : 0 < r) (L : ℝ) :
    (∫ y : ℝ, Real.exp (-(r * (y - L)) ^ 2 / 2)) = Real.sqrt (2 * Real.pi) / r := by
  rw [integral_sub_right_eq_self (fun y : ℝ => Real.exp (-(r * y) ^ 2 / 2)) L]
  have hf : (fun w : ℝ => Real.exp (-w ^ 2 / 2)) =
      (fun w : ℝ => Real.exp (-(1 / 2 : ℝ) * w ^ 2)) := by
    funext w
    congr 1
    ring
  rw [Measure.integral_comp_mul_left (fun w : ℝ => Real.exp (-w ^ 2 / 2)),
    abs_of_pos (inv_pos.mpr hr), hf, integral_gaussian]
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The Gaussian width and physical logarithmic scale are linked exactly. -/
theorem source_gaussian_width_mul {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    Real.sqrt (a / L) * L = Real.sqrt (a * L) := by
  calc
    _ = Real.sqrt (a / L) * Real.sqrt (L ^ 2) := by rw [Real.sqrt_sq hL.le]
    _ = Real.sqrt (a / L * L ^ 2) := (Real.sqrt_mul (div_pos ha hL).le _).symm
    _ = _ := by congr 1; field_simp

/-- The one-third continuity exponent becomes precisely the source one-sixth saving. -/
theorem source_gaussian_width_third {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    (Real.sqrt (a / L) * L) ^ (1 / 3 : ℝ) = (a * L) ^ (1 / 6 : ℝ) := by
  rw [source_gaussian_width_mul ha hL, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (mul_pos ha hL).le]
  norm_num

/-- Completing the square keeps the original exponential cutoff weight exactly. -/
theorem source_gaussian_weight_centered {a L : ℝ} (ha : 0 < a) (hL : 0 < L)
    (y : ℝ) :
    Real.exp ((a - 1) * y - (a / L) * y ^ 2 / 2) =
      Real.exp (a * L / 2) * Real.exp (-(Real.sqrt (a / L) * (y - L)) ^ 2 / 2) /
        Real.exp y := by
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  rw [mul_pow, Real.sq_sqrt (div_pos ha hL).le]
  field_simp
  ring

/-- Absolute convergence of the centered scalar Gaussian. -/
theorem integrable_centered_gaussian {r : ℝ} (hr : 0 < r) (L : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-(r * (y - L)) ^ 2 / 2)) := by
  have hg : Integrable (fun w : ℝ => Real.exp (-w ^ 2 / 2)) := by
    simpa only [show -(1 / 2 : ℝ) = -1 / 2 by ring, div_mul_eq_mul_div,
      neg_one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  exact (hg.comp_mul_left' hr.ne').comp_sub_right L

/-- The original sum's Gaussian integral splits into its central value and an actual error. -/
theorem source_gaussian_integral_centered {a L : ℝ} (ha : 0 < a) (hL : 0 < L)
    (t : ℝ) :
    (∫ y : ℝ, zetaSum (Real.exp y) t *
      (Real.exp ((a - 1) * y - (a / L) * y ^ 2 / 2) : ℂ)) =
      (Real.exp (a * L / 2) : ℂ) *
        (∫ y : ℝ, (zetaSum (Real.exp y) t / (Real.exp y : ℂ) -
          zetaSum (Real.exp L) t / (Real.exp L : ℂ)) *
            (Real.exp (-(Real.sqrt (a / L) * (y - L)) ^ 2 / 2) : ℂ)) +
      (Real.exp (a * L / 2) : ℂ) * (zetaSum (Real.exp L) t / (Real.exp L : ℂ)) *
        ((Real.sqrt (2 * Real.pi) / Real.sqrt (a / L) : ℝ) : ℂ) := by
  let r := Real.sqrt (a / L)
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos ha hL)
  have hi := (integrable_normalized_zetaSum_gaussian_difference (L := L) hr t).const_mul
    (Real.exp (a * L / 2) : ℂ)
  have hg := ((integrable_centered_gaussian hr L).ofReal).const_mul
    ((Real.exp (a * L / 2) : ℂ) * (zetaSum (Real.exp L) t / (Real.exp L : ℂ)))
  have he : (fun y : ℝ => zetaSum (Real.exp y) t *
      (Real.exp ((a - 1) * y - (a / L) * y ^ 2 / 2) : ℂ)) =
      (fun y : ℝ => (Real.exp (a * L / 2) : ℂ) *
        ((zetaSum (Real.exp y) t / (Real.exp y : ℂ) -
          zetaSum (Real.exp L) t / (Real.exp L : ℂ)) *
            (Real.exp (-(r * (y - L)) ^ 2 / 2) : ℂ)) +
        ((Real.exp (a * L / 2) : ℂ) * (zetaSum (Real.exp L) t / (Real.exp L : ℂ))) *
          (Real.exp (-(r * (y - L)) ^ 2 / 2) : ℂ)) := by
    funext y
    rw [source_gaussian_weight_centered ha hL y]
    push_cast
    dsimp only [r]
    ring
  rw [he]
  have hadd := integral_add hi hg
  simp only [integral_const_mul, integral_ofReal, integral_centered_gaussian hr L] at hadd
  exact hadd

/-- Full source-normalized Gaussian evaluation at the actual maximizing twist. -/
theorem exists_maximizingTwist_source_gaussian_error :
    ∃ L₀ : ℝ, 16 ≤ L₀ ∧ ∀ x t t₀ : ℝ, 1 < x → L₀ ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → ∀ a : ℝ, 0 < a → a ≤ 1 / 2 →
      ‖(Real.sqrt (2 * Real.pi * (a / Real.log x)) : ℂ) *
        (∫ y : ℝ, zetaSum (Real.exp y) (t - t₀) *
          (Real.exp ((a - 1) * y - (a / Real.log x) * y ^ 2 / 2) : ℂ)) -
        (2 * Real.pi : ℂ) * (Real.exp (a * Real.log x / 2) : ℂ) *
          (zetaSum (Real.exp (Real.log x)) (t - t₀) / (Real.exp (Real.log x) : ℂ))‖ ≤
      (Real.sqrt (2 * Real.pi) * dilationLipschitzConstant * gaussianMomentConstant) *
        Real.exp (a * Real.log x / 2) / (a * Real.log x) ^ (1 / 6 : ℝ) := by
  obtain ⟨L₀, hL₀, hconc⟩ := exists_maximizingTwist_gaussian_concentration
  refine ⟨L₀, hL₀, ?_⟩
  intro x t t₀ hx hlog hmax ht₀ a ha ha2
  let L := Real.log x
  let r := Real.sqrt (a / L)
  let E := Real.exp (a * L / 2)
  let F := zetaSum (Real.exp L) (t - t₀) / (Real.exp L : ℂ)
  let J := ∫ y : ℝ, (zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ) - F) *
    (Real.exp (-(r * (y - L)) ^ 2 / 2) : ℂ)
  have hL : 0 < L := Real.log_pos hx
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos ha hL)
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hL).mpr (by
    have : 16 ≤ L := hL₀.trans hlog
    linarith))
  have hj : ‖J‖ ≤ dilationLipschitzConstant * gaussianMomentConstant / r /
      (r * L) ^ (1 / 3 : ℝ) := hconc x t t₀ hx hlog hmax ht₀ r hr hr1
  have hsqrt : Real.sqrt (2 * Real.pi * (a / L)) = Real.sqrt (2 * Real.pi) * r :=
    Real.sqrt_mul (by positivity) _
  have hc : Real.sqrt (2 * Real.pi * (a / L)) * (Real.sqrt (2 * Real.pi) / r) =
      2 * Real.pi := by
    rw [hsqrt]
    calc
      _ = Real.sqrt (2 * Real.pi) ^ 2 := by field_simp
      _ = _ := Real.sq_sqrt (by positivity)
  have hcC : (Real.sqrt (2 * Real.pi * (a / L)) : ℂ) *
      ((Real.sqrt (2 * Real.pi) / r : ℝ) : ℂ) = (2 * Real.pi : ℂ) := by
    exact_mod_cast hc
  have hsplit := source_gaussian_integral_centered ha hL (t - t₀)
  change (∫ y : ℝ, zetaSum (Real.exp y) (t - t₀) *
    (Real.exp ((a - 1) * y - (a / L) * y ^ 2 / 2) : ℂ)) =
    (E : ℂ) * J + (E : ℂ) * F * ((Real.sqrt (2 * Real.pi) / r : ℝ) : ℂ) at hsplit
  change ‖(Real.sqrt (2 * Real.pi * (a / L)) : ℂ) * _ -
    (2 * Real.pi : ℂ) * (E : ℂ) * F‖ ≤ _
  rw [hsplit]
  have he : (Real.sqrt (2 * Real.pi * (a / L)) : ℂ) *
      ((E : ℂ) * J + (E : ℂ) * F * ((Real.sqrt (2 * Real.pi) / r : ℝ) : ℂ)) -
      (2 * Real.pi : ℂ) * (E : ℂ) * F =
      (Real.sqrt (2 * Real.pi * (a / L)) : ℂ) * (E : ℂ) * J := by
    linear_combination hcC * (E : ℂ) * F
  rw [he, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.sqrt (2 * Real.pi * (a / L)) * E *
        (dilationLipschitzConstant * gaussianMomentConstant / r /
          (r * L) ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ = _ := by
      rw [hsqrt, source_gaussian_width_third ha hL]
      dsimp only [E, L]
      field_simp

end
end DongWangWangZhang2026
