import GafniTao.PintzZetaAFEContour

/-!
# Removal of the horizontal sides of the single-zeta AFE contour

The fixed quadratic Gaussian dominates the audited order-`3/2` growth of
the completed-xi numerator.  All constants here are allowed to depend on the
fixed point `s` and contour width `c`; no height-uniform estimate is claimed
at this stage.
-/

open Complex Filter MeasureTheory Set Topology

noncomputable section

namespace GafniTao

open RiemannZeta.GuthMaynard

theorem one_add_norm_add_horizontal_le
    (s : ℂ) (c H x : ℝ) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hx : x ∈ Set.uIcc (-c) c) :
    1 + ‖s + ((x : ℂ) + (H : ℂ) * I)‖ ≤
      1 + ‖s‖ + c + H := by
  have hxc : |x| ≤ c := by
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  calc
    1 + ‖s + ((x : ℂ) + (H : ℂ) * I)‖
        ≤ 1 + (‖s‖ + ‖(x : ℂ) + (H : ℂ) * I‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 1 + ‖s‖ + (|x| + H) := by
      rw [show 1 + (‖s‖ + ‖(x : ℂ) + (H : ℂ) * I‖) =
          1 + ‖s‖ + ‖(x : ℂ) + (H : ℂ) * I‖ by ring]
      gcongr
      calc
        ‖(x : ℂ) + (H : ℂ) * I‖
            ≤ ‖(x : ℂ)‖ + ‖(H : ℂ) * I‖ := norm_add_le _ _
        _ = |x| + H := by simp [Real.norm_eq_abs, abs_of_nonneg hH]
    _ ≤ 1 + ‖s‖ + c + H := by linarith

/-- Pointwise upper bound on either horizontal side. -/
theorem exists_pintzZetaAFEContourIntegrand_horizontal_bound
    (s : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, C > 0 ∧ ∀ H : ℝ, H ≥ 1 → ∀ x ∈ Set.uIcc (-c) c,
      ‖pintzZetaAFEContourIntegrand s
          ((x : ℂ) + (H : ℂ) * I)‖ ≤
        Real.exp (100 * c ^ 2 - H ^ 2 +
          C * (1 + ‖s‖ + c + H) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hxi⟩ :=
    exists_completedXiNumerator_order_three_halves_bound
  refine ⟨C, hC, ?_⟩
  intro H hH x hx
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have harg := one_add_norm_add_horizontal_le s c H x hc hH0 hx
  have hpow :
      (1 + ‖s + ((x : ℂ) + (H : ℂ) * I)‖) ^ (3 / 2 : ℝ) ≤
        (1 + ‖s‖ + c + H) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) harg (by norm_num)
  have hxiBound :
      ‖completedXiNumerator
        (s + ((x : ℂ) + (H : ℂ) * I))‖ ≤
        Real.exp (C * (1 + ‖s‖ + c + H) ^ (3 / 2 : ℝ)) :=
    (hxi _).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hC.le))
  have hxabs : |x| ≤ c := by
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hxsq : x ^ 2 ≤ c ^ 2 := by
    have hsquare := mul_self_le_mul_self (abs_nonneg x) hxabs
    calc
      x ^ 2 = |x| ^ 2 := by rw [sq_abs]
      _ ≤ c ^ 2 := by simpa only [pow_two] using hsquare
  have hgauss :
      ‖Complex.exp (100 * (((x : ℂ) + (H : ℂ) * I) ^ 2))‖ ≤
        Real.exp (100 * c ^ 2 - H ^ 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : ((((x : ℂ) + (H : ℂ) * I) ^ 2).re) =
        x ^ 2 - H ^ 2 := by
      simp [pow_two, mul_re, mul_im]
    norm_num [mul_re, hre]
    nlinarith [sq_nonneg H]
  have hwNorm : 1 ≤ ‖(x : ℂ) + (H : ℂ) * I‖ := by
    have himle := Complex.abs_im_le_norm ((x : ℂ) + (H : ℂ) * I)
    have himle' : H ≤ ‖(x : ℂ) + (H : ℂ) * I‖ := by
      simpa [abs_of_nonneg hH0] using himle
    linarith
  unfold pintzZetaAFEContourIntegrand pintzZetaAFEContourNumerator
  rw [norm_div, norm_mul]
  calc
    (‖Complex.exp (100 * (((x : ℂ) + (H : ℂ) * I) ^ 2))‖ *
          ‖completedXiNumerator
            (s + ((x : ℂ) + (H : ℂ) * I))‖) /
        ‖(x : ℂ) + (H : ℂ) * I‖
        ≤ (Real.exp (100 * c ^ 2 - H ^ 2) *
            Real.exp (C * (1 + ‖s‖ + c + H) ^ (3 / 2 : ℝ))) / 1 := by
          gcongr
    _ = Real.exp (100 * c ^ 2 - H ^ 2 +
          C * (1 + ‖s‖ + c + H) ^ (3 / 2 : ℝ)) := by
      rw [div_one, Real.exp_add]

theorem tendsto_hIntegral_pintzZetaAFE_top_zero
    (s : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun H : ℝ =>
      HIntegral (pintzZetaAFEContourIntegrand s) (-c) c H)
      atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pintzZetaAFEContourIntegrand_horizontal_bound s c hc
  let A : ℝ := 1 + ‖s‖ + c
  let envelope : ℝ → ℝ := fun H =>
    Real.exp (100 * c ^ 2 - H ^ 2 +
      C * (A + H) ^ (3 / 2 : ℝ))
  have henv0 : Tendsto envelope atTop (nhds 0) := by
    exact tendsto_exp_const_sub_sq_add_three_halves A C (100 * c ^ 2)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral (pintzZetaAFEContourIntegrand s) (-c) c H‖ ≤
        envelope H * |c - (-c)| by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.uIcc (-c) c := Set.uIoc_subset_uIcc hx
      simpa [envelope, A, add_assoc] using hbound H hH x hx')
  simpa using henv0.mul_const |c - (-c)|

theorem tendsto_hIntegral'_pintzZetaAFE_top_zero
    (s : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun H : ℝ =>
      HIntegral' (pintzZetaAFEContourIntegrand s) (-c) c H)
      atTop (nhds 0) := by
  unfold HIntegral'
  simpa using
    (tendsto_hIntegral_pintzZetaAFE_top_zero s c hc).const_smul
      (1 / (2 * Real.pi * I))

#print axioms exists_pintzZetaAFEContourIntegrand_horizontal_bound
#print axioms tendsto_hIntegral'_pintzZetaAFE_top_zero

end GafniTao
