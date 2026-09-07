import RiemannZeta.GuthMaynard.HughesYoungGammaDerivatives
import RiemannZeta.GuthMaynard.HughesYoungDFIProfile

open Complex Filter Set Topology
open Classical
open scoped ContDiff

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Height jets of the Hughes--Young Gamma quotient

Hughes--Young equation (65) differentiates the paired quotient of four real
Gamma factors in the physical height.  The definitions below expose the four
half-arguments of the ordinary Gamma function.  Keeping the shifted and
unshifted arguments paired is essential: their logarithmic derivatives differ
by one small displacement and therefore gain an inverse power of the height.
-/

/-- The `hughesYoungGammaPlusCenter` definition used by the source-facing construction in `HughesYoungGammaRatioJets`. -/
noncomputable def hughesYoungGammaPlusCenter (t : ℝ) : ℂ :=
  (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2

/-- The `hughesYoungGammaPlusShift` definition used by the source-facing construction in `HughesYoungGammaRatioJets`. -/
noncomputable def hughesYoungGammaPlusShift (t c u : ℝ) : ℂ :=
  (((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I) / 2

/-- The `hughesYoungGammaMinusCenter` definition used by the source-facing construction in `HughesYoungGammaRatioJets`. -/
noncomputable def hughesYoungGammaMinusCenter (t : ℝ) : ℂ :=
  (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) / 2

/-- The `hughesYoungGammaMinusShift` definition used by the source-facing construction in `HughesYoungGammaRatioJets`. -/
noncomputable def hughesYoungGammaMinusShift (t c u : ℝ) : ℂ :=
  (((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I) / 2

@[simp] theorem hughesYoungGammaPlusCenter_re (t : ℝ) :
    (hughesYoungGammaPlusCenter t).re = 1 / 4 := by
  simp [hughesYoungGammaPlusCenter]
  ring

@[simp] theorem hughesYoungGammaPlusCenter_im (t : ℝ) :
    (hughesYoungGammaPlusCenter t).im = t / 2 := by
  simp [hughesYoungGammaPlusCenter]

@[simp] theorem hughesYoungGammaPlusShift_re (t c u : ℝ) :
    (hughesYoungGammaPlusShift t c u).re = 1 / 4 + c / 2 := by
  simp [hughesYoungGammaPlusShift]
  ring

@[simp] theorem hughesYoungGammaPlusShift_im (t c u : ℝ) :
    (hughesYoungGammaPlusShift t c u).im = (t + u) / 2 := by
  simp [hughesYoungGammaPlusShift]

@[simp] theorem hughesYoungGammaMinusCenter_re (t : ℝ) :
    (hughesYoungGammaMinusCenter t).re = 1 / 4 := by
  simp [hughesYoungGammaMinusCenter]
  ring

@[simp] theorem hughesYoungGammaMinusCenter_im (t : ℝ) :
    (hughesYoungGammaMinusCenter t).im = -t / 2 := by
  simp [hughesYoungGammaMinusCenter]

@[simp] theorem hughesYoungGammaMinusShift_re (t c u : ℝ) :
    (hughesYoungGammaMinusShift t c u).re = 1 / 4 + c / 2 := by
  simp [hughesYoungGammaMinusShift]
  ring

@[simp] theorem hughesYoungGammaMinusShift_im (t c u : ℝ) :
    (hughesYoungGammaMinusShift t c u).im = (-t + u) / 2 := by
  simp [hughesYoungGammaMinusShift]

theorem hughesYoungGammaPlus_segment_geometry
    {T t c u : ℝ} (hT : 16 ≤ T) (ht0 : T / 4 ≤ t)
    (hc : 0 ≤ c) (hu : |u| ≤ T / 8) :
    ∀ w ∈ segment ℝ (hughesYoungGammaPlusCenter t)
        (hughesYoungGammaPlusShift t c u),
      1 / 4 ≤ w.re ∧ T / 16 ≤ |w.im| := by
  intro w hw
  rcases hw with ⟨a, b, ha, hb, hab, rfl⟩
  have huLower : -T / 8 ≤ u := by
    have := neg_le_of_abs_le hu
    linarith
  have hcenterRe : (1 / 4 : ℝ) ≤ 1 / 4 := le_rfl
  have hshiftRe : (1 / 4 : ℝ) ≤ 1 / 4 + c / 2 := by linarith
  have hcenterIm : T / 16 ≤ t / 2 := by linarith
  have hshiftIm : T / 16 ≤ (t + u) / 2 := by linarith
  constructor
  · simp only [add_re, smul_re, hughesYoungGammaPlusCenter_re,
      hughesYoungGammaPlusShift_re, smul_eq_mul]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hcenterRe),
      mul_nonneg hb (sub_nonneg.mpr hshiftRe)]
  · have him : T / 16 ≤
        (a • hughesYoungGammaPlusCenter t +
          b • hughesYoungGammaPlusShift t c u).im := by
      simp only [add_im, smul_im, hughesYoungGammaPlusCenter_im,
        hughesYoungGammaPlusShift_im, smul_eq_mul]
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hcenterIm),
        mul_nonneg hb (sub_nonneg.mpr hshiftIm)]
    rw [abs_of_nonneg (le_trans (by positivity) him)]
    exact him

theorem hughesYoungGammaMinus_segment_geometry
    {T t c u : ℝ} (hT : 16 ≤ T) (ht0 : T / 4 ≤ t)
    (hc : 0 ≤ c) (hu : |u| ≤ T / 8) :
    ∀ w ∈ segment ℝ (hughesYoungGammaMinusCenter t)
        (hughesYoungGammaMinusShift t c u),
      1 / 4 ≤ w.re ∧ T / 16 ≤ |w.im| := by
  intro w hw
  rcases hw with ⟨a, b, ha, hb, hab, rfl⟩
  have huUpper : u ≤ T / 8 := le_of_abs_le hu
  have hcenterRe : (1 / 4 : ℝ) ≤ 1 / 4 := le_rfl
  have hshiftRe : (1 / 4 : ℝ) ≤ 1 / 4 + c / 2 := by linarith
  have hcenterIm : -t / 2 ≤ -T / 16 := by linarith
  have hshiftIm : (-t + u) / 2 ≤ -T / 16 := by linarith
  constructor
  · simp only [add_re, smul_re, hughesYoungGammaMinusCenter_re,
      hughesYoungGammaMinusShift_re, smul_eq_mul]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hcenterRe),
      mul_nonneg hb (sub_nonneg.mpr hshiftRe)]
  · have him :
        (a • hughesYoungGammaMinusCenter t +
          b • hughesYoungGammaMinusShift t c u).im ≤ -T / 16 := by
      simp only [add_im, smul_im, hughesYoungGammaMinusCenter_im,
        hughesYoungGammaMinusShift_im, smul_eq_mul]
      nlinarith [mul_nonneg ha (sub_nonneg.mpr (neg_le_neg hcenterIm)),
        mul_nonneg hb (sub_nonneg.mpr (neg_le_neg hshiftIm))]
    have hnonpos :
        (a • hughesYoungGammaMinusCenter t +
          b • hughesYoungGammaMinusShift t c u).im ≤ 0 := by
      linarith
    rw [abs_of_nonpos hnonpos]
    linarith

theorem hughesYoungGammaPlusShift_sub_center (t c u : ℝ) :
    hughesYoungGammaPlusShift t c u - hughesYoungGammaPlusCenter t =
      ((c : ℂ) + (u : ℂ) * I) / 2 := by
  unfold hughesYoungGammaPlusShift hughesYoungGammaPlusCenter
  push_cast
  ring

theorem hughesYoungGammaMinusShift_sub_center (t c u : ℝ) :
    hughesYoungGammaMinusShift t c u - hughesYoungGammaMinusCenter t =
      ((c : ℂ) + (u : ℂ) * I) / 2 := by
  unfold hughesYoungGammaMinusShift hughesYoungGammaMinusCenter
  push_cast
  ring

theorem norm_hughesYoungGamma_displacement_le
    {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ‖((c : ℂ) + (u : ℂ) * I) / 2‖ ≤ 1 + |u| := by
  calc
    ‖((c : ℂ) + (u : ℂ) * I) / 2‖ ≤
        (‖(c : ℂ)‖ + ‖(u : ℂ) * I‖) / ‖(2 : ℂ)‖ := by
      rw [norm_div]
      gcongr
      exact norm_add_le _ _
    _ = (c + |u|) / 2 := by
      rw [norm_mul, norm_I, mul_one, norm_real, norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0]
      norm_num
    _ ≤ 1 + |u| := by
      have hu0 := abs_nonneg u
      linarith

/-- An explicit constant for the all-orders shifted/unshifted digamma
difference.  The `j = 0` branch uses the trigamma mean-value estimate; every
positive branch uses the next polygamma derivative. -/
noncomputable def hughesYoungDigammaDifferenceConstant (j : ℕ) : ℝ :=
  if j = 0 then 2 * (3 + 4 ^ 2)
  else (j + 1).factorial * (3 + 4 ^ (j + 2))

theorem hughesYoungDigammaDifferenceConstant_pos (j : ℕ) :
    0 < hughesYoungDigammaDifferenceConstant j := by
  unfold hughesYoungDigammaDifferenceConstant
  split_ifs <;> positivity

theorem norm_iteratedDeriv_digamma_plus_shift_sub_le
    {j : ℕ} {T t c u : ℝ} (hT : 16 ≤ T) (ht0 : T / 4 ≤ t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : |u| ≤ T / 8) :
    ‖iteratedDeriv j Complex.digamma (hughesYoungGammaPlusShift t c u) -
        iteratedDeriv j Complex.digamma (hughesYoungGammaPlusCenter t)‖ ≤
      hughesYoungDigammaDifferenceConstant j *
        (T / 16)⁻¹ ^ (j + 1) * (1 + |u|) := by
  have hY : (1 : ℝ) ≤ T / 16 := by linarith
  have hdisp := norm_hughesYoungGamma_displacement_le (u := u) hc0 hc1
  cases j with
  | zero =>
      have hraw := norm_digamma_sub_le (a := (1 / 4 : ℝ)) (Y := T / 16)
        (by norm_num) hY
        (hughesYoungGammaPlus_segment_geometry hT ht0 hc0 hu)
      simp only [iteratedDeriv_zero]
      rw [hughesYoungGammaPlusShift_sub_center] at hraw
      have hconstant : 2 * (3 + (min (1 / 4 : ℝ) 1)⁻¹ ^ 2) =
          hughesYoungDigammaDifferenceConstant 0 := by
        norm_num [hughesYoungDigammaDifferenceConstant]
      rw [hconstant] at hraw
      simpa only [zero_add, pow_one] using
        hraw.trans (mul_le_mul_of_nonneg_left hdisp
          (mul_nonneg (hughesYoungDigammaDifferenceConstant_pos 0).le
            (inv_nonneg.mpr (by linarith))))
  | succ n =>
      have hraw := norm_iteratedDeriv_digamma_sub_le (j := n + 1)
        (by omega) (a := (1 / 4 : ℝ)) (Y := T / 16)
        (by norm_num) hY
        (hughesYoungGammaPlus_segment_geometry hT ht0 hc0 hu)
      rw [hughesYoungGammaPlusShift_sub_center] at hraw
      have hconstant : (n + 1 + 1).factorial *
          (3 + (min (1 / 4 : ℝ) 1)⁻¹ ^ (n + 1 + 2)) =
          hughesYoungDigammaDifferenceConstant (n + 1) := by
        norm_num [hughesYoungDigammaDifferenceConstant]
      rw [hconstant] at hraw
      exact hraw.trans (mul_le_mul_of_nonneg_left hdisp
        (mul_nonneg (hughesYoungDigammaDifferenceConstant_pos (n + 1)).le
          (pow_nonneg (inv_nonneg.mpr (by linarith)) _)))

theorem norm_iteratedDeriv_digamma_minus_shift_sub_le
    {j : ℕ} {T t c u : ℝ} (hT : 16 ≤ T) (ht0 : T / 4 ≤ t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : |u| ≤ T / 8) :
    ‖iteratedDeriv j Complex.digamma (hughesYoungGammaMinusShift t c u) -
        iteratedDeriv j Complex.digamma (hughesYoungGammaMinusCenter t)‖ ≤
      hughesYoungDigammaDifferenceConstant j *
        (T / 16)⁻¹ ^ (j + 1) * (1 + |u|) := by
  have hY : (1 : ℝ) ≤ T / 16 := by linarith
  have hdisp := norm_hughesYoungGamma_displacement_le (u := u) hc0 hc1
  cases j with
  | zero =>
      have hraw := norm_digamma_sub_le (a := (1 / 4 : ℝ)) (Y := T / 16)
        (by norm_num) hY
        (hughesYoungGammaMinus_segment_geometry hT ht0 hc0 hu)
      simp only [iteratedDeriv_zero]
      rw [hughesYoungGammaMinusShift_sub_center] at hraw
      have hconstant : 2 * (3 + (min (1 / 4 : ℝ) 1)⁻¹ ^ 2) =
          hughesYoungDigammaDifferenceConstant 0 := by
        norm_num [hughesYoungDigammaDifferenceConstant]
      rw [hconstant] at hraw
      simpa only [zero_add, pow_one] using
        hraw.trans (mul_le_mul_of_nonneg_left hdisp
          (mul_nonneg (hughesYoungDigammaDifferenceConstant_pos 0).le
            (inv_nonneg.mpr (by linarith))))
  | succ n =>
      have hraw := norm_iteratedDeriv_digamma_sub_le (j := n + 1)
        (by omega) (a := (1 / 4 : ℝ)) (Y := T / 16)
        (by norm_num) hY
        (hughesYoungGammaMinus_segment_geometry hT ht0 hc0 hu)
      rw [hughesYoungGammaMinusShift_sub_center] at hraw
      have hconstant : (n + 1 + 1).factorial *
          (3 + (min (1 / 4 : ℝ) 1)⁻¹ ^ (n + 1 + 2)) =
          hughesYoungDigammaDifferenceConstant (n + 1) := by
        norm_num [hughesYoungDigammaDifferenceConstant]
      rw [hconstant] at hraw
      exact hraw.trans (mul_le_mul_of_nonneg_left hdisp
        (mul_nonneg (hughesYoungDigammaDifferenceConstant_pos (n + 1)).le
          (pow_nonneg (inv_nonneg.mpr (by linarith)) _)))

private theorem hasDerivAt_iteratedDeriv_digamma_all
    (j : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (iteratedDeriv j Complex.digamma)
      (iteratedDeriv (j + 1) Complex.digamma z) z := by
  cases j with
  | zero =>
      have h := hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one hz
      simpa only [iteratedDeriv_zero, zero_add, iteratedDeriv_one, h.deriv] using h
  | succ n =>
      exact hasDerivAt_iteratedDeriv_digamma (j := n + 1) (by omega) hz

/-- The `hughesYoungPlusDigammaDifference` definition used by the source-facing construction in `HughesYoungGammaRatioJets`. -/
noncomputable def hughesYoungPlusDigammaDifference
    (j : ℕ) (t c u : ℝ) : ℂ :=
  iteratedDeriv j Complex.digamma (hughesYoungGammaPlusShift t c u) -
    iteratedDeriv j Complex.digamma (hughesYoungGammaPlusCenter t)

/-- The `hughesYoungMinusDigammaDifference` definition used by the source-facing construction in `HughesYoungGammaRatioJets`. -/
noncomputable def hughesYoungMinusDigammaDifference
    (j : ℕ) (t c u : ℝ) : ℂ :=
  iteratedDeriv j Complex.digamma (hughesYoungGammaMinusShift t c u) -
    iteratedDeriv j Complex.digamma (hughesYoungGammaMinusCenter t)

theorem hasDerivAt_hughesYoungPlusDigammaDifference
    (j : ℕ) {t c u : ℝ} (hc : 0 < 1 / 2 + c) :
    HasDerivAt (fun x : ℝ => hughesYoungPlusDigammaDifference j x c u)
      ((I / 2) * hughesYoungPlusDigammaDifference (j + 1) t c u) t := by
  let φ₁ : ℂ → ℂ := fun q =>
    (((1 / 2 + c : ℝ) : ℂ) + (q + (u : ℂ)) * I) / 2
  let φ₀ : ℂ → ℂ := fun q =>
    (((1 / 2 : ℝ) : ℂ) + q * I) / 2
  have hφ₁ : HasDerivAt φ₁ (I / 2) (t : ℂ) := by
    dsimp [φ₁]
    convert (((hasDerivAt_id (t : ℂ)).add_const (u : ℂ)).mul_const I).const_add
      (((1 / 2 + c : ℝ) : ℂ)) |>.div_const 2 using 1
    all_goals ring
  have hφ₀ : HasDerivAt φ₀ (I / 2) (t : ℂ) := by
    dsimp [φ₀]
    convert ((hasDerivAt_id (t : ℂ)).mul_const I).const_add
      (((1 / 2 : ℝ) : ℂ)) |>.div_const 2 using 1
    all_goals ring
  have h₁pos : 0 < (φ₁ (t : ℂ)).re := by
    dsimp [φ₁]
    simp
    linarith
  have h₀pos : 0 < (φ₀ (t : ℂ)).re := by
    dsimp [φ₀]
    norm_num
  have h₁ := ((hasDerivAt_iteratedDeriv_digamma_all j h₁pos).comp
    (t : ℂ) hφ₁).comp_ofReal
  have h₀ := ((hasDerivAt_iteratedDeriv_digamma_all j h₀pos).comp
    (t : ℂ) hφ₀).comp_ofReal
  have h₁' : HasDerivAt (fun x : ℝ =>
      iteratedDeriv j Complex.digamma (hughesYoungGammaPlusShift x c u))
      ((I / 2) * iteratedDeriv (j + 1) Complex.digamma
        (hughesYoungGammaPlusShift t c u)) t := by
    convert h₁ using 1
    · funext x
      congr 1
      simp only [φ₁, hughesYoungGammaPlusShift]
      push_cast
      ring
    · simp only [φ₁, hughesYoungGammaPlusShift]
      push_cast
      ring
  have h₀' : HasDerivAt (fun x : ℝ =>
      iteratedDeriv j Complex.digamma (hughesYoungGammaPlusCenter x))
      ((I / 2) * iteratedDeriv (j + 1) Complex.digamma
        (hughesYoungGammaPlusCenter t)) t := by
    convert h₀ using 1
    all_goals simp only [φ₀, hughesYoungGammaPlusCenter]
    all_goals push_cast
    all_goals ring
  convert h₁'.sub h₀' using 1
  all_goals simp only [hughesYoungPlusDigammaDifference]
  all_goals ring

theorem hasDerivAt_hughesYoungMinusDigammaDifference
    (j : ℕ) {t c u : ℝ} (hc : 0 < 1 / 2 + c) :
    HasDerivAt (fun x : ℝ => hughesYoungMinusDigammaDifference j x c u)
      ((-I / 2) * hughesYoungMinusDigammaDifference (j + 1) t c u) t := by
  let φ₁ : ℂ → ℂ := fun q =>
    (((1 / 2 + c : ℝ) : ℂ) + (-q + (u : ℂ)) * I) / 2
  let φ₀ : ℂ → ℂ := fun q =>
    (((1 / 2 : ℝ) : ℂ) + (-q) * I) / 2
  have hφ₁ : HasDerivAt φ₁ (-I / 2) (t : ℂ) := by
    dsimp [φ₁]
    convert ((((hasDerivAt_id (t : ℂ)).neg.add_const (u : ℂ)).mul_const I).const_add
      (((1 / 2 + c : ℝ) : ℂ))).div_const 2 using 1
    all_goals ring
  have hφ₀ : HasDerivAt φ₀ (-I / 2) (t : ℂ) := by
    dsimp [φ₀]
    convert (((hasDerivAt_id (t : ℂ)).neg.mul_const I).const_add
      (((1 / 2 : ℝ) : ℂ))).div_const 2 using 1
    all_goals ring
  have h₁pos : 0 < (φ₁ (t : ℂ)).re := by
    dsimp [φ₁]
    simp
    linarith
  have h₀pos : 0 < (φ₀ (t : ℂ)).re := by
    dsimp [φ₀]
    norm_num
  have h₁ := ((hasDerivAt_iteratedDeriv_digamma_all j h₁pos).comp
    (t : ℂ) hφ₁).comp_ofReal
  have h₀ := ((hasDerivAt_iteratedDeriv_digamma_all j h₀pos).comp
    (t : ℂ) hφ₀).comp_ofReal
  have h₁' : HasDerivAt (fun x : ℝ =>
      iteratedDeriv j Complex.digamma (hughesYoungGammaMinusShift x c u))
      ((-I / 2) * iteratedDeriv (j + 1) Complex.digamma
        (hughesYoungGammaMinusShift t c u)) t := by
    convert h₁ using 1
    · funext x
      congr 1
      simp only [φ₁, hughesYoungGammaMinusShift]
      push_cast
      ring
    · simp only [φ₁, hughesYoungGammaMinusShift]
      push_cast
      ring
  have h₀' : HasDerivAt (fun x : ℝ =>
      iteratedDeriv j Complex.digamma (hughesYoungGammaMinusCenter x))
      ((-I / 2) * iteratedDeriv (j + 1) Complex.digamma
        (hughesYoungGammaMinusCenter t)) t := by
    convert h₀ using 1
    funext x
    congr 1
    simp only [φ₀, hughesYoungGammaMinusCenter]
    push_cast
    ring
    simp only [φ₀, hughesYoungGammaMinusCenter]
    push_cast
    ring
  convert h₁'.sub h₀' using 1
  all_goals simp only [hughesYoungMinusDigammaDifference]
  all_goals ring

/-- The `j`-th physical-height derivative of the logarithmic derivative of
the complete paired Gamma quotient. -/
noncomputable def hughesYoungGammaLogJet
    (j : ℕ) (t c u : ℝ) : ℂ :=
  I * ((I / 2) ^ j * hughesYoungPlusDigammaDifference j t c u -
    (-I / 2) ^ j * hughesYoungMinusDigammaDifference j t c u)

theorem hasDerivAt_hughesYoungGammaLogJet
    (j : ℕ) {t c u : ℝ} (hc : 0 < 1 / 2 + c) :
    HasDerivAt (fun x : ℝ => hughesYoungGammaLogJet j x c u)
      (hughesYoungGammaLogJet (j + 1) t c u) t := by
  have hp := (hasDerivAt_hughesYoungPlusDigammaDifference
    (t := t) (c := c) (u := u) j hc).const_mul
    ((I / 2) ^ j)
  have hm := (hasDerivAt_hughesYoungMinusDigammaDifference
    (t := t) (c := c) (u := u) j hc).const_mul
    ((-I / 2) ^ j)
  have h := (hp.sub hm).const_mul I
  convert h using 1
  simp only [hughesYoungGammaLogJet, pow_succ]
  ring

theorem norm_hughesYoungGammaLogJet_le
    {j : ℕ} {T t c u : ℝ} (hT : 16 ≤ T) (ht0 : T / 4 ≤ t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : |u| ≤ T / 8) :
    ‖hughesYoungGammaLogJet j t c u‖ ≤
      2 * hughesYoungDigammaDifferenceConstant j *
        (T / 16)⁻¹ ^ (j + 1) * (1 + |u|) := by
  have hp := norm_iteratedDeriv_digamma_plus_shift_sub_le
    (j := j) hT ht0 hc0 hc1 hu
  have hm := norm_iteratedDeriv_digamma_minus_shift_sub_le
    (j := j) hT ht0 hc0 hc1 hu
  have hhalf : ‖(I / 2 : ℂ)‖ ≤ 1 := by norm_num
  have hneghalf : ‖(-I / 2 : ℂ)‖ ≤ 1 := by norm_num
  unfold hughesYoungGammaLogJet
  rw [norm_mul, norm_I]
  calc
    1 * ‖(I / 2) ^ j * hughesYoungPlusDigammaDifference j t c u -
          (-I / 2) ^ j * hughesYoungMinusDigammaDifference j t c u‖ ≤
        ‖(I / 2) ^ j * hughesYoungPlusDigammaDifference j t c u‖ +
          ‖(-I / 2) ^ j * hughesYoungMinusDigammaDifference j t c u‖ := by
      simpa using (norm_sub_le
        ((I / 2) ^ j * hughesYoungPlusDigammaDifference j t c u)
        ((-I / 2) ^ j * hughesYoungMinusDigammaDifference j t c u))
    _ ≤ 1 ^ j * ‖hughesYoungPlusDigammaDifference j t c u‖ +
          1 ^ j * ‖hughesYoungMinusDigammaDifference j t c u‖ := by
      simp only [norm_mul, norm_pow]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hhalf _) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hneghalf _) (norm_nonneg _)
    _ ≤ 2 * hughesYoungDigammaDifferenceConstant j *
          (T / 16)⁻¹ ^ (j + 1) * (1 + |u|) := by
      have hp' : ‖hughesYoungPlusDigammaDifference j t c u‖ ≤
          hughesYoungDigammaDifferenceConstant j *
            (T / 16)⁻¹ ^ (j + 1) * (1 + |u|) := by
        simpa only [hughesYoungPlusDigammaDifference] using hp
      have hm' : ‖hughesYoungMinusDigammaDifference j t c u‖ ≤
          hughesYoungDigammaDifferenceConstant j *
            (T / 16)⁻¹ ^ (j + 1) * (1 + |u|) := by
        simpa only [hughesYoungMinusDigammaDifference] using hm
      simpa only [one_pow, one_mul] using
        (calc
          ‖hughesYoungPlusDigammaDifference j t c u‖ +
              ‖hughesYoungMinusDigammaDifference j t c u‖ ≤
              (hughesYoungDigammaDifferenceConstant j *
                  (T / 16)⁻¹ ^ (j + 1) * (1 + |u|)) +
                (hughesYoungDigammaDifferenceConstant j *
                  (T / 16)⁻¹ ^ (j + 1) * (1 + |u|)) :=
            add_le_add hp' hm'
          _ = 2 * hughesYoungDigammaDifferenceConstant j *
                (T / 16)⁻¹ ^ (j + 1) * (1 + |u|) := by ring)

/-! ## The paired Gamma-ratio differential equation -/

/-- The logarithmic derivative of Deligne's real Gamma factor on the open
right half-plane.  This is proved from the definition of `Gammaℝ`; in
particular, no asymptotic Gamma formula is being assumed. -/
private theorem hasDerivAt_GammaR_eq_mul_logDeriv_of_re_pos
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.Gammaℝ
      (Complex.Gammaℝ z *
        ((-Complex.log (Real.pi : ℂ) + Complex.digamma (z / 2)) / 2)) z := by
  have hpow : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) z := by
    convert (((hasDerivAt_id z).neg.div_const 2).const_cpow
      (c := (Real.pi : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) using 1
  have hzhalf : 0 < (z / 2).re := by
    simpa only [div_ofNat_re] using div_pos hz two_pos
  have hgammaOuter := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos hzhalf
  have hgamma : HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2))
      (Complex.Gamma (z / 2) * Complex.digamma (z / 2) / 2) z := by
    convert hgammaOuter.comp z ((hasDerivAt_id z).div_const 2) using 1
    ring
  unfold Complex.Gammaℝ
  convert hpow.mul hgamma using 1
  ring

/-- Height derivative of one real Gamma factor along an affine vertical
line. -/
private theorem hasDerivAt_GammaR_affine_height
    (a b d t : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ =>
        Complex.Gammaℝ ((a : ℂ) + ((d * x + b : ℝ) : ℂ) * I))
      (((d : ℂ) * I) *
        Complex.Gammaℝ ((a : ℂ) + ((d * t + b : ℝ) : ℂ) * I) *
        ((-Complex.log (Real.pi : ℂ) +
            Complex.digamma
              (((a : ℂ) + ((d * t + b : ℝ) : ℂ) * I) / 2)) / 2)) t := by
  let phi : ℂ → ℂ := fun x =>
    (a : ℂ) + ((d : ℂ) * x + (b : ℂ)) * I
  have hphi : HasDerivAt phi ((d : ℂ) * I) (t : ℂ) := by
    dsimp [phi]
    convert ((((hasDerivAt_id (t : ℂ)).const_mul (d : ℂ)).add_const
      (b : ℂ)).mul_const I).const_add (a : ℂ) using 1
    ring
  have hphiRe : 0 < (phi (t : ℂ)).re := by
    dsimp [phi]
    simpa using ha
  have houter := hasDerivAt_GammaR_eq_mul_logDeriv_of_re_pos hphiRe
  convert (houter.comp (t : ℂ) hphi).comp_ofReal using 1
  · funext x
    congr 1
    dsimp [phi]
    push_cast
    ring
  · dsimp [phi]
    push_cast
    ring

/-- The paired shifted/unshifted Gamma quotient has the exact logarithmic
height derivative used in Hughes--Young (65).  The constant `log pi` terms
cancel before any estimate is taken. -/
theorem hasDerivAt_hughesYoungGammaRatioShift
    {t c u : ℝ} (hc : 0 < 1 / 2 + c) :
    HasDerivAt (fun x : ℝ => hughesYoungGammaRatioShift x c u)
      (hughesYoungGammaRatioShift t c u *
        hughesYoungGammaLogJet 0 t c u) t := by
  let A : ℂ := Complex.Gammaℝ
    (((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)
  let B : ℂ := Complex.Gammaℝ
    (((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I)
  let C : ℂ := Complex.Gammaℝ
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let D : ℂ := Complex.Gammaℝ
    (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)
  let qA : ℂ := -Complex.log (Real.pi : ℂ) +
    Complex.digamma (hughesYoungGammaPlusShift t c u)
  let qB : ℂ := -Complex.log (Real.pi : ℂ) +
    Complex.digamma (hughesYoungGammaMinusShift t c u)
  let qC : ℂ := -Complex.log (Real.pi : ℂ) +
    Complex.digamma (hughesYoungGammaPlusCenter t)
  let qD : ℂ := -Complex.log (Real.pi : ℂ) +
    Complex.digamma (hughesYoungGammaMinusCenter t)
  have hA : HasDerivAt (fun x : ℝ => Complex.Gammaℝ
      (((1 / 2 + c : ℝ) : ℂ) + ((x + u : ℝ) : ℂ) * I))
      (I * A * (qA / 2)) t := by
    convert hasDerivAt_GammaR_affine_height (1 / 2 + c) u 1 t hc using 1
    · funext x
      congr 1
      push_cast
      ring
    · dsimp [A, qA, hughesYoungGammaPlusShift]
      ring_nf
  have hB : HasDerivAt (fun x : ℝ => Complex.Gammaℝ
      (((1 / 2 + c : ℝ) : ℂ) + ((-x + u : ℝ) : ℂ) * I))
      (-I * B * (qB / 2)) t := by
    convert hasDerivAt_GammaR_affine_height (1 / 2 + c) u (-1) t hc using 1
    · funext x
      congr 1
      push_cast
      ring
    · dsimp [B, qB, hughesYoungGammaMinusShift]
      norm_num
  have hC : HasDerivAt (fun x : ℝ => Complex.Gammaℝ
      (((1 / 2 : ℝ) : ℂ) + (x : ℂ) * I))
      (I * C * (qC / 2)) t := by
    convert hasDerivAt_GammaR_affine_height (1 / 2) 0 1 t (by norm_num) using 1
    · funext x
      congr 1
      push_cast
      ring
    · dsimp [C, qC, hughesYoungGammaPlusCenter]
      ring_nf
  have hD : HasDerivAt (fun x : ℝ => Complex.Gammaℝ
      (((1 / 2 : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * I))
      (-I * D * (qD / 2)) t := by
    convert hasDerivAt_GammaR_affine_height (1 / 2) 0 (-1) t (by norm_num) using 1
    · funext x
      congr 1
      push_cast
      ring
    · dsimp [D, qD, hughesYoungGammaMinusCenter]
      norm_num
  have hden : C ^ 2 * D ^ 2 ≠ 0 := by
    apply mul_ne_zero <;> apply pow_ne_zero
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [C])
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [D])
  have hquot := ((hA.pow 2).mul (hB.pow 2)).div
    ((hC.pow 2).mul (hD.pow 2)) hden
  convert hquot using 1
  · funext x
    simp only [hughesYoungGammaRatioShift, afeGammaNormalization,
      afeCriticalPoint]
    push_cast
    congr 1
  · simp only [hughesYoungGammaRatioShift, afeGammaNormalization,
      hughesYoungGammaLogJet, hughesYoungPlusDigammaDifference,
      hughesYoungMinusDigammaDifference, iteratedDeriv_zero,
      afeCriticalPoint]
    dsimp [A, B, C, D, qA, qB, qC, qD]
    push_cast
    field_simp [hden]
    ring

/-- Every physical-height derivative of a log jet is the next corresponding
jet.  This is the exact all-orders input for the complete Bell recurrence. -/
theorem iteratedDeriv_hughesYoungGammaLogJet_eq
    (j n : ℕ) {c : ℝ} (hc : 0 < 1 / 2 + c) (u : ℝ) :
    iteratedDeriv n (fun t : ℝ => hughesYoungGammaLogJet j t c u) =
      fun t : ℝ => hughesYoungGammaLogJet (j + n) t c u := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega, iteratedDeriv_succ, ih]
      funext t
      simpa only [Nat.add_assoc] using
        (hasDerivAt_hughesYoungGammaLogJet (j + n)
          (t := t) (u := u) hc).deriv

theorem contDiff_hughesYoungGammaLogJet
    (j : ℕ) {c : ℝ} (hc : 0 < 1 / 2 + c) (u : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => hughesYoungGammaLogJet j t c u) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _hn
  rw [iteratedDeriv_hughesYoungGammaLogJet_eq j n hc u]
  intro t
  exact (hasDerivAt_hughesYoungGammaLogJet (j + n)
    (t := t) (u := u) hc).differentiableAt

/-- Smoothness of the complete paired quotient, proved on the exact positive
Hughes--Young line. -/
theorem contDiff_hughesYoungGammaRatioShift
    {c : ℝ} (hc : 0 < 1 / 2 + c) (u : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => hughesYoungGammaRatioShift t c u) := by
  have hplus : ContDiff ℝ ∞ (fun t : ℝ => Complex.Gammaℝ
      (((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)) := by
    convert contDiff_GammaR_afe_height c u hc using 1
    funext t
    congr 1
    simp only [afeCriticalPoint]
    push_cast
    ring
  have hminus : ContDiff ℝ ∞ (fun t : ℝ => Complex.Gammaℝ
      (((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I)) := by
    convert (contDiff_GammaR_afe_height c u hc).comp contDiff_neg using 1
    funext t
    congr 1
    simp only [afeCriticalPoint]
    push_cast
    ring
  have hnum := (hplus.pow 2).mul (hminus.pow 2)
  have hden := contDiff_afeGammaNormalization.inv afeGammaNormalization_ne_zero
  simpa only [hughesYoungGammaRatioShift, div_eq_mul_inv] using hnum.mul hden

/-- The complete exponential Bell recurrence generated by the logarithmic
jets.  The `Fin (n+1)` index makes every recursive call structurally smaller
than the successor being defined. -/
noncomputable def hughesYoungGammaRatioBell (c u : ℝ) : ℕ → ℝ → ℂ
  | 0, _ => 1
  | n + 1, t => ∑ k : Fin (n + 1),
      (n.choose k : ℂ) * hughesYoungGammaRatioBell c u k t *
        hughesYoungGammaLogJet (n - k) t c u
termination_by n => n
decreasing_by omega

@[simp] theorem hughesYoungGammaRatioBell_zero
    (c u t : ℝ) : hughesYoungGammaRatioBell c u 0 t = 1 := by
  rw [hughesYoungGammaRatioBell]

theorem hughesYoungGammaRatioBell_succ
    (n : ℕ) (c u t : ℝ) :
    hughesYoungGammaRatioBell c u (n + 1) t =
      ∑ k : Fin (n + 1), (n.choose k : ℂ) *
        hughesYoungGammaRatioBell c u k t *
          hughesYoungGammaLogJet (n - k) t c u := by
  rw [hughesYoungGammaRatioBell]

theorem contDiff_hughesYoungGammaRatioBell
    (n : ℕ) {c : ℝ} (hc : 0 < 1 / 2 + c) (u : ℝ) :
    ContDiff ℝ ∞ (hughesYoungGammaRatioBell c u n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          convert (contDiff_const : ContDiff ℝ ∞ (fun _t : ℝ => (1 : ℂ))) using 1
          funext t
          rw [hughesYoungGammaRatioBell_zero]
      | succ n =>
          have hsum : ContDiff ℝ ∞ (fun t : ℝ =>
              ∑ k : Fin (n + 1), (n.choose k : ℂ) *
                hughesYoungGammaRatioBell c u k t *
                  hughesYoungGammaLogJet (n - k) t c u) := by
            apply ContDiff.sum
            intro k _hk
            exact ((contDiff_const.mul (ih k k.isLt)).mul
              (contDiff_hughesYoungGammaLogJet (n - k) hc u))
          convert hsum using 1
          funext t
          exact hughesYoungGammaRatioBell_succ n c u t

/-- Exact all-orders derivative formula for the paired Gamma quotient. -/
theorem iteratedDeriv_hughesYoungGammaRatioShift_eq
    (n : ℕ) {c : ℝ} (hc : 0 < 1 / 2 + c) (u t : ℝ) :
    iteratedDeriv n (fun x : ℝ => hughesYoungGammaRatioShift x c u) t =
      hughesYoungGammaRatioShift t c u *
        hughesYoungGammaRatioBell c u n t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [iteratedDeriv_succ']
          have hderiv : deriv (fun x : ℝ => hughesYoungGammaRatioShift x c u) =
              fun x : ℝ => hughesYoungGammaRatioShift x c u *
                hughesYoungGammaLogJet 0 x c u := by
            funext x
            exact (hasDerivAt_hughesYoungGammaRatioShift
              (t := x) (u := u) hc).deriv
          rw [hderiv]
          change iteratedDeriv n
            ((fun x : ℝ => hughesYoungGammaRatioShift x c u) *
              fun x : ℝ => hughesYoungGammaLogJet 0 x c u) t = _
          rw [iteratedDeriv_mul
            ((contDiff_hughesYoungGammaRatioShift hc u).contDiffAt.of_le
              (by exact_mod_cast le_top))
            ((contDiff_hughesYoungGammaLogJet 0 hc u).contDiffAt.of_le
              (by exact_mod_cast le_top))]
          rw [hughesYoungGammaRatioBell_succ,
            Finset.sum_fin_eq_sum_range]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k (Finset.mem_range.mp hk)]
          rw [congrFun (iteratedDeriv_hughesYoungGammaLogJet_eq
            0 (n - k) hc u) t]
          simp only [zero_add]
          have hklt : k < n + 1 := Finset.mem_range.mp hk
          split
          · ring
          · contradiction

/-- A scalar majorant for the Bell recurrence. -/
noncomputable def hughesYoungGammaRatioBellConstant : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1),
      n.choose k * hughesYoungGammaRatioBellConstant k *
        (2 * hughesYoungDigammaDifferenceConstant (n - k))
termination_by n => n
decreasing_by omega

@[simp] theorem hughesYoungGammaRatioBellConstant_zero :
    hughesYoungGammaRatioBellConstant 0 = 1 := by
  rw [hughesYoungGammaRatioBellConstant]

theorem hughesYoungGammaRatioBellConstant_succ (n : ℕ) :
    hughesYoungGammaRatioBellConstant (n + 1) =
      ∑ k : Fin (n + 1), n.choose k *
        hughesYoungGammaRatioBellConstant k *
          (2 * hughesYoungDigammaDifferenceConstant (n - k)) := by
  rw [hughesYoungGammaRatioBellConstant]

theorem hughesYoungGammaRatioBellConstant_nonneg (n : ℕ) :
    0 ≤ hughesYoungGammaRatioBellConstant n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [hughesYoungGammaRatioBellConstant_succ]
          apply Finset.sum_nonneg
          intro k _hk
          exact mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (ih k k.isLt))
            (mul_nonneg (by norm_num)
              (hughesYoungDigammaDifferenceConstant_pos (n - k)).le)

/-- A single logarithmic jet is controlled by one power of the common
height-shift scale. -/
theorem norm_hughesYoungGammaLogJet_le_commonScale
    {j : ℕ} {T t c u : ℝ} (hT : 16 ≤ T) (ht0 : T / 4 ≤ t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : |u| ≤ T / 8) :
    ‖hughesYoungGammaLogJet j t c u‖ ≤
      2 * hughesYoungDigammaDifferenceConstant j *
        (((T / 16)⁻¹ * (1 + |u|)) ^ (j + 1)) := by
  have hraw := norm_hughesYoungGammaLogJet_le
    (j := j) hT ht0 hc0 hc1 hu
  have ha0 : 0 ≤ (T / 16)⁻¹ := by positivity
  have hb1 : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
  calc
    ‖hughesYoungGammaLogJet j t c u‖ ≤
        2 * hughesYoungDigammaDifferenceConstant j *
          (T / 16)⁻¹ ^ (j + 1) * (1 + |u|) := hraw
    _ ≤ 2 * hughesYoungDigammaDifferenceConstant j *
          (T / 16)⁻¹ ^ (j + 1) * (1 + |u|) ^ (j + 1) := by
      have hpow : 1 + |u| ≤ (1 + |u|) ^ (j + 1) := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ hb1 (show 1 ≤ j + 1 by omega))
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg
          (mul_nonneg (by positivity)
            (hughesYoungDigammaDifferenceConstant_pos j).le)
          (pow_nonneg ha0 _))
    _ = 2 * hughesYoungDigammaDifferenceConstant j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ (j + 1)) := by
      rw [mul_pow]
      ring

/-- Uniform all-orders Bell-polynomial bound in the central Mellin range. -/
theorem norm_hughesYoungGammaRatioBell_le
    {n : ℕ} {T t c u : ℝ} (hT : 16 ≤ T) (ht0 : T / 4 ≤ t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : |u| ≤ T / 8) :
    ‖hughesYoungGammaRatioBell c u n t‖ ≤
      hughesYoungGammaRatioBellConstant n *
        (((T / 16)⁻¹ * (1 + |u|)) ^ n) := by
  let S : ℝ := (T / 16)⁻¹ * (1 + |u|)
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [hughesYoungGammaRatioBell_succ]
          calc
            ‖∑ k : Fin (n + 1), (n.choose k : ℂ) *
                hughesYoungGammaRatioBell c u k t *
                  hughesYoungGammaLogJet (n - k) t c u‖ ≤
                ∑ k : Fin (n + 1),
                  ‖(n.choose k : ℂ) *
                    hughesYoungGammaRatioBell c u k t *
                      hughesYoungGammaLogJet (n - k) t c u‖ :=
              norm_sum_le _ _
            _ ≤ ∑ k : Fin (n + 1),
                (n.choose k * hughesYoungGammaRatioBellConstant k *
                  (2 * hughesYoungDigammaDifferenceConstant (n - k))) *
                    S ^ (n + 1) := by
              apply Finset.sum_le_sum
              intro k _hk
              have hklt : (k : ℕ) < n + 1 := k.isLt
              have hbell := ih k hklt
              have hlog := norm_hughesYoungGammaLogJet_le_commonScale
                (j := n - k) hT ht0 hc0 hc1 hu
              change ‖hughesYoungGammaRatioBell c u k t‖ ≤
                  hughesYoungGammaRatioBellConstant k * S ^ (k : ℕ) at hbell
              change ‖hughesYoungGammaLogJet (n - k) t c u‖ ≤
                  2 * hughesYoungDigammaDifferenceConstant (n - k) *
                    S ^ (n - k + 1) at hlog
              rw [norm_mul, norm_mul, norm_natCast]
              calc
                (n.choose k : ℝ) * ‖hughesYoungGammaRatioBell c u k t‖ *
                    ‖hughesYoungGammaLogJet (n - k) t c u‖ ≤
                    (n.choose k : ℝ) *
                      (hughesYoungGammaRatioBellConstant k * S ^ (k : ℕ)) *
                      (2 * hughesYoungDigammaDifferenceConstant (n - k) *
                        S ^ (n - k + 1)) := by
                  have hchoose : 0 ≤ (n.choose k : ℝ) := Nat.cast_nonneg _
                  have hbellRhs : 0 ≤
                      hughesYoungGammaRatioBellConstant k * S ^ (k : ℕ) :=
                    mul_nonneg (hughesYoungGammaRatioBellConstant_nonneg k)
                      (pow_nonneg hS _)
                  have hfirst := mul_le_mul_of_nonneg_left hbell hchoose
                  exact mul_le_mul hfirst hlog (norm_nonneg _) <|
                    mul_nonneg hchoose hbellRhs
                _ = (n.choose k * hughesYoungGammaRatioBellConstant k *
                      (2 * hughesYoungDigammaDifferenceConstant (n - k))) *
                        S ^ (n + 1) := by
                  have hexp : (k : ℕ) + (n - k + 1) = n + 1 := by omega
                  have hpow : S ^ (k : ℕ) * S ^ (n - k + 1) =
                      S ^ (n + 1) := by
                    rw [← pow_add, hexp]
                  calc
                    (n.choose k : ℝ) *
                        (hughesYoungGammaRatioBellConstant k * S ^ (k : ℕ)) *
                        (2 * hughesYoungDigammaDifferenceConstant (n - k) *
                          S ^ (n - k + 1)) =
                        (n.choose k * hughesYoungGammaRatioBellConstant k *
                          (2 * hughesYoungDigammaDifferenceConstant (n - k))) *
                          (S ^ (k : ℕ) * S ^ (n - k + 1)) := by ring
                    _ = _ := by rw [hpow]
            _ = hughesYoungGammaRatioBellConstant (n + 1) * S ^ (n + 1) := by
              rw [← Finset.sum_mul,
                ← hughesYoungGammaRatioBellConstant_succ]

/-- Uniform physical-height derivative bound for the paired Gamma quotient.
The constant from the horizontal Gamma estimate is universal, while the
Bell constant depends only on the derivative order. -/
theorem exists_norm_iteratedDeriv_hughesYoungGammaRatioShift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (T t c u : ℝ),
      16 ≤ T → T / 4 ≤ t → 0 ≤ c → c ≤ 1 → |u| ≤ T / 8 →
      ‖iteratedDeriv n (fun x : ℝ => hughesYoungGammaRatioShift x c u) t‖ ≤
        Real.exp
          (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) *
        hughesYoungGammaRatioBellConstant n *
          (((T / 16)⁻¹ * (1 + |u|)) ^ n) := by
  obtain ⟨C, hC, hvalue⟩ := exists_norm_hughesYoungGammaRatioShift_le
  refine ⟨C, hC, ?_⟩
  intro n T t c u hT ht0 hc0 hc1 hu
  have hformula := iteratedDeriv_hughesYoungGammaRatioShift_eq
    n (c := c) (u := u) (t := t) (by linarith)
  have hbell := norm_hughesYoungGammaRatioBell_le
    (n := n) hT ht0 hc0 hc1 hu
  have hval := hvalue t u c hc0 hc1
  rw [hformula, norm_mul]
  exact (mul_le_mul hval hbell (norm_nonneg _) (by positivity)).trans_eq <| by
    ring

end RiemannZeta.GuthMaynard
