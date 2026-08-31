import GafniTao.FordZetaBasic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Meromorphic
import RiemannZeta.External.PNT.ResidueCalcOnRectangles

/-!
# The cotangent kernel in Ford's zero detector

Ford integrates the logarithmic derivative against
`(pi / (2 eta)) cot (pi z / (2 eta))`.  This file fixes that normalization
and proves the endpoint and vertical-line identities which produce the
`cosh u ^ (-2)` weight in the detector.
-/

open Complex Filter Set Topology

namespace GafniTao

noncomputable def fordCotKernel (eta : ℝ) (z : ℂ) : ℂ :=
  ((Real.pi / (2 * eta) : ℝ) : ℂ) *
    Complex.cot ((((Real.pi / (2 * eta) : ℝ) : ℂ) * z))

theorem fordCotKernel_pos_endpoint {eta : ℝ} (heta : 0 < eta) :
    fordCotKernel eta eta = 0 := by
  have harg :
      (((Real.pi / (2 * eta) : ℝ) : ℂ) * (eta : ℂ)) =
        (Real.pi / 2 : ℝ) := by
    push_cast
    field_simp [heta.ne']
  unfold fordCotKernel
  rw [harg]
  simp [Complex.cot]

theorem fordCotKernel_neg_endpoint {eta : ℝ} (heta : 0 < eta) :
    fordCotKernel eta (-eta) = 0 := by
  have harg :
      (((Real.pi / (2 * eta) : ℝ) : ℂ) * (-eta : ℂ)) =
        -(Real.pi / 2 : ℝ) := by
    push_cast
    field_simp [heta.ne']
  unfold fordCotKernel
  rw [harg]
  simp [Complex.cot]

theorem fordCotKernel_scale_mul {eta : ℝ} (heta : 0 < eta)
    (u : ℝ) :
    (((Real.pi / (2 * eta) : ℝ) : ℂ) *
        ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I)) =
      (Real.pi / 2 : ℝ) + (u : ℂ) * Complex.I := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp [heta.ne', hpi]

theorem fordCotKernel_scale_neg_mul {eta : ℝ} (heta : 0 < eta)
    (u : ℝ) :
    (((Real.pi / (2 * eta) : ℝ) : ℂ) *
        ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I)) =
      -(Real.pi / 2 : ℝ) + (u : ℂ) * Complex.I := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp [heta.ne', hpi]

theorem ford_sin_pos_vertical {eta : ℝ} (heta : 0 < eta)
    (u : ℝ) :
    Complex.sin
        ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
          ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I))) =
      (Real.cosh u : ℂ) := by
  rw [fordCotKernel_scale_mul heta u]
  rw [show ((Real.pi / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I =
      (u : ℂ) * Complex.I + (Real.pi : ℂ) / 2 by push_cast; ring]
  rw [Complex.sin_add_pi_div_two, Complex.cos_mul_I,
    ← Complex.ofReal_cosh]

theorem ford_sin_neg_vertical {eta : ℝ} (heta : 0 < eta)
    (u : ℝ) :
    Complex.sin
        ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
          ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I))) =
      -(Real.cosh u : ℂ) := by
  rw [fordCotKernel_scale_neg_mul heta u]
  rw [show (-(Real.pi / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I =
      (u : ℂ) * Complex.I - (Real.pi : ℂ) / 2 by push_cast; ring]
  rw [Complex.sin_sub_pi_div_two, Complex.cos_mul_I,
    ← Complex.ofReal_cosh]

theorem ford_sin_pos_vertical_ne_zero {eta : ℝ} (heta : 0 < eta)
    (u : ℝ) :
    Complex.sin
        ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
          ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I))) ≠ 0 := by
  rw [ford_sin_pos_vertical heta u]
  exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos u).ne'

theorem ford_sin_neg_vertical_ne_zero {eta : ℝ} (heta : 0 < eta)
    (u : ℝ) :
    Complex.sin
        ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
          ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I))) ≠ 0 := by
  rw [ford_sin_neg_vertical heta u]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (Real.cosh_pos u).ne')

theorem hasDerivAt_fordCotKernel {eta : ℝ} {z : ℂ}
    (hsin : Complex.sin
      ((((Real.pi / (2 * eta) : ℝ) : ℂ) * z)) ≠ 0) :
    HasDerivAt (fordCotKernel eta)
      (-(((Real.pi / (2 * eta) : ℝ) : ℂ) ^ 2) /
        Complex.sin
          ((((Real.pi / (2 * eta) : ℝ) : ℂ) * z)) ^ 2) z := by
  let c : ℂ := ((Real.pi / (2 * eta) : ℝ) : ℂ)
  have hlin : HasDerivAt (fun w : ℂ => c * w) c z := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul c
  have hcos : HasDerivAt (fun w : ℂ => Complex.cos (c * w))
      (-Complex.sin (c * z) * c) z :=
    (Complex.hasDerivAt_cos (c * z)).comp z hlin
  have hsin' : HasDerivAt (fun w : ℂ => Complex.sin (c * w))
      (Complex.cos (c * z) * c) z :=
    (Complex.hasDerivAt_sin (c * z)).comp z hlin
  have hsinC : Complex.sin (c * z) ≠ 0 := by
    simpa only [c] using hsin
  have hquot := hcos.div hsin' hsinC
  have hmul := hquot.const_mul c
  have hcoeff :
      -c ^ 2 / Complex.sin (c * z) ^ 2 =
        c * ((-Complex.sin (c * z) * c * Complex.sin (c * z) -
          Complex.cos (c * z) * (Complex.cos (c * z) * c)) /
            Complex.sin (c * z) ^ 2) := by
    field_simp [hsinC]
    rw [show
      -Complex.sin (c * z) ^ 2 - Complex.cos (c * z) ^ 2 =
        -(Complex.sin (c * z) ^ 2 + Complex.cos (c * z) ^ 2) by ring,
      Complex.sin_sq_add_cos_sq]
    ring
  rw [hcoeff]
  simpa only [fordCotKernel, Complex.cot, c] using hmul

theorem deriv_fordCotKernel_pos_vertical {eta : ℝ} (heta : 0 < eta)
    (u : ℝ) :
    deriv (fordCotKernel eta)
        ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) =
      -(((Real.pi / (2 * eta) : ℝ) : ℂ) ^ 2) /
        (Real.cosh u : ℂ) ^ 2 := by
  rw [(hasDerivAt_fordCotKernel
    (ford_sin_pos_vertical_ne_zero heta u)).deriv,
    ford_sin_pos_vertical heta u]

theorem deriv_fordCotKernel_neg_vertical {eta : ℝ} (heta : 0 < eta)
    (u : ℝ) :
    deriv (fordCotKernel eta)
        ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) =
      -(((Real.pi / (2 * eta) : ℝ) : ℂ) ^ 2) /
        (Real.cosh u : ℂ) ^ 2 := by
  rw [(hasDerivAt_fordCotKernel
    (ford_sin_neg_vertical_ne_zero heta u)).deriv,
    ford_sin_neg_vertical heta u]
  ring

/-- The Ford cotangent weight has residue one at its central pole.  This is
the normalization needed for the logarithmic-derivative term in the detector. -/
theorem tendsto_mul_fordCotKernel_zero {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun z : ℂ => z * fordCotKernel eta z)
      (nhdsWithin 0 {0}ᶜ) (𝓝 1) := by
  let c : ℂ := ((Real.pi / (2 * eta) : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast div_ne_zero Real.pi_ne_zero (mul_ne_zero two_ne_zero heta.ne')
  have hsinSlope :
      Tendsto (slope Complex.sin 0) (nhdsWithin 0 {0}ᶜ) (𝓝 1) := by
    simpa using hasDerivAt_iff_tendsto_slope.mp (Complex.hasDerivAt_sin 0)
  have hsinDiv :
      Tendsto (fun w : ℂ => Complex.sin w / w)
        (nhdsWithin 0 {0}ᶜ) (𝓝 1) := by
    refine hsinSlope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp [slope, hw]
  have hcomp : Tendsto (fun z : ℂ => c * z)
      (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    exact (tendsto_const_nhds.mul tendsto_id).nhdsWithin_of_mapsTo
      (fun z hz => mul_ne_zero hc hz)
  have hratio :
      Tendsto (fun z : ℂ => (c * z) / Complex.sin (c * z))
        (nhdsWithin 0 {0}ᶜ) (𝓝 1) := by
    have hforward := hsinDiv.comp hcomp
    have hinv := hforward.inv₀ one_ne_zero
    simpa [div_eq_mul_inv] using hinv
  have hcos : Tendsto (fun z : ℂ => Complex.cos (c * z))
      (nhdsWithin 0 {0}ᶜ) (𝓝 1) := by
    simpa using (Complex.continuous_cos.tendsto 0).comp
      ((tendsto_const_nhds.mul tendsto_id).mono_left nhdsWithin_le_nhds)
  have hmul := hcos.mul hratio
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hcz : c * z ≠ 0 := mul_ne_zero hc hz
  simp only [fordCotKernel, Complex.cot, c]
  field_simp [hc, hz, hcz]
  ring

theorem residue_fordCotKernel_zero {eta : ℝ} (heta : 0 < eta) :
    residue (fordCotKernel eta) 0 = 1 := by
  exact residue_eq_of_tendsto (tendsto_mul_fordCotKernel_zero heta)

end GafniTao
