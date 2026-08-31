import GafniTao.FordZeroDetectorVerticalParts

open Complex

#check GafniTao.fordDetectorZetaLogDeriv_eq
#check logDeriv
#check intervalIntegral.integral_comp_mul_left
#check intervalIntegral.integral_comp_mul_deriv'
#check intervalIntegral.integral_comp_mul_add
#check intervalIntegral.smul_integral_comp_mul_left
#check Complex.tanh_ofReal_re
#check Complex.tanh_ofReal_im
#check ContinuousOn.intervalIntegrable
#check intervalIntegral.intervalIntegral_re

open RiemannZeta.GuthMaynard

example (F : ℂ → ℂ) {x t R scale : ℝ} (hscale : scale ≠ 0) :
    VIntegral' F x (t - R) (t + R) =
      ∫ u in (-R / scale)..(R / scale),
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I) := by
  let f : ℝ → ℂ := fun y =>
    (1 / (2 * (Real.pi : ℂ) * I)) * I *
      F ((x : ℂ) + (y : ℝ) * I)
  have hchange := intervalIntegral.integral_comp_mul_add
    (f := f) (a := -R / scale) (b := R / scale) hscale t
  have hlower : scale * (-R / scale) + t = t - R := by
    field_simp [hscale]
    ring
  have hupper : scale * (R / scale) + t = t + R := by
    field_simp [hscale]
    ring
  rw [hlower, hupper] at hchange
  have hscaleC : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale
  calc
    VIntegral' F x (t - R) (t + R) =
        ∫ y in t - R..t + R, f y := by
      unfold VIntegral' VIntegral
      simp only [smul_eq_mul]
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _hy
      dsimp only [f]
      ring
    _ = (scale : ℂ) *
        ∫ u in (-R / scale)..(R / scale), f (scale * u + t) := by
      rw [hchange]
      rw [Complex.real_smul]
      push_cast
      field_simp [hscaleC]
    _ = ∫ u in (-R / scale)..(R / scale),
        (scale : ℂ) * f (scale * u + t) := by
      symm
      exact intervalIntegral.integral_const_mul
        (scale : ℂ) (fun u : ℝ => f (scale * u + t))
    _ = ∫ u in (-R / scale)..(R / scale),
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      dsimp only [f]
      push_cast
      ring

example {eta : ℝ} (heta : 0 < eta) (u : ℝ) (L : ℂ) :
    ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        GafniTao.fordCotKernel eta
          ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) * L).re =
      (1 / (2 * Real.pi)) * Real.tanh u * L.im := by
  rw [GafniTao.fordCotKernel_pos_vertical heta]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have hcomplex :
      (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
          (-((Real.pi / (2 * eta) : ℝ) : ℂ) *
            (Real.tanh u : ℂ) * I) * L =
        -((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (Real.tanh u : ℂ) * I * L := by
    push_cast
    field_simp [hpi, hetaC]
  rw [hcomplex]
  simp [Complex.mul_re, Complex.tanh_ofReal_re]

example {z : ℂ} {a x : ℝ}
    (h1 : z + (x : ℂ) * ((a : ℂ) * I) ≠ 1)
    (hzeta : riemannZeta (z + (x : ℂ) * ((a : ℂ) * I)) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖riemannZeta
        (z + (u : ℂ) * ((a : ℂ) * I))‖)
      (-a * (GafniTao.fordDetectorZetaLogDeriv
        (z + (x : ℂ) * ((a : ℂ) * I))).im) x := by
  have h := GafniTao.hasDerivAt_log_norm_riemannZeta_vertical h1 hzeta
  convert h using 1
  rw [GafniTao.fordDetectorZetaLogDeriv_eq h1 hzeta]
  rfl
