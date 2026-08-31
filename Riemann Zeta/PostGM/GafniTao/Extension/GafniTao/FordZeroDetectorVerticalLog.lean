import GafniTao.FordZeroDetectorVerticalParts

/-!
# Branch-independent logarithms on Ford's vertical edges

The real part of the normalized vertical contour integral depends only on
`log |ζ|`.  These lemmas identify its derivative with Ford's actual zeta
logarithmic derivative and assemble the finite-height Abel formula.  Thus no
unproved global branch of the complex logarithm is introduced.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

theorem fordDetector_posVerticalParam_re
    {eta : ℝ} (heta : 0 < eta) (u : ℝ) (L : ℂ) :
    ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        fordCotKernel eta
          ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) * L).re =
      (1 / (2 * Real.pi)) * Real.tanh u * L.im := by
  rw [fordCotKernel_pos_vertical heta]
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

theorem fordDetector_negVerticalParam_re
    {eta : ℝ} (heta : 0 < eta) (u : ℝ) (L : ℂ) :
    ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        fordCotKernel eta
          ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) * L).re =
      (1 / (2 * Real.pi)) * Real.tanh u * L.im := by
  rw [fordCotKernel_neg_vertical heta]
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

theorem hasDerivAt_log_norm_zeta_detector_vertical
    {z : ℂ} {a u : ℝ}
    (h1 : z + (u : ℂ) * ((a : ℂ) * I) ≠ 1)
    (hzeta : riemannZeta (z + (u : ℂ) * ((a : ℂ) * I)) ≠ 0) :
    HasDerivAt
      (fun v : ℝ => Real.log ‖riemannZeta
        (z + (v : ℂ) * ((a : ℂ) * I))‖)
      (-a * (fordDetectorZetaLogDeriv
        (z + (u : ℂ) * ((a : ℂ) * I))).im) u := by
  have h := hasDerivAt_log_norm_riemannZeta_vertical h1 hzeta
  convert h using 1
  rw [fordDetectorZetaLogDeriv_eq h1 hzeta]
  rfl

theorem differentiableAt_fordDetectorZetaLogDeriv
    {s : ℂ} (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ fordDetectorZetaLogDeriv s := by
  have hsur : sharpZetaSurrogate s ≠ 0 := by
    intro hzero
    exact hzeta ((sharpZetaSurrogate_eq_zero_iff hs1).mp hzero)
  unfold fordDetectorZetaLogDeriv
  exact (differentiableAt_logDeriv_sharpZetaSurrogate hsur).sub
    ((differentiableAt_const (c := (1 : ℂ))).div
      (differentiableAt_id.sub_const (1 : ℂ))
      (sub_ne_zero.mpr hs1))

/-- Finite-height branch-independent vertical-edge formula.  The sign
`side = ±η` is supplied through the exact cotangent identity `hkernel`.
The boundary contribution is intentionally retained. -/
theorem integral_re_fordDetector_verticalParam_eq
    {eta a b : ℝ} (heta : 0 < eta) (z₀ : ℂ) (side : ℝ)
    (hkernel : ∀ u : ℝ,
      fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I)
    (h1 : ∀ u ∈ uIcc a b,
      z₀ + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I ≠ 1)
    (hzeta : ∀ u ∈ uIcc a b,
      riemannZeta (z₀ + (side : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (∫ u in a..b,
      ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        fordCotKernel eta
          ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) *
        fordDetectorZetaLogDeriv
          (z₀ + (side : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I)).re) =
      (1 / (4 * eta)) *
        ((∫ u in a..b,
          Real.log ‖riemannZeta
            (z₀ + (side : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh b * Real.log ‖riemannZeta
              (z₀ + (side : ℂ) +
                (2 * eta * b / Real.pi : ℝ) * I)‖ -
           Real.tanh a * Real.log ‖riemannZeta
              (z₀ + (side : ℂ) +
                (2 * eta * a / Real.pi : ℝ) * I)‖)) := by
  let scale : ℝ := 2 * eta / Real.pi
  let q : ℝ → ℝ := fun u => Real.log ‖riemannZeta
    ((z₀ + (side : ℂ)) + (u : ℂ) * ((scale : ℂ) * I))‖
  let q' : ℝ → ℝ := fun u => -scale *
    (fordDetectorZetaLogDeriv
      ((z₀ + (side : ℂ)) + (u : ℂ) * ((scale : ℂ) * I))).im
  have hq : ∀ u ∈ uIcc a b, HasDerivAt q (q' u) u := by
    intro u hu
    have hpath :
        z₀ + (side : ℂ) + (scale * u : ℝ) * I =
          (z₀ + (side : ℂ)) +
            (u : ℂ) * ((scale : ℂ) * I) := by
      push_cast
      ring
    have hphysical :
        z₀ + (side : ℂ) + (scale * u : ℝ) * I =
          z₀ + (side : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I := by
      dsimp only [scale]
      push_cast
      ring
    have h1' :
        (z₀ + (side : ℂ)) +
            (u : ℂ) * ((scale : ℂ) * I) ≠ 1 := by
      rw [← hpath, hphysical]
      exact h1 u hu
    have hzeta' :
        riemannZeta ((z₀ + (side : ℂ)) +
            (u : ℂ) * ((scale : ℂ) * I)) ≠ 0 := by
      rw [← hpath, hphysical]
      exact hzeta u hu
    exact hasDerivAt_log_norm_zeta_detector_vertical
      h1' hzeta'
  have hqInt : IntervalIntegrable q' volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hpath :
        (z₀ + (side : ℂ)) + (u : ℂ) * ((scale : ℂ) * I) =
          z₀ + (side : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I := by
      dsimp only [scale]
      push_cast
      ring
    have h1' :
        (z₀ + (side : ℂ)) + (u : ℂ) * ((scale : ℂ) * I) ≠ 1 := by
      rw [hpath]
      exact h1 u hu
    have hzeta' :
        riemannZeta ((z₀ + (side : ℂ)) +
          (u : ℂ) * ((scale : ℂ) * I)) ≠ 0 := by
      rw [hpath]
      exact hzeta u hu
    have hpathCont : ContinuousAt
        (fun v : ℝ => (z₀ + (side : ℂ)) +
          (v : ℂ) * ((scale : ℂ) * I)) u := by fun_prop
    have hLCont : ContinuousAt
        (fun v : ℝ => fordDetectorZetaLogDeriv
          ((z₀ + (side : ℂ)) +
            (v : ℂ) * ((scale : ℂ) * I))) u :=
      (differentiableAt_fordDetectorZetaLogDeriv h1' hzeta').continuousAt.comp_of_eq
        hpathCont rfl
    have himCont : ContinuousAt
        (fun v : ℝ => (fordDetectorZetaLogDeriv
          ((z₀ + (side : ℂ)) +
            (v : ℂ) * ((scale : ℂ) * I))).im) u :=
      Complex.continuous_im.continuousAt.comp hLCont
    exact (continuousAt_const.mul himCont).continuousWithinAt
  have hparts := integral_tanh_mul_deriv_eq_boundary_sub_sechSq hq hqInt
  have hpoint : ∀ u : ℝ,
      ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        fordCotKernel eta
          ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) *
        fordDetectorZetaLogDeriv
          (z₀ + (side : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I)).re =
        (-1 / (4 * eta)) * Real.tanh u * q' u := by
    intro u
    rw [hkernel u]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
    have hcomplex :
        (1 / (2 * (Real.pi : ℂ) * I)) *
            (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
            (-((Real.pi / (2 * eta) : ℝ) : ℂ) *
              (Real.tanh u : ℂ) * I) *
            fordDetectorZetaLogDeriv
              (z₀ + (side : ℂ) +
                (2 * eta * u / Real.pi : ℝ) * I) =
          -((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (Real.tanh u : ℂ) * I *
            fordDetectorZetaLogDeriv
              (z₀ + (side : ℂ) +
                (2 * eta * u / Real.pi : ℝ) * I) := by
      push_cast
      field_simp [hpi, hetaC]
    rw [hcomplex]
    dsimp only [q', scale]
    simp [Complex.mul_re, Complex.tanh_ofReal_re]
    field_simp [heta.ne', Real.pi_ne_zero]
    ring
  rw [show (∫ u in a..b,
      ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        fordCotKernel eta
          ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) *
        fordDetectorZetaLogDeriv
          (z₀ + (side : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I)).re) =
      ∫ u in a..b, (-1 / (4 * eta)) * Real.tanh u * q' u by
        apply intervalIntegral.integral_congr
        intro u _hu
        exact hpoint u]
  have q_eq : ∀ u : ℝ, q u = Real.log ‖riemannZeta
      (z₀ + (side : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I)‖ := by
    intro u
    dsimp only [q, scale]
    congr 2
    push_cast
    ring
  calc
    (∫ u in a..b, (-1 / (4 * eta)) * Real.tanh u * q' u) =
        (-1 / (4 * eta)) *
          ∫ u in a..b, Real.tanh u * q' u := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _hu
      ring
    _ = (-1 / (4 * eta)) *
        (Real.tanh b * q b - Real.tanh a * q a -
          ∫ u in a..b, q u / Real.cosh u ^ 2) := by rw [hparts]
    _ = (1 / (4 * eta)) *
        ((∫ u in a..b, q u / Real.cosh u ^ 2) -
          (Real.tanh b * q b - Real.tanh a * q a)) := by ring
    _ = (1 / (4 * eta)) *
        ((∫ u in a..b,
          Real.log ‖riemannZeta
            (z₀ + (side : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh b * Real.log ‖riemannZeta
              (z₀ + (side : ℂ) +
                (2 * eta * b / Real.pi : ℝ) * I)‖ -
           Real.tanh a * Real.log ‖riemannZeta
              (z₀ + (side : ℂ) +
                (2 * eta * a / Real.pi : ℝ) * I)‖)) := by
      simp_rw [q_eq]

theorem integral_re_fordDetector_posVerticalParam_eq
    {eta a b : ℝ} (heta : 0 < eta) (z₀ : ℂ)
    (h1 : ∀ u ∈ uIcc a b,
      z₀ + (eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I ≠ 1)
    (hzeta : ∀ u ∈ uIcc a b,
      riemannZeta (z₀ + (eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (∫ u in a..b,
      ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        fordCotKernel eta
          ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) *
        fordDetectorZetaLogDeriv
          (z₀ + (eta : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I)).re) =
      (1 / (4 * eta)) *
        ((∫ u in a..b,
          Real.log ‖riemannZeta
            (z₀ + (eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh b * Real.log ‖riemannZeta
              (z₀ + (eta : ℂ) +
                (2 * eta * b / Real.pi : ℝ) * I)‖ -
           Real.tanh a * Real.log ‖riemannZeta
              (z₀ + (eta : ℂ) +
                (2 * eta * a / Real.pi : ℝ) * I)‖)) := by
  exact integral_re_fordDetector_verticalParam_eq heta z₀ eta
    (fordCotKernel_pos_vertical heta) h1 hzeta

theorem integral_re_fordDetector_negVerticalParam_eq
    {eta a b : ℝ} (heta : 0 < eta) (z₀ : ℂ)
    (h1 : ∀ u ∈ uIcc a b,
      z₀ + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I ≠ 1)
    (hzeta : ∀ u ∈ uIcc a b,
      riemannZeta (z₀ + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (∫ u in a..b,
      ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        fordCotKernel eta
          ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) *
        fordDetectorZetaLogDeriv
          (z₀ + (-eta : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I)).re) =
      (1 / (4 * eta)) *
        ((∫ u in a..b,
          Real.log ‖riemannZeta
            (z₀ + (-eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh b * Real.log ‖riemannZeta
              (z₀ + (-eta : ℂ) +
                (2 * eta * b / Real.pi : ℝ) * I)‖ -
           Real.tanh a * Real.log ‖riemannZeta
              (z₀ + (-eta : ℂ) +
                (2 * eta * a / Real.pi : ℝ) * I)‖)) := by
  simpa using
    (integral_re_fordDetector_verticalParam_eq heta z₀ (-eta)
      (fun u => by simpa using fordCotKernel_neg_vertical heta u)
      (fun u hu => by simpa using h1 u hu)
      (fun u hu => by simpa using hzeta u hu))

end

end GafniTao
