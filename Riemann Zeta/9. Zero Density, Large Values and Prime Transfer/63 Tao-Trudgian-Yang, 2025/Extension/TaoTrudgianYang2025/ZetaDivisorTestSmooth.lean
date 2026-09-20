import TaoTrudgianYang2025.ZetaDivisorWeightSmooth
import TaoTrudgianYang2025.ZetaShortDivisorGeometry

/-!
# Positive-axis smoothness of the genuine divisor test

The Gaussian transform is evaluated before differentiating. Thus the
smooth function here is the actual test in the finite source sum, with
the complex Mellin weight and the reflected Gamma phase unchanged.
-/

noncomputable section

open Complex Filter Set Topology
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem contDiff_zetaGaussianQuadraticIntegral (T : ℝ) {G : ℝ} (hG : G ≠ 0) :
    ContDiff ℝ ∞ (zetaGaussianQuadraticIntegral T G) := by
  have he : zetaGaussianQuadraticIntegral T G = fun v : ℝ =>
      ((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ) *
        Complex.exp (-(v : ℂ) ^ 2 / (4 * zetaGaussianQuadraticCoefficient T G)) := by
    funext v
    exact zetaGaussianQuadraticIntegral_eq T v hG
  rw [he]
  have hcast : ContDiff ℝ ∞ (fun v : ℝ => (v : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

theorem contDiffAt_ofReal_cpow_positive (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) ^ s) x := by
  have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx.ne'
  have hcastlog : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog
  have hexp : ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * s)) x := by
    fun_prop
  apply hexp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hy), ← Complex.ofReal_log hy.le]

theorem contDiffAt_zetaShortDivisorTestFunction (T : ℝ) {G x : ℝ}
    (hG : G ≠ 0) (hx : 0 < x) :
    ContDiffAt ℝ ∞ (zetaShortDivisorTestFunction T G) x := by
  have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx.ne'
  have hpow := contDiffAt_ofReal_cpow_positive ((-1 / 2 : ℂ) + (T : ℂ) * I) hx
  have hcastlog : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog
  have hweight : ContDiffAt ℝ ∞
      (fun y : ℝ => zetaDivisorWeight ((Real.log y : ℂ) - zetaGammaLeadingLog T)) x :=
    contDiff_zetaDivisorWeight.contDiffAt.comp x (hcastlog.sub contDiffAt_const)
  have hquad := contDiff_zetaGaussianQuadraticIntegral T hG
  unfold zetaShortDivisorTestFunction
  fun_prop

theorem contDiffOn_zetaShortDivisorTestFunction (T : ℝ) {G : ℝ} (hG : G ≠ 0) :
    ContDiffOn ℝ ∞ (zetaShortDivisorTestFunction T G) (Ioi 0) :=
  fun _ hx => (contDiffAt_zetaShortDivisorTestFunction T hG hx).contDiffWithinAt

end TaoTrudgianYang2025
