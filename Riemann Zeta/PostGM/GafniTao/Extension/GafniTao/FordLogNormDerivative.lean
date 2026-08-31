import GafniTao.FordZeroDetectorHorizontalDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Real logarithms along zero-free complex paths

Ford's integration by parts ultimately uses only the real part of a
logarithm branch.  That real part is canonically `log ‖f‖`, independent of
the branch.  The lemmas below prove its derivative directly through
`Complex.normSq`, avoiding any hidden choice of argument.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

theorem hasDerivAt_complex_normSq
    {g : ℝ → ℂ} {x : ℝ} {g' : ℂ} (hg : HasDerivAt g g' x) :
    HasDerivAt (fun u => Complex.normSq (g u))
      (2 * (starRingEnd ℂ (g x) * g').re) x := by
  have hre : HasDerivAt (fun u => (g u).re) g'.re x := by
    simpa only [Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hg
  have him : HasDerivAt (fun u => (g u).im) g'.im x := by
    simpa only [Complex.imCLM_apply] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hg
  simp only [Complex.normSq_apply]
  convert (hre.mul hre).add (him.mul him) using 1
  simp [Complex.mul_re]
  ring

theorem hasDerivAt_real_log_norm
    {g : ℝ → ℂ} {x : ℝ} {g' : ℂ} (hg : HasDerivAt g g' x)
    (hgne : g x ≠ 0) :
    HasDerivAt (fun u => Real.log ‖g u‖) (g' / g x).re x := by
  have hsq := hasDerivAt_complex_normSq hg
  have hsqne : Complex.normSq (g x) ≠ 0 :=
    fun h => hgne (Complex.normSq_eq_zero.mp h)
  have hlog := (Real.hasDerivAt_log hsqne).comp x hsq
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hfun : (fun u => Real.log ‖g u‖) =
      fun u => (1 / 2 : ℝ) * Real.log (Complex.normSq (g u)) := by
    funext u
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
    ring
  rw [hfun]
  convert hhalf using 1
  rw [Complex.div_re, Complex.normSq_apply]
  simp [Complex.mul_re]
  field_simp [hsqne]

/-- Fundamental theorem for the branch-independent real logarithm along a
zero-free differentiable complex path. -/
theorem integral_re_logDeriv_path_eq_log_norm_sub
    {g : ℝ → ℂ} {g' : ℝ → ℂ} {a b : ℝ}
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x)
    (hne : ∀ x ∈ uIcc a b, g x ≠ 0)
    (hint : IntervalIntegrable (fun x => (g' x / g x).re) volume a b) :
    (∫ x in a..b, (g' x / g x).re) =
      Real.log ‖g b‖ - Real.log ‖g a‖ := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_real_log_norm (hg x hx) (hne x hx)) hint

theorem hasDerivAt_complex_affine (z d : ℂ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => z + (u : ℂ) * d) d x := by
  convert (Complex.ofRealCLM.hasDerivAt.mul_const d).const_add z using 1
  simp

theorem hasDerivAt_riemannZeta_affine
    {z d : ℂ} {x : ℝ} (h1 : z + (x : ℂ) * d ≠ 1) :
    HasDerivAt (fun u : ℝ => riemannZeta (z + (u : ℂ) * d))
      (d * deriv riemannZeta (z + (x : ℂ) * d)) x := by
  have hz := (differentiableAt_riemannZeta h1).hasDerivAt
  convert hz.comp x (hasDerivAt_complex_affine z d x) using 1
  ring

theorem hasDerivAt_log_norm_riemannZeta_affine
    {z d : ℂ} {x : ℝ} (h1 : z + (x : ℂ) * d ≠ 1)
    (hzeta : riemannZeta (z + (x : ℂ) * d) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖riemannZeta (z + (u : ℂ) * d)‖)
      ((d * deriv riemannZeta (z + (x : ℂ) * d)) /
        riemannZeta (z + (x : ℂ) * d)).re x :=
  hasDerivAt_real_log_norm (hasDerivAt_riemannZeta_affine h1) hzeta

/-- Vertical-line form of the preceding derivative. -/
theorem hasDerivAt_log_norm_riemannZeta_vertical
    {z : ℂ} {a x : ℝ}
    (h1 : z + (x : ℂ) * ((a : ℂ) * Complex.I) ≠ 1)
    (hzeta : riemannZeta
      (z + (x : ℂ) * ((a : ℂ) * Complex.I)) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖riemannZeta
        (z + (u : ℂ) * ((a : ℂ) * Complex.I))‖)
      (-a * (deriv riemannZeta
          (z + (x : ℂ) * ((a : ℂ) * Complex.I)) /
        riemannZeta
          (z + (x : ℂ) * ((a : ℂ) * Complex.I))).im) x := by
  have h := hasDerivAt_log_norm_riemannZeta_affine
    (z := z) (d := (a : ℂ) * Complex.I) (x := x) h1 hzeta
  convert h using 1
  rw [mul_div_assoc, Complex.mul_re]
  simp

end

end GafniTao
