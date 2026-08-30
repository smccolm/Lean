import RiemannZeta.GuthMaynard.HughesYoungGCD
import RiemannZeta.GuthMaynard.HughesYoungShiftWeight

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Cleaning after the Hughes--Young gcd reduction

The mollifier coefficients retain the original indices `h,k`, whereas the
quadratic-divisor equation uses the coprime pair `h/gcd(h,k),k/gcd(h,k)`.
This file proves the exact height-phase cancellation in those coordinates.
-/

/-- Height-independent localized amplitude after removing the common divisor
from the two DFI coefficients.  The arithmetic scalar still uses the original
mollifier indices. -/
noncomputable def hughesYoungReducedLocalizedStaticWeight
    (T c u X Y : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  hughesYoungLocalizedStaticScalar T h k *
    hughesYoungLocalizedLogKernel X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
      ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
      ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) x y

/-- The original mollifier phases and the coprime-coordinate physical phases
still collapse exactly to the source Fourier character. -/
theorem hughesYoung_reduced_combined_height_phase
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    Complex.exp (-((t : ℂ) * I) * (Real.log (h : ℝ) : ℂ)) *
        Complex.exp (((t : ℂ) * I) * (Real.log (k : ℝ) : ℂ)) *
        Complex.exp (-((t : ℂ) * I) *
          (Real.log (x / hughesYoungReducedLeft h k) : ℂ)) *
        Complex.exp (((t : ℂ) * I) *
          (Real.log (y / hughesYoungReducedRight h k) : ℂ)) =
      Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) := by
  let d : ℝ := hughesYoungCommonDivisor h k
  let a : ℝ := hughesYoungReducedLeft h k
  let b : ℝ := hughesYoungReducedRight h k
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast hughesYoungReducedLeft_pos hh
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast hughesYoungReducedRight_pos hh hk
  have hleft : d * a = (h : ℝ) := by
    dsimp [d, a]
    exact_mod_cast hughesYoungCommonDivisor_mul_reducedLeft h k
  have hright : d * b = (k : ℝ) := by
    dsimp [d, b]
    exact_mod_cast hughesYoungCommonDivisor_mul_reducedRight h k
  have hlogH : Real.log (h : ℝ) = Real.log d + Real.log a := by
    rw [← hleft, Real.log_mul hd.ne' ha.ne']
  have hlogK : Real.log (k : ℝ) = Real.log d + Real.log b := by
    rw [← hright, Real.log_mul hd.ne' hb.ne']
  have hlogX : Real.log (x / a) = Real.log x - Real.log a :=
    Real.log_div hx.ne' ha.ne'
  have hlogY : Real.log (y / b) = Real.log y - Real.log b :=
    Real.log_div hy.ne' hb.ne'
  have hlogRatio : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div hy.ne' hx.ne'
  change Complex.exp (-((t : ℂ) * I) * (Real.log (h : ℝ) : ℂ)) *
      Complex.exp (((t : ℂ) * I) * (Real.log (k : ℝ) : ℂ)) *
      Complex.exp (-((t : ℂ) * I) * (Real.log (x / a) : ℂ)) *
      Complex.exp (((t : ℂ) * I) * (Real.log (y / b) : ℂ)) = _
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  rw [hlogH, hlogK, hlogX, hlogY, hlogRatio]
  congr 1
  push_cast
  ring

/-- Pointwise reduced-coordinate analogue of the source identity underlying
Hughes--Young equation (65). -/
theorem heightWeight_mul_hughesYoungReducedLocalizedMellinWeight_eq_static_mul_phase
    (T t c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k x y =
      hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y *
        Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
        hughesYoungHeightFourierInput T c u t := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpowH : (h : ℂ) ^ (-afeCriticalPoint t) =
      hughesYoungLogPower (afeCriticalPoint t) (h : ℝ) := by
    simpa only [Complex.ofReal_natCast] using
      (hughesYoungLogPower_eq_cpow hhR (afeCriticalPoint t)).symm
  have hpowK : (k : ℂ) ^ (-afeCriticalPoint (-t)) =
      hughesYoungLogPower (afeCriticalPoint (-t)) (k : ℝ) := by
    simpa only [Complex.ofReal_natCast] using
      (hughesYoungLogPower_eq_cpow hkR (afeCriticalPoint (-t))).symm
  have hsplitH : hughesYoungLogPower (afeCriticalPoint t) (h : ℝ) =
      hughesYoungLogPower (1 / 2 : ℂ) (h : ℝ) *
        Complex.exp (-((t : ℂ) * I) * (Real.log (h : ℝ) : ℂ)) := by
    simpa using hughesYoungLogPower_afeCriticalPoint_add t 0 (h : ℝ)
  have hsplitK : hughesYoungLogPower (afeCriticalPoint (-t)) (k : ℝ) =
      hughesYoungLogPower (1 / 2 : ℂ) (k : ℝ) *
        Complex.exp (((t : ℂ) * I) * (Real.log (k : ℝ) : ℂ)) := by
    simpa using hughesYoungLogPower_afeCriticalPoint_neg_add t 0 (k : ℝ)
  rw [hughesYoungReducedLocalizedMellinWeight]
  unfold hughesYoungMellinScalar hughesYoungLocalizedLogKernel
  rw [hpowH, hpowK, hsplitH, hsplitK,
    hughesYoungLogPower_afeCriticalPoint_add t
      ((c : ℂ) + (u : ℂ) * I),
    hughesYoungLogPower_afeCriticalPoint_neg_add t
      ((c : ℂ) + (u : ℂ) * I)]
  unfold hughesYoungReducedLocalizedStaticWeight
    hughesYoungLocalizedStaticScalar hughesYoungHeightFourierInput
  unfold hughesYoungLocalizedLogKernel
  rw [← hughesYoung_reduced_combined_height_phase hh hk hx hy t]
  ring

/-- Exact height integration of the gcd-reduced source summand. -/
theorem integral_heightWeight_mul_hughesYoungReducedLocalizedMellinWeight_eq_transform
    (T c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k x y) =
      hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y *
        hughesYoungHeightTransform T c u (Real.log (y / x)) := by
  simp_rw [heightWeight_mul_hughesYoungReducedLocalizedMellinWeight_eq_static_mul_phase
    T _ c u X Y hh hk hx hy]
  rw [show (fun t : ℝ =>
      hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y *
        Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
          hughesYoungHeightFourierInput T c u t) =
      fun t : ℝ => hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y *
        (Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
          hughesYoungHeightFourierInput T c u t) by
    funext t
    ring]
  rw [integral_const_mul]
  rw [← hughesYoungHeightTransform_eq_integral]

end RiemannZeta.GuthMaynard
