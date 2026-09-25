import TaoTrudgianYang2025.AtkinsonIndexFirstDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Physical normalization of the Atkinson gap phase

Rationalizing the actual slope removes the small height gap from the
normalized profile. The profile remains smooth at coinciding heights.
This is an entry bridge, not yet the general exponent-pair sum estimate.
-/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

def atkinsonGapSlopeProfile (q r x : ℝ) : ℝ :=
  (Real.sqrt r+1)/
    (Real.sqrt x*(Real.sqrt (r+q*x)+Real.sqrt (1+q*x)))

def atkinsonGapFrequency (M t u : ℝ) : ℝ :=
  2*Real.pi*(t-u)/
    (Real.sqrt (2*Real.pi*u/M)*(Real.sqrt (t/u)+1))

def atkinsonNormalizedGapPhase (M t u x : ℝ) : ℝ :=
  atkinsonIndexPhaseDifference t u (M*x)/atkinsonGapFrequency M t u

theorem atkinsonGapFrequency_pos {M t u : ℝ}
    (hM : 0 < M) (hu : 0 < u) (htu : u < t) :
    0 < atkinsonGapFrequency M t u := by
  unfold atkinsonGapFrequency
  positivity

theorem atkinsonGapSlopeProfile_zero (r x : ℝ) :
    atkinsonGapSlopeProfile 0 r x = 1/Real.sqrt x := by
  unfold atkinsonGapSlopeProfile
  simp only [zero_mul,add_zero,Real.sqrt_one]
  have hs : Real.sqrt r+1 ≠ 0 := by positivity
  field_simp

theorem atkinsonIndexRealSlope_scaled {M T u x : ℝ}
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) (hx : 0 < x) :
    atkinsonIndexRealSlope T (M*x) =
      Real.sqrt (2*Real.pi*u/M)*
        Real.sqrt (T/u+(Real.pi*M/(2*u))*x)/Real.sqrt x := by
  have hA : 0 < 2*Real.pi*u/M := by positivity
  have hB : 0 < T/u+(Real.pi*M/(2*u))*x := by positivity
  have hR : 0 < 2*Real.pi*T/(M*x)+Real.pi^2 := by positivity
  have hs : (Real.sqrt (2*Real.pi*u/M)*
      Real.sqrt (T/u+(Real.pi*M/(2*u))*x)/Real.sqrt x)^2 =
      2*Real.pi*T/(M*x)+Real.pi^2 := by
    rw [div_pow,mul_pow,Real.sq_sqrt hA.le,Real.sq_sqrt hB.le,Real.sq_sqrt hx.le]
    field_simp
  have hn : 0 ≤ Real.sqrt (2*Real.pi*u/M)*
      Real.sqrt (T/u+(Real.pi*M/(2*u))*x)/Real.sqrt x := by positivity
  unfold atkinsonIndexRealSlope
  nlinarith [Real.sq_sqrt hR.le,Real.sqrt_nonneg
    (2*Real.pi*T/(M*x)+Real.pi^2)]

theorem hasDerivAt_atkinsonNormalizedGapPhase {M t u x : ℝ}
    (hM : 0 < M) (hu : 0 < u) (htu : u < t) (hx : 0 < x) :
    HasDerivAt (atkinsonNormalizedGapPhase M t u)
      (atkinsonGapSlopeProfile (Real.pi*M/(2*u)) (t/u) x) x := by
  have ht := hu.trans htu
  have hMx : 0 < M*x := mul_pos hM hx
  have hd := ((hasDerivAt_atkinsonIndexPhaseDifference ht hu hMx).comp x
    ((hasDerivAt_id x).const_mul M)).div_const (atkinsonGapFrequency M t u)
  simp only [mul_one] at hd
  change HasDerivAt (atkinsonNormalizedGapPhase M t u)
    (((atkinsonIndexRealSlope t (M*x)-atkinsonIndexRealSlope u (M*x))*M)/
      atkinsonGapFrequency M t u) x at hd
  apply hd.congr_deriv
  rw [atkinsonIndexRealSlope_sub_eq ht hu hMx,
    atkinsonIndexRealSlope_scaled hM ht hu hx,
    atkinsonIndexRealSlope_scaled hM hu hu hx]
  rw [div_self hu.ne']
  have hS : 0 < Real.sqrt (2*Real.pi*u/M) := by positivity
  have hX : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hSum : 0 < Real.sqrt (t/u+(Real.pi*M/(2*u))*x)+
      Real.sqrt (1+(Real.pi*M/(2*u))*x) := by positivity
  have hGap : t-u ≠ 0 := sub_ne_zero.mpr htu.ne'
  unfold atkinsonGapFrequency atkinsonGapSlopeProfile
  have hsq := Real.sq_sqrt hx.le
  field_simp [hM.ne',hu.ne',hx.ne',hS.ne',hX.ne',hSum.ne',hGap,Real.pi_ne_zero]
  nlinarith [hsq]

theorem contDiffAt_atkinsonGapSlopeProfile
    {q r x : ℝ} (hr : 0 < r) (hx : 0 < x)
    (hqr : 0 < r+q*x) (hqx : 0 < 1+q*x) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ × ℝ => atkinsonGapSlopeProfile p.1 p.2.1 p.2.2)
      (q,r,x) := by
  unfold atkinsonGapSlopeProfile
  have hden : Real.sqrt x*(Real.sqrt (r+q*x)+Real.sqrt (1+q*x)) ≠ 0 := by
    positivity
  fun_prop (disch := positivity)

end TaoTrudgianYang2025
