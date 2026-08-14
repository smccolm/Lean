import RiemannZeta.GuthMaynard.DFIVoronoiDual
import RiemannZeta.External.PNT.ZetaAppendix
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The order-zero Bessel kernels in DFI Proposition 1

This file starts from the classical real integral representations of the
order-zero kernels occurring in the Duke--Friedlander--Iwaniec divisor
Voronoi formula.  The first result is the source-strength pointwise estimate
for the positive-sign modified-Bessel kernel.  It is proved from its defining
integral, not postulated as a special-function bound.
-/

open Complex Set MeasureTheory
open scoped Topology

namespace RiemannZeta.GuthMaynard

/-- The positive-sign order-zero kernel, in the classical representation
`K₀(x) = ∫₀∞ exp (-x cosh t) dt` for `x > 0`. -/
noncomputable def dfiBesselK0 (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * Real.cosh t)

/-- The elementary quadratic lower bound for the hyperbolic cosine. -/
theorem one_add_sq_div_two_le_cosh (t : ℝ) :
    1 + t ^ 2 / 2 ≤ Real.cosh t := by
  rw [Real.cosh_eq_tsum]
  have hsummable := (Real.hasSum_cosh t).summable
  have hnonneg : ∀ n : ℕ, 0 ≤ t ^ (2 * n) / (2 * n).factorial := by
    intro n
    rw [show 2 * n = n * 2 by omega, pow_mul]
    positivity
  have hpartial := hsummable.sum_le_tsum (s := Finset.range 2)
    (fun n hn => hnonneg n)
  norm_num [Finset.sum_range_succ] at hpartial ⊢
  exact hpartial

/-- Gaussian domination of the positive-sign Bessel integrand. -/
theorem dfiBesselK0_integrand_le_gaussian
    {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    Real.exp (-x * Real.cosh t) ≤ Real.exp (-(x / 2) * t ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hcosh := one_add_sq_div_two_le_cosh t
  calc
    -x * Real.cosh t ≤ -x * (1 + t ^ 2 / 2) := by
      exact mul_le_mul_of_nonpos_left hcosh (neg_nonpos.mpr hx)
    _ ≤ -(x / 2) * t ^ 2 := by
      nlinarith

/-- The defining integral of `dfiBesselK0` is absolutely integrable for a
positive argument. -/
theorem integrableOn_dfiBesselK0_integrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-x * Real.cosh t)) (Set.Ioi 0) := by
  have hgauss : IntegrableOn
      (fun t : ℝ => Real.exp (-(x / 2) * t ^ 2)) (Set.Ioi 0) := by
    exact (integrable_exp_neg_mul_sq (by positivity : 0 < x / 2)).integrableOn
  refine hgauss.mono' ?_ ?_
  · exact (Real.continuous_exp.comp
      (continuous_const.mul Real.continuous_cosh)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact dfiBesselK0_integrand_le_gaussian hx.le t

/-- DFI's source-strength trivial bound `K₀(x) ≪ x⁻¹ᐟ²`, with an explicit
constant. -/
theorem abs_dfiBesselK0_le {x : ℝ} (hx : 0 < x) :
    |dfiBesselK0 x| ≤ Real.sqrt (Real.pi / (x / 2)) / 2 := by
  have hInt := integrableOn_dfiBesselK0_integrand hx
  have hGauss : IntegrableOn
      (fun t : ℝ => Real.exp (-(x / 2) * t ^ 2)) (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < x / 2)).integrableOn
  have hnonneg : 0 ≤ dfiBesselK0 x := by
    unfold dfiBesselK0
    exact integral_nonneg fun _ => (Real.exp_pos _).le
  rw [abs_of_nonneg hnonneg]
  unfold dfiBesselK0
  calc
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * Real.cosh t) ≤
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(x / 2) * t ^ 2) := by
      exact setIntegral_mono hInt hGauss fun t =>
        dfiBesselK0_integrand_le_gaussian hx.le t
    _ = Real.sqrt (Real.pi / (x / 2)) / 2 := integral_gaussian_Ioi (x / 2)

/-- A simpler power form of the preceding estimate. -/
theorem abs_dfiBesselK0_le_two_div_sqrt {x : ℝ} (hx : 0 < x) :
    |dfiBesselK0 x| ≤ 2 / Real.sqrt x := by
  have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hquotPos : 0 ≤ Real.pi / (x / 2) := by positivity
  have hsquareA : Real.sqrt (Real.pi / (x / 2)) ^ 2 =
      Real.pi / (x / 2) := Real.sq_sqrt hquotPos
  have hsquareX : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hprodNonneg :
      0 ≤ Real.sqrt (Real.pi / (x / 2)) * Real.sqrt x := by positivity
  have hprodSq :
      (Real.sqrt (Real.pi / (x / 2)) * Real.sqrt x) ^ 2 =
        2 * Real.pi := by
    rw [mul_pow, hsquareA, hsquareX]
    field_simp [hx.ne']
  have hprod :
      Real.sqrt (Real.pi / (x / 2)) * Real.sqrt x ≤ 4 := by
    nlinarith
  refine (abs_dfiBesselK0_le hx).trans ?_
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  rw [show 2 / Real.sqrt x * 2 = 4 / Real.sqrt x by ring]
  apply (le_div_iff₀ hsqrtPos).2
  exact hprod

/-- The exponentially decaying term in Schläfli's real integral
representation of the order-zero Neumann kernel. -/
noncomputable def dfiBesselY0Tail (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-x * t) / Real.sqrt (1 + t ^ 2)

/-- The oscillatory term in Schläfli's representation, written after the
change of variables `u = π/2 - θ`.  Taking the imaginary part packages the
real sine integral while retaining the complex exponential needed for the
first-derivative estimate. -/
noncomputable def dfiBesselY0Osc (x : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..Real.pi / 2,
    Complex.exp (Complex.I * (x * Real.cos u))).im

/-- DFI's order-zero Neumann kernel, defined by the DLMF/Schläfli integral
representation
`Y₀(x) = (2/π) ( ∫₀^π/² sin(x cos u) du
                         - ∫₀^∞ exp(-xt)/sqrt(1+t²) dt )`.
The representation is used only for positive arguments, exactly as in DFI
Proposition 1. -/
noncomputable def dfiBesselY0 (x : ℝ) : ℝ :=
  (2 / Real.pi) * (dfiBesselY0Osc x - dfiBesselY0Tail x)

/-- The DLMF tail is absolutely integrable for positive arguments. -/
theorem integrableOn_dfiBesselY0Tail_integrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-x * t) / Real.sqrt (1 + t ^ 2))
      (Set.Ioi 0) := by
  have hExp : IntegrableOn (fun t : ℝ => t ^ (0 : ℝ) *
      Real.exp (-x * t ^ (1 : ℝ))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hx
  have hExp' : IntegrableOn (fun t : ℝ => Real.exp (-x * t)) (Set.Ioi 0) := by
    convert hExp using 1
    ext t
    simp
  refine hExp'.mono' ?_ ?_
  · have hcont : ContinuousOn
        (fun t : ℝ => Real.exp (-x * t) / Real.sqrt (1 + t ^ 2))
        (Set.Ioi 0) := by
      exact (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousOn.div
          (Real.continuous_sqrt.comp
            (continuous_const.add (continuous_id.pow 2))).continuousOn
          (fun t ht => ne_of_gt (Real.sqrt_pos.2 (by positivity)))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _)]
    have hsqrt : 1 ≤ Real.sqrt (1 + t ^ 2) := by
      have harg : 0 ≤ 1 + t ^ 2 := by positivity
      have hsquare := Real.sq_sqrt harg
      have hnonneg := Real.sqrt_nonneg (1 + t ^ 2)
      nlinarith [sq_nonneg t]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self (Real.exp_pos _).le hsqrt

/-- The nonoscillatory term in the `Y₀` representation already has the
source-strength square-root bound. -/
theorem abs_dfiBesselY0Tail_le {x : ℝ} (hx : 0 < x) :
    |dfiBesselY0Tail x| ≤ Real.sqrt Real.pi / Real.sqrt x := by
  have hHalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hGammaInt := Real.integral_rpow_mul_exp_neg_mul_Ioi hHalf hx
  have hMajorant : IntegrableOn
      (fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(x * t)))
      (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := -(1 / 2 : ℝ)) (b := x)
      (by norm_num) (by norm_num) hx
    convert h using 1
    ext t
    norm_num
  have hTail := integrableOn_dfiBesselY0Tail_integrand hx
  have hnonneg : 0 ≤ dfiBesselY0Tail x := by
    unfold dfiBesselY0Tail
    exact integral_nonneg fun t => div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  rw [abs_of_nonneg hnonneg]
  unfold dfiBesselY0Tail
  calc
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * t) / Real.sqrt (1 + t ^ 2) ≤
        ∫ t in Set.Ioi (0 : ℝ),
          t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(x * t)) := by
      exact setIntegral_mono_on hTail hMajorant measurableSet_Ioi fun t ht => by
        have htPos : 0 < t := ht
        have hsqrtT : Real.sqrt t ≤ Real.sqrt (1 + t ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg (t - 1 / 2)]
        have hsqrtTPos : 0 < Real.sqrt t := Real.sqrt_pos.2 htPos
        have hsqrtDenPos : 0 < Real.sqrt (1 + t ^ 2) := by positivity
        have hInv : 1 / Real.sqrt (1 + t ^ 2) ≤ 1 / Real.sqrt t := by
          exact one_div_le_one_div_of_le hsqrtTPos hsqrtT
        rw [show t ^ ((1 / 2 : ℝ) - 1) = 1 / Real.sqrt t by
          rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring,
            Real.rpow_neg htPos.le, Real.sqrt_eq_rpow]
          ring]
        rw [div_eq_mul_inv, one_div]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left hInv (Real.exp_pos (-x * t)).le
    _ = (1 / x) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2) := hGammaInt
    _ = Real.sqrt Real.pi / Real.sqrt x := by
      rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [Real.div_rpow zero_le_one hx.le]
      norm_num
      ring

/-- On the nonstationary part of Schläfli's oscillatory integral, the
first-derivative test gives the required square-root cancellation. -/
theorem norm_dfiBesselY0Osc_far_le {x : ℝ} (hx : 1 ≤ x) :
    ‖∫ u in (1 / Real.sqrt x)..Real.pi / 2,
        Complex.exp (Complex.I * (x * Real.cos u))‖ ≤
      4 / Real.sqrt x := by
  let δ : ℝ := 1 / Real.sqrt x
  let φ : ℝ → ℝ := fun u => x * Real.cos u / (2 * Real.pi)
  let g : ℝ → ℝ := fun u => -(2 * Real.pi) / (x * Real.sin u)
  have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxPos
  have hsqrtOne : 1 ≤ Real.sqrt x := by
    nlinarith [Real.sq_sqrt hxPos.le, Real.sqrt_nonneg x]
  have hδPos : 0 < δ := by dsimp [δ]; positivity
  have hδLeOne : δ ≤ 1 := by
    dsimp [δ]
    exact (div_le_one hsqrtPos).2 hsqrtOne
  have hOneLtHalfPi : (1 : ℝ) < Real.pi / 2 := by
    linarith [Real.pi_gt_three]
  have hδLtHalfPi : δ < Real.pi / 2 := hδLeOne.trans_lt hOneLtHalfPi
  have hHalfPiLtPi : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  have hsinPos {u : ℝ} (hu : u ∈ Set.Icc δ (Real.pi / 2)) :
      0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi (hδPos.trans_le hu.1)
      (hu.2.trans_lt hHalfPiLtPi)
  have hφDeriv (u : ℝ) : deriv φ u = -(x * Real.sin u) / (2 * Real.pi) := by
    dsimp [φ]
    rw [show (fun y : ℝ => x * Real.cos y / (2 * Real.pi)) =
        (fun y : ℝ => (x / (2 * Real.pi)) * Real.cos y) by
      funext y
      ring]
    rw [((Real.hasDerivAt_cos u).const_mul (x / (2 * Real.pi))).deriv]
    ring
  have hPhase := ZetaAppendix.nonstationary_phase_integral_bound hδLtHalfPi
    φ (by fun_prop)
    (fun u hu => by
      rw [hφDeriv]
      exact div_ne_zero (neg_ne_zero.mpr
        (mul_ne_zero hxPos.ne' (hsinPos hu).ne'))
        (mul_ne_zero (by norm_num) Real.pi_ne_zero))
    (fun _ => 1) g
    (fun u => by
      rw [hφDeriv]
      dsimp [g]
      by_cases hsin : Real.sin u = 0
      · simp [hsin]
      · field_simp [hxPos.ne', hsin, Real.pi_ne_zero])
    (by
      intro u hu
      dsimp [g]
      fun_prop (disch := exact (mul_ne_zero hxPos.ne' (hsinPos hu).ne')))
    (by
      intro u hu v hv huv
      have huRange : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor
        · linarith [Real.pi_pos, hδPos, hu.1]
        · exact hu.2
      have hvRange : v ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor
        · linarith [Real.pi_pos, hδPos, hv.1]
        · exact hv.2
      have hsinMono : Real.sin u ≤ Real.sin v :=
        Real.monotoneOn_sin huRange hvRange huv
      have hsu := hsinPos hu
      have hsv := hsinPos hv
      have hgu : |g u| = 2 * Real.pi / (x * Real.sin u) := by
        dsimp [g]
        rw [abs_div, abs_neg, abs_of_pos (mul_pos hxPos hsu),
          abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      have hgv : |g v| = 2 * Real.pi / (x * Real.sin v) := by
        dsimp [g]
        rw [abs_div, abs_neg, abs_of_pos (mul_pos hxPos hsv),
          abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      change |g v| ≤ |g u|
      rw [hgu, hgv]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos hxPos hsu) (mul_le_mul_of_nonneg_left hsinMono hxPos.le))
  have hPhase' :
      ‖∫ u in δ..Real.pi / 2,
          Complex.exp (Complex.I * (x * Real.cos u))‖ ≤ |g δ| / Real.pi := by
    rw [intervalIntegral.integral_of_le hδLtHalfPi.le,
      ← integral_Icc_eq_integral_Ioc]
    convert hPhase using 1
    · apply congrArg Norm.norm
      apply setIntegral_congr_fun measurableSet_Icc
      intro u _
      dsimp [φ]
      push_cast
      field_simp [Real.pi_ne_zero]
  have hsinδ : δ / 2 ≤ Real.sin δ := by
    have hStrict := Real.sin_gt_sub_cube hδPos hδLeOne
    nlinarith [sq_nonneg δ, mul_self_le_mul_self (show 0 ≤ δ from hδPos.le) hδLeOne]
  have hsinδPos : 0 < Real.sin δ := lt_of_lt_of_le (half_pos hδPos) hsinδ
  calc
    ‖∫ u in (1 / Real.sqrt x)..Real.pi / 2,
        Complex.exp (Complex.I * (x * Real.cos u))‖ =
        ‖∫ u in δ..Real.pi / 2,
          Complex.exp (Complex.I * (x * Real.cos u))‖ := by rfl
    _ ≤ |g δ| / Real.pi := hPhase'
    _ = 2 / (x * Real.sin δ) := by
      dsimp [g]
      rw [abs_div, abs_neg, abs_of_pos (mul_pos hxPos hsinδPos),
        abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      field_simp [Real.pi_ne_zero]
    _ ≤ 4 / Real.sqrt x := by
      have hden : x * (δ / 2) ≤ x * Real.sin δ :=
        mul_le_mul_of_nonneg_left hsinδ hxPos.le
      have hsmallDenPos : 0 < x * (δ / 2) := mul_pos hxPos (half_pos hδPos)
      calc
        2 / (x * Real.sin δ) ≤ 2 / (x * (δ / 2)) :=
          div_le_div_of_nonneg_left (by norm_num) hsmallDenPos hden
        _ = 4 / Real.sqrt x := by
          dsimp [δ]
          field_simp [hxPos.ne', hsqrtPos.ne']
          nlinarith [Real.sq_sqrt hxPos.le]

/-- The complete oscillatory term in Schläfli's representation satisfies a
uniform square-root estimate. -/
theorem abs_dfiBesselY0Osc_le {x : ℝ} (hx : 0 < x) :
    |dfiBesselY0Osc x| ≤ 5 / Real.sqrt x := by
  let F : ℝ → ℂ := fun u =>
    Complex.exp (Complex.I * (x * Real.cos u))
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hFint (a b : ℝ) : IntervalIntegrable F volume a b :=
    hFcont.intervalIntegrable a b
  have hnormF (u : ℝ) : ‖F u‖ = 1 := by
    dsimp [F]
    rw [Complex.norm_exp]
    simp
  have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have him :
      |dfiBesselY0Osc x| ≤
        ‖∫ u in (0 : ℝ)..Real.pi / 2, F u‖ := by
    unfold dfiBesselY0Osc
    exact Complex.abs_im_le_norm _
  by_cases hxOne : x ≤ 1
  · have hWhole := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := F) (a := (0 : ℝ)) (b := Real.pi / 2) (C := (1 : ℝ))
        (fun u _ => by rw [hnormF])
    have hsqrtLe : Real.sqrt x ≤ 1 := by
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    calc
      |dfiBesselY0Osc x| ≤
          ‖∫ u in (0 : ℝ)..Real.pi / 2, F u‖ := him
      _ ≤ Real.pi / 2 := by
        simpa [abs_of_pos (half_pos Real.pi_pos)] using hWhole
      _ ≤ 5 / Real.sqrt x := by
        apply (le_div_iff₀ hsqrtPos).2
        have hpi : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]
        nlinarith
  · have hxLarge : 1 ≤ x := le_of_not_ge hxOne
    let δ : ℝ := 1 / Real.sqrt x
    have hδPos : 0 < δ := by dsimp [δ]; positivity
    have hδLtHalfPi : δ < Real.pi / 2 := by
      have hsqrtOne : 1 ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      have hδLeOne : δ ≤ 1 := by
        dsimp [δ]
        exact (div_le_one hsqrtPos).2 hsqrtOne
      linarith [Real.pi_gt_three]
    have hNear : ‖∫ u in (0 : ℝ)..δ, F u‖ ≤ δ := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := F) (a := (0 : ℝ)) (b := δ) (C := (1 : ℝ))
        (fun u _ => by rw [hnormF])
      simpa [abs_of_pos hδPos] using h
    have hFar : ‖∫ u in δ..Real.pi / 2, F u‖ ≤
        4 / Real.sqrt x := by
      simpa [F, δ] using norm_dfiBesselY0Osc_far_le hxLarge
    have hSplit :
        (∫ u in (0 : ℝ)..Real.pi / 2, F u) =
          (∫ u in (0 : ℝ)..δ, F u) +
            ∫ u in δ..Real.pi / 2, F u := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hFint 0 δ) (hFint δ (Real.pi / 2))).symm
    calc
      |dfiBesselY0Osc x| ≤
          ‖∫ u in (0 : ℝ)..Real.pi / 2, F u‖ := him
      _ = ‖(∫ u in (0 : ℝ)..δ, F u) +
            ∫ u in δ..Real.pi / 2, F u‖ := by rw [hSplit]
      _ ≤ ‖∫ u in (0 : ℝ)..δ, F u‖ +
            ‖∫ u in δ..Real.pi / 2, F u‖ := norm_add_le _ _
      _ ≤ δ + 4 / Real.sqrt x := add_le_add hNear hFar
      _ = 5 / Real.sqrt x := by
        dsimp [δ]
        ring

/-- DFI's source-strength trivial estimate `Y₀(x) ≪ x⁻¹ᐟ²`, proved
directly from Schläfli's representation. -/
theorem abs_dfiBesselY0_le_seven_div_sqrt {x : ℝ} (hx : 0 < x) :
    |dfiBesselY0 x| ≤ 7 / Real.sqrt x := by
  have hOsc := abs_dfiBesselY0Osc_le hx
  have hTail := abs_dfiBesselY0Tail_le hx
  have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsqrtPi : Real.sqrt Real.pi < 2 := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi,
      Real.pi_lt_four]
  have hCoeff : |2 / Real.pi| < 1 := by
    rw [abs_of_pos (div_pos (by norm_num) Real.pi_pos), div_lt_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  unfold dfiBesselY0
  calc
    |2 / Real.pi * (dfiBesselY0Osc x - dfiBesselY0Tail x)| =
        |2 / Real.pi| * |dfiBesselY0Osc x - dfiBesselY0Tail x| := abs_mul _ _
    _ ≤ |2 / Real.pi| *
        (|dfiBesselY0Osc x| + |dfiBesselY0Tail x|) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa using abs_sub_le (dfiBesselY0Osc x) 0 (dfiBesselY0Tail x))
        (abs_nonneg _)
    _ ≤ 1 * (5 / Real.sqrt x + Real.sqrt Real.pi / Real.sqrt x) := by
      exact mul_le_mul hCoeff.le (add_le_add hOsc hTail)
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
    _ ≤ 7 / Real.sqrt x := by
      apply (le_div_iff₀ hsqrtPos).2
      field_simp [hsqrtPos.ne']
      nlinarith

/-- The square-root rescaling used in DFI's retained Bessel transforms. -/
theorem one_div_sqrt_four_pi_sqrt_div_le
    {q x y : ℝ} (hq : 0 < q) (hx : 0 < x) (hy : 0 < y) :
    1 / Real.sqrt (4 * Real.pi * Real.sqrt (x * y) / q) ≤
      Real.sqrt q / Real.sqrt (Real.sqrt (x * y)) := by
  let A : ℝ := 4 * Real.pi * Real.sqrt (x * y) / q
  have hxy : 0 < x * y := mul_pos hx hy
  have hA : 0 < A := by dsimp [A]; positivity
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hsqrtQ : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hFourth : 0 < Real.sqrt (Real.sqrt (x * y)) := by positivity
  have hsqA := Real.sq_sqrt hA.le
  have hsqQ := Real.sq_sqrt hq.le
  have hsqXY := Real.sq_sqrt hxy.le
  have hsqFourth := Real.sq_sqrt (Real.sqrt_pos.2 hxy).le
  have hscale : A * q = 4 * Real.pi * Real.sqrt (x * y) := by
    dsimp [A]
    field_simp [hq.ne']
  have hrootScale :
      Real.sqrt (Real.sqrt (x * y)) ≤ Real.sqrt A * Real.sqrt q := by
    have hleft := Real.sqrt_nonneg (Real.sqrt (x * y))
    have hright : 0 ≤ Real.sqrt A * Real.sqrt q := by positivity
    nlinarith [Real.pi_gt_three]
  dsimp [A] at hsqrtA ⊢
  exact (div_le_div_iff₀ hsqrtA hFourth).2 (by
    simpa [A, mul_comm] using hrootScale)

/-- DFI's retained-range pointwise bound for the positive-sign kernel after
the source scaling `4π√(xy)/q`. -/
theorem abs_dfiBesselK0_scaled_le
    {q x y : ℝ} (hq : 0 < q) (hx : 0 < x) (hy : 0 < y) :
    |dfiBesselK0 (4 * Real.pi * Real.sqrt (x * y) / q)| ≤
      2 * Real.sqrt q / Real.sqrt (Real.sqrt (x * y)) := by
  have hArg : 0 < 4 * Real.pi * Real.sqrt (x * y) / q := by positivity
  calc
    |dfiBesselK0 (4 * Real.pi * Real.sqrt (x * y) / q)| ≤
        2 / Real.sqrt (4 * Real.pi * Real.sqrt (x * y) / q) :=
      abs_dfiBesselK0_le_two_div_sqrt hArg
    _ ≤ 2 * (Real.sqrt q / Real.sqrt (Real.sqrt (x * y))) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [one_div] using
          one_div_sqrt_four_pi_sqrt_div_le hq hx hy) (by norm_num)
    _ = 2 * Real.sqrt q / Real.sqrt (Real.sqrt (x * y)) := by ring

/-- DFI's retained-range pointwise bound for the equal-sign kernel after
the source scaling `4π√(xy)/q`. -/
theorem abs_dfiBesselY0_scaled_le
    {q x y : ℝ} (hq : 0 < q) (hx : 0 < x) (hy : 0 < y) :
    |dfiBesselY0 (4 * Real.pi * Real.sqrt (x * y) / q)| ≤
      7 * Real.sqrt q / Real.sqrt (Real.sqrt (x * y)) := by
  have hArg : 0 < 4 * Real.pi * Real.sqrt (x * y) / q := by positivity
  calc
    |dfiBesselY0 (4 * Real.pi * Real.sqrt (x * y) / q)| ≤
        7 / Real.sqrt (4 * Real.pi * Real.sqrt (x * y) / q) :=
      abs_dfiBesselY0_le_seven_div_sqrt hArg
    _ ≤ 7 * (Real.sqrt q / Real.sqrt (Real.sqrt (x * y))) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [one_div] using
          one_div_sqrt_four_pi_sqrt_div_le hq hx hy) (by norm_num)
    _ = 7 * Real.sqrt q / Real.sqrt (Real.sqrt (x * y)) := by ring

/-- The literal positive-sign Bessel transform in DFI Proposition 1. -/
noncomputable def dfiVoronoiPlusBesselTransform
    (q : ℕ) [NeZero q] (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  (4 / (q : ℂ)) * ∫ x in Set.Ioi (0 : ℝ),
    g x * (dfiBesselK0
      (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)

/-- The literal equal-sign Bessel transform in DFI Proposition 1. -/
noncomputable def dfiVoronoiMinusBesselTransform
    (q : ℕ) [NeZero q] (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  (-(2 * Real.pi) / (q : ℂ)) * ∫ x in Set.Ioi (0 : ℝ),
    g x * (dfiBesselY0
      (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)

/-- Weighted physical norm naturally produced by the pointwise order-zero
Bessel estimates. -/
noncomputable def dfiBesselQuarterNorm (g : ℝ → ℂ) (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    ‖g x‖ / Real.sqrt (Real.sqrt (x * n))

/-- The literal positive-sign transform has DFI's retained-frequency
quarter-power size. -/
theorem norm_dfiVoronoiPlusBesselTransform_le
    (q : ℕ) [NeZero q] (g : ℝ → ℂ) (n : ℕ) (hn : 0 < n)
    (hMajor : IntegrableOn
      (fun x : ℝ => ‖g x‖ / Real.sqrt (Real.sqrt (x * n))) (Set.Ioi 0)) :
    ‖dfiVoronoiPlusBesselTransform q g n‖ ≤
      8 / Real.sqrt q * dfiBesselQuarterNorm g n := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hIntegral :
      ‖∫ x in Set.Ioi (0 : ℝ),
          g x * (dfiBesselK0
            (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)‖ ≤
        2 * Real.sqrt q * dfiBesselQuarterNorm g n := by
    calc
      ‖∫ x in Set.Ioi (0 : ℝ),
          g x * (dfiBesselK0
            (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)‖ ≤
          ∫ x in Set.Ioi (0 : ℝ),
            2 * Real.sqrt q *
              (‖g x‖ / Real.sqrt (Real.sqrt (x * n))) := by
        apply norm_integral_le_of_norm_le
          (by simpa [mul_assoc] using hMajor.const_mul (2 * Real.sqrt q))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxR : 0 < x := hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          ‖g x‖ * |dfiBesselK0
              (4 * Real.pi * Real.sqrt (x * n) / q)| ≤
              ‖g x‖ *
                (2 * Real.sqrt q / Real.sqrt (Real.sqrt (x * n))) :=
            mul_le_mul_of_nonneg_left
              (abs_dfiBesselK0_scaled_le hq hxR hnR) (norm_nonneg _)
          _ = 2 * Real.sqrt q *
              (‖g x‖ / Real.sqrt (Real.sqrt (x * n))) := by ring
      _ = 2 * Real.sqrt q * dfiBesselQuarterNorm g n := by
        unfold dfiBesselQuarterNorm
        rw [MeasureTheory.integral_const_mul]
  unfold dfiVoronoiPlusBesselTransform
  rw [norm_mul]
  have hCoeffNorm : ‖(4 / (q : ℂ))‖ = 4 / q := by
    rw [norm_div, Complex.norm_natCast]
    norm_num
  rw [hCoeffNorm]
  have hsqrtQPos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  calc
    4 / q * ‖∫ x in Set.Ioi (0 : ℝ),
        g x * (dfiBesselK0
          (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)‖ ≤
        4 / q * (2 * Real.sqrt q * dfiBesselQuarterNorm g n) :=
      mul_le_mul_of_nonneg_left hIntegral (by positivity)
    _ = 8 / Real.sqrt q * dfiBesselQuarterNorm g n := by
      field_simp [NeZero.ne q, hsqrtQPos.ne']
      rw [Real.sq_sqrt hq.le]
      ring

/-- The literal equal-sign transform has the same DFI quarter-power size,
with an explicit absolute constant. -/
theorem norm_dfiVoronoiMinusBesselTransform_le
    (q : ℕ) [NeZero q] (g : ℝ → ℂ) (n : ℕ) (hn : 0 < n)
    (hMajor : IntegrableOn
      (fun x : ℝ => ‖g x‖ / Real.sqrt (Real.sqrt (x * n))) (Set.Ioi 0)) :
    ‖dfiVoronoiMinusBesselTransform q g n‖ ≤
      14 * Real.pi / Real.sqrt q * dfiBesselQuarterNorm g n := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hIntegral :
      ‖∫ x in Set.Ioi (0 : ℝ),
          g x * (dfiBesselY0
            (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)‖ ≤
        7 * Real.sqrt q * dfiBesselQuarterNorm g n := by
    calc
      ‖∫ x in Set.Ioi (0 : ℝ),
          g x * (dfiBesselY0
            (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)‖ ≤
          ∫ x in Set.Ioi (0 : ℝ),
            7 * Real.sqrt q *
              (‖g x‖ / Real.sqrt (Real.sqrt (x * n))) := by
        apply norm_integral_le_of_norm_le
          (by simpa [mul_assoc] using hMajor.const_mul (7 * Real.sqrt q))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxR : 0 < x := hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          ‖g x‖ * |dfiBesselY0
              (4 * Real.pi * Real.sqrt (x * n) / q)| ≤
              ‖g x‖ *
                (7 * Real.sqrt q / Real.sqrt (Real.sqrt (x * n))) :=
            mul_le_mul_of_nonneg_left
              (abs_dfiBesselY0_scaled_le hq hxR hnR) (norm_nonneg _)
          _ = 7 * Real.sqrt q *
              (‖g x‖ / Real.sqrt (Real.sqrt (x * n))) := by ring
      _ = 7 * Real.sqrt q * dfiBesselQuarterNorm g n := by
        unfold dfiBesselQuarterNorm
        rw [MeasureTheory.integral_const_mul]
  unfold dfiVoronoiMinusBesselTransform
  rw [norm_mul]
  have hCoeffNorm :
      ‖(-(2 * Real.pi) / (q : ℂ))‖ = (2 * Real.pi) / q := by
    rw [norm_div, Complex.norm_natCast, norm_neg, norm_mul,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hCoeffNorm]
  have hsqrtQPos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  calc
    (2 * Real.pi) / q * ‖∫ x in Set.Ioi (0 : ℝ),
        g x * (dfiBesselY0
          (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)‖ ≤
        (2 * Real.pi) / q *
          (7 * Real.sqrt q * dfiBesselQuarterNorm g n) :=
      mul_le_mul_of_nonneg_left hIntegral (by positivity)
    _ = 14 * Real.pi / Real.sqrt q * dfiBesselQuarterNorm g n := by
      field_simp [NeZero.ne q, hsqrtQPos.ne']
      rw [Real.sq_sqrt hq.le]
      ring

end RiemannZeta.GuthMaynard
