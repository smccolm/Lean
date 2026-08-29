import RiemannZeta.GuthMaynard.HughesYoungShiftTailConsumer
import RiemannZeta.GuthMaynard.HughesYoungSmallContourTail

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative finite small-contour correction

This module estimates the literal loss caused by restricting the finite
equation-(83) Mellin integral to `[-T/8,T/8]`.  The analytic input is the
height-uniform low-contour estimate already proved for the regularized
equation-(84) kernel.  The first step below makes its arithmetic coefficient
dependence explicit and uniform in the finite shift.
-/

/-- Removing a symmetric finite interval from an absolutely convergent
whole-line integral leaves exactly the integral over its measurable
complement, and its norm is bounded by the corresponding norm integral.
This is the measure-theoretic form of the two tails used below. -/
theorem norm_integral_sub_symmetricIntervalIntegral_le_compl_norm
    {f : ℝ → ℂ} (hf : Integrable f) {H : ℝ} (hH : 0 ≤ H) :
    ‖(∫ u : ℝ, f u) - ∫ u in -H..H, f u‖ ≤
      ∫ u in (Set.Ioc (-H) H)ᶜ, ‖f u‖ := by
  rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H),
    ← MeasureTheory.setIntegral_compl measurableSet_Ioc hf]
  exact MeasureTheory.norm_integral_le_integral_norm _

/-- A fixed mass for the Gaussian left after absorbing the polynomial
ordinate factors in the moving-contour kernel. -/
noncomputable def hughesYoungSmallContourGaussianTailConstant : ℝ :=
  hughesYoungGaussianPowerConstant 17 *
      (∫ u : ℝ, Real.exp (-43 * u ^ 2)) + 1

theorem hughesYoungSmallContourGaussianTailConstant_pos :
    0 < hughesYoungSmallContourGaussianTailConstant := by
  unfold hughesYoungSmallContourGaussianTailConstant
  have hnonneg : 0 ≤ ∫ u : ℝ, Real.exp (-43 * u ^ 2) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hG := hughesYoungGaussianPowerConstant_pos 17
  positivity

/-- The two tails outside `[-H,H]` of the equation-(84) Gaussian profile
have a uniform `exp (-40 H²)` bound. -/
theorem integral_compl_Ioc_exp_neg84_mul_one_add_abs_pow_seventeen_le
    {H : ℝ} (hH : 1 ≤ H) :
    (∫ u in (Set.Ioc (-H) H)ᶜ,
        Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17) ≤
      hughesYoungSmallContourGaussianTailConstant *
        Real.exp (-40 * H ^ 2) := by
  let G : ℝ := hughesYoungGaussianPowerConstant 17
  let g : ℝ → ℝ := fun u =>
    G * Real.exp (-40 * H ^ 2) * Real.exp (-43 * u ^ 2)
  have hG : 0 ≤ G := (hughesYoungGaussianPowerConstant_pos 17).le
  have hg : Integrable g := by
    simpa only [g, mul_assoc] using
      ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 43)).const_mul
        (Real.exp (-40 * H ^ 2))).const_mul G
  have hsource : Integrable
      (fun u : ℝ => Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17) :=
    integrable_exp_neg_84_mul_one_add_abs_pow 17
  have hpoint : ∀ u ∈ (Set.Ioc (-H) H)ᶜ,
      Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17 ≤ g u := by
    intro u hu
    have hH0 : 0 ≤ H := zero_le_one.trans hH
    have hHu : H ≤ |u| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or] at hu
      rcases hu with hu | hu
      · have : u ≤ -H := le_of_not_gt hu
        rw [abs_of_nonpos (this.trans (neg_nonpos.mpr hH0))]
        linarith
      · have : H < u := lt_of_not_ge hu
        rw [abs_of_nonneg (hH0.trans this.le)]
        exact this.le
    have hpoly := pow_add_one_le_gaussianPowerConstant_mul_exp
      (abs_nonneg u) 17
    have hsq : H ^ 2 ≤ u ^ 2 := by
      rw [← sq_abs u]
      nlinarith [sq_nonneg (|u| - H)]
    have hexp :
        Real.exp (-84 * u ^ 2) * Real.exp |u| ≤
          Real.exp (-40 * H ^ 2) * Real.exp (-43 * u ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have habsOne : 1 ≤ |u| := hH.trans hHu
      have habs : |u| ≤ u ^ 2 := by
        rw [← sq_abs u]
        nlinarith [sq_nonneg (|u| - 1)]
      have hHsq : 40 * H ^ 2 ≤ 40 * u ^ 2 := by nlinarith
      nlinarith
    dsimp only [g, G]
    calc
      Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17 ≤
          Real.exp (-84 * u ^ 2) *
            (hughesYoungGaussianPowerConstant 17 * Real.exp |u|) := by
              gcongr
              simpa only [add_comm] using hpoly
      _ = hughesYoungGaussianPowerConstant 17 *
          (Real.exp (-84 * u ^ 2) * Real.exp |u|) := by ring
      _ ≤ hughesYoungGaussianPowerConstant 17 *
          (Real.exp (-40 * H ^ 2) * Real.exp (-43 * u ^ 2)) := by
            gcongr
      _ = _ := by ring
  have hset := MeasureTheory.setIntegral_mono_on hsource.integrableOn
    hg.integrableOn measurableSet_Ioc.compl hpoint
  calc
    _ ≤ ∫ u in (Set.Ioc (-H) H)ᶜ, g u := hset
    _ ≤ ∫ u : ℝ, g u :=
      MeasureTheory.setIntegral_le_integral hg
        (Filter.Eventually.of_forall fun u => by dsimp only [g]; positivity)
    _ = G * Real.exp (-40 * H ^ 2) *
          (∫ u : ℝ, Real.exp (-43 * u ^ 2)) := by
      dsimp only [g]
      rw [MeasureTheory.integral_const_mul]
    _ ≤ hughesYoungSmallContourGaussianTailConstant *
          Real.exp (-40 * H ^ 2) := by
      unfold hughesYoungSmallContourGaussianTailConstant
      have hmass : 0 ≤ ∫ u : ℝ, Real.exp (-43 * u ^ 2) :=
        integral_nonneg fun _ => (Real.exp_pos _).le
      have htail : 0 ≤ Real.exp (-40 * H ^ 2) := (Real.exp_pos _).le
      dsimp only [G]
      nlinarith

/-- A fixed convergent mass which dominates both logarithmic factors in the
four arithmetic moments of equation (84). -/
noncomputable def hughesYoungEquation84LogProfileMass : ℝ :=
  (∑' q : ℕ,
    ((q : ℝ) ^ 2)⁻¹ * (1 + 4 * Real.log (q : ℝ)) ^ 2) + 1

theorem summable_hughesYoungEquation84LogProfile :
    Summable (fun q : ℕ =>
      ((q : ℝ) ^ 2)⁻¹ * (1 + 4 * Real.log (q : ℝ)) ^ 2) :=
  summable_natCast_inv_sq_mul_four_log_profile_sq 1 (by norm_num)

theorem hughesYoungEquation84LogProfileMass_pos :
    0 < hughesYoungEquation84LogProfileMass := by
  unfold hughesYoungEquation84LogProfileMass
  have hnonneg : 0 ≤ ∑' q : ℕ,
      ((q : ℝ) ^ 2)⁻¹ * (1 + 4 * Real.log (q : ℝ)) ^ 2 :=
    tsum_nonneg fun _ => by positivity
  linarith

theorem tsum_natCast_inv_sq_mul_four_log_profile_sq_le
    {A : ℝ} (hA : 1 ≤ A) :
    (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2) ≤
      A ^ 2 * hughesYoungEquation84LogProfileMass := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hleft := summable_natCast_inv_sq_mul_four_log_profile_sq A hA0
  have hright : Summable (fun q : ℕ =>
      A ^ 2 * (((q : ℝ) ^ 2)⁻¹ *
        (1 + 4 * Real.log (q : ℝ)) ^ 2)) :=
    summable_hughesYoungEquation84LogProfile.mul_left (A ^ 2)
  have hpoint (q : ℕ) :
      ((q : ℝ) ^ 2)⁻¹ * (A + 4 * Real.log (q : ℝ)) ^ 2 ≤
        A ^ 2 * (((q : ℝ) ^ 2)⁻¹ *
          (1 + 4 * Real.log (q : ℝ)) ^ 2) := by
    by_cases hq : q = 0
    · subst q
      norm_num
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
      have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
      have hprofile : A + 4 * Real.log (q : ℝ) ≤
          A * (1 + 4 * Real.log (q : ℝ)) := by
        nlinarith
      have hprofile0 : 0 ≤ A + 4 * Real.log (q : ℝ) := by positivity
      have honeProfile : 0 ≤ 1 + 4 * Real.log (q : ℝ) := by positivity
      calc
        ((q : ℝ) ^ 2)⁻¹ * (A + 4 * Real.log (q : ℝ)) ^ 2 ≤
            ((q : ℝ) ^ 2)⁻¹ *
              (A * (1 + 4 * Real.log (q : ℝ))) ^ 2 := by gcongr
        _ = A ^ 2 * (((q : ℝ) ^ 2)⁻¹ *
              (1 + 4 * Real.log (q : ℝ)) ^ 2) := by ring
  calc
    (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2) ≤
        ∑' q : ℕ, A ^ 2 * (((q : ℝ) ^ 2)⁻¹ *
          (1 + 4 * Real.log (q : ℝ)) ^ 2) :=
      hleft.tsum_le_tsum hpoint hright
    _ = A ^ 2 * (∑' q : ℕ,
        ((q : ℝ) ^ 2)⁻¹ * (1 + 4 * Real.log (q : ℝ)) ^ 2) := by
      rw [tsum_mul_left]
    _ ≤ A ^ 2 * hughesYoungEquation84LogProfileMass := by
      unfold hughesYoungEquation84LogProfileMass
      gcongr
      linarith

set_option maxHeartbeats 1000000 in
/-- Quantitative version of arithmetic-moment summability.  Its constant is
absolute; all dependence on the reduced moduli and the positive shift is
displayed. -/
theorem norm_hughesYoungEquation84PositiveArithmeticMoment_le
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (i j : Bool) :
    ‖hughesYoungEquation84PositiveArithmeticMoment a b r i j‖ ≤
      ((a * b * r ^ 2 : ℕ) : ℝ) *
        hughesYoungEquation84LogBudget a b r ^ 2 *
        hughesYoungEquation84LogProfileMass := by
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let X : ℕ → ℂ := fun q =>
    if i then hughesYoungEquation84PositiveCX b r q else 1
  let Y : ℕ → ℂ := fun q =>
    if j then hughesYoungEquation84PositiveCOne a r q else 1
  let K : ℝ := ((a * b * r ^ 2 : ℕ) : ℝ)
  have hA : 1 ≤ A := one_le_hughesYoungEquation84LogBudget a b r
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hX : ∀ q, 0 < q → ‖X q‖ ≤ A + 4 * Real.log (q : ℝ) := by
    intro q hq
    dsimp only [X, A]
    split
    · exact norm_hughesYoungEquation84PositiveCX_le_logBudget a b r q hq
    · simpa using one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq
  have hY : ∀ q, 0 < q → ‖Y q‖ ≤ A + 4 * Real.log (q : ℝ) := by
    intro q hq
    dsimp only [Y, A]
    split
    · exact norm_hughesYoungEquation84PositiveCOne_le_logBudget a b r q hq
    · simpa using one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq
  have hs : Summable (fun q : ℕ =>
      dfiEquation27ArithmeticCoefficient a b r q * X q * Y q) :=
    summable_dfiEquation27ArithmeticCoefficient_mul_two_logProfiles
      a b r ha hb hr X Y A hA hX hY
  have hnorm : ‖∑' q : ℕ,
      dfiEquation27ArithmeticCoefficient a b r q * X q * Y q‖ ≤
      ∑' q : ℕ, ‖dfiEquation27ArithmeticCoefficient a b r q * X q * Y q‖ :=
    norm_tsum_le_tsum_norm hs.norm
  have hmajor : ∀ q : ℕ,
      ‖dfiEquation27ArithmeticCoefficient a b r q * X q * Y q‖ ≤
        K * (((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) := by
    intro q
    by_cases hq0 : q = 0
    · subst q
      simp [dfiEquation27ArithmeticCoefficient]
    · have hq : 0 < q := Nat.pos_of_ne_zero hq0
      letI : NeZero q := ⟨hq0⟩
      have hCoeff :=
        norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
      simp only [norm_mul]
      calc
        ‖dfiEquation27ArithmeticCoefficient a b r q‖ * ‖X q‖ * ‖Y q‖ ≤
            (K * ((q : ℝ) ^ 2)⁻¹) *
              (A + 4 * Real.log (q : ℝ)) *
              (A + 4 * Real.log (q : ℝ)) := by
          gcongr
          · exact hX q hq
          · exact hY q hq
        _ = K * (((q : ℝ) ^ 2)⁻¹ *
              (A + 4 * Real.log (q : ℝ)) ^ 2) := by ring
  have hmajorSummable : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA0).mul_left K
  have hsumMajor :
      (∑' q : ℕ, ‖dfiEquation27ArithmeticCoefficient a b r q * X q * Y q‖) ≤
        ∑' q : ℕ, K * (((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) :=
    hs.norm.tsum_le_tsum hmajor hmajorSummable
  have hprofile := tsum_natCast_inv_sq_mul_four_log_profile_sq_le hA
  unfold hughesYoungEquation84PositiveArithmeticMoment
  change ‖∑' q : ℕ,
      dfiEquation27ArithmeticCoefficient a b r q * X q * Y q‖ ≤ _
  calc
    _ ≤ ∑' q : ℕ,
        ‖dfiEquation27ArithmeticCoefficient a b r q * X q * Y q‖ := hnorm
    _ ≤ ∑' q : ℕ, K * (((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) := hsumMajor
    _ = K * (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) := by rw [tsum_mul_left]
    _ ≤ K * (A ^ 2 * hughesYoungEquation84LogProfileMass) := by
      gcongr
    _ = ((a * b * r ^ 2 : ℕ) : ℝ) *
          hughesYoungEquation84LogBudget a b r ^ 2 *
          hughesYoungEquation84LogProfileMass := by
      dsimp only [K, A]
      ring

/-! ## Uniform control of the critical beta integral as the contour shrinks -/

/-- Near zero, the logarithmic singularity costs less than the fixed power
`x^(-1/8)`.  The deliberately generous constant keeps the later affine
two-logarithm estimate elementary. -/
theorem one_add_abs_log_le_seventeen_mul_rpow_neg_sixteenth
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    1 + |Real.log x| ≤ 17 * x ^ (-(1 / 16 : ℝ)) := by
  have hinv0 : 0 ≤ x⁻¹ := (inv_pos.mpr hx).le
  have hlog := Real.log_le_rpow_div hinv0
    (show (0 : ℝ) < 1 / 16 by norm_num)
  have hlogNonpos : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  have hpowOne : 1 ≤ x ^ (-(1 / 16 : ℝ)) := by
    rw [← Real.rpow_zero x]
    exact Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
  have hlogBound : |Real.log x| ≤ 16 * x ^ (-(1 / 16 : ℝ)) := by
    rw [Real.log_inv x] at hlog
    rw [abs_of_nonpos hlogNonpos]
    calc
      -Real.log x ≤ x⁻¹ ^ (1 / 16 : ℝ) / (1 / 16 : ℝ) := hlog
      _ = 16 * x ^ (-(1 / 16 : ℝ)) := by
        rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
        ring
  nlinarith

/-- On the large half-line, a logarithm is absorbed by half of the
available Mellin decay. -/
theorem one_add_log_le_three_mul_inv_mul_rpow_half
    {c x : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hx : 1 ≤ x) :
    1 + Real.log x ≤ 3 * c⁻¹ * x ^ (c / 2) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hhalf : 0 < c / 2 := by positivity
  have hlog := Real.log_le_rpow_div hx0 hhalf
  have hpow : 1 ≤ x ^ (c / 2) := Real.one_le_rpow hx (by positivity)
  have hcinv : 1 ≤ c⁻¹ := (one_le_inv₀ hc).mpr hc1
  have hone : 1 ≤ c⁻¹ * x ^ (c / 2) :=
    one_le_mul_of_one_le_of_one_le hcinv hpow
  have hlog' : Real.log x ≤ 2 * c⁻¹ * x ^ (c / 2) := by
    calc
      Real.log x ≤ x ^ (c / 2) / (c / 2) := hlog
      _ = 2 * c⁻¹ * x ^ (c / 2) := by
        field_simp [hc.ne']
  linarith

theorem log_one_add_le_one_add_log
    {x : ℝ} (hx : 1 ≤ x) :
    Real.log (1 + x) ≤ 1 + Real.log x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have htwoX : 1 + x ≤ 2 * x := by linarith
  have hlogMono : Real.log (1 + x) ≤ Real.log (2 * x) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa using add_pos zero_lt_one hx0)
      (by simpa using mul_pos (show (0 : ℝ) < 2 by norm_num) hx0) htwoX
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at hlogMono
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]

/-- The `hughesYoungCriticalAffineBetaIntegrand` definition used by the source-facing construction in `HughesYoungSmallContourQuantitative`. -/
noncomputable def hughesYoungCriticalAffineBetaIntegrand
    (t u c x : ℝ) (CX COne : ℂ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  ((Real.log x : ℂ) + CX) * ((Real.log (1 + x) : ℂ) + COne) *
    ((x : ℂ) ^ (-(afeCriticalPoint (-t) + w)) *
      (1 + (x : ℂ)) ^ (-(afeCriticalPoint t + w)))

theorem norm_hughesYoungCriticalAffineBetaPower_eq
    {t u c x : ℝ} (hx : 0 < x) :
    ‖((x : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) *
        (1 + (x : ℂ)) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))))‖ =
      x ^ (-(1 / 2 : ℝ) - c) * (1 + x) ^ (-(1 / 2 : ℝ) - c) := by
  have hone : 0 < 1 + x := by linarith
  rw [norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx,
    show 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hone]
  simp only [afeCriticalPoint, neg_re, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, I_im]
  congr 2 <;> norm_num <;> ring

theorem hughesYoungCriticalBetaPower_near_le
    {t u c x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hc0 : 0 ≤ c) (hc4 : c ≤ 1 / 4) :
    ‖((x : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) *
        (1 + (x : ℂ)) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))))‖ ≤
      x ^ (-(3 / 4 : ℝ)) := by
  rw [norm_hughesYoungCriticalAffineBetaPower_eq hx]
  have hfirst : x ^ (-(1 / 2 : ℝ) - c) ≤ x ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
  have hsecond : (1 + x) ^ (-(1 / 2 : ℝ) - c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  calc
    x ^ (-(1 / 2 : ℝ) - c) * (1 + x) ^ (-(1 / 2 : ℝ) - c) ≤
        x ^ (-(3 / 4 : ℝ)) * 1 := by
          exact mul_le_mul hfirst hsecond (Real.rpow_nonneg (by positivity) _)
            (Real.rpow_nonneg hx.le _)
    _ = x ^ (-(3 / 4 : ℝ)) := mul_one _

theorem hughesYoungCriticalBetaPower_tail_le
    {t u c x : ℝ} (hx : 1 ≤ x) (hc0 : 0 ≤ c) :
    ‖((x : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) *
        (1 + (x : ℂ)) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))))‖ ≤
      x ^ (-1 - 2 * c) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  rw [norm_hughesYoungCriticalAffineBetaPower_eq hx0]
  have he : -(1 / 2 : ℝ) - c ≤ 0 := by linarith
  have hsecond : (1 + x) ^ (-(1 / 2 : ℝ) - c) ≤
      x ^ (-(1 / 2 : ℝ) - c) := by
    exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) he
  calc
    x ^ (-(1 / 2 : ℝ) - c) * (1 + x) ^ (-(1 / 2 : ℝ) - c) ≤
        x ^ (-(1 / 2 : ℝ) - c) * x ^ (-(1 / 2 : ℝ) - c) :=
      mul_le_mul_of_nonneg_left hsecond (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-1 - 2 * c) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring

theorem norm_hughesYoungCriticalAffineBetaIntegrand_near_le
    {t u c x : ℝ} {CX COne : ℂ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hc0 : 0 ≤ c) (hc4 : c ≤ 1 / 4) :
    ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
      289 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * x ^ (-(7 / 8 : ℝ)) := by
  let S : ℝ := 1 + ‖CX‖ + ‖COne‖
  let P : ℝ := x ^ (-(1 / 16 : ℝ))
  have hS : 1 ≤ S := by
    dsimp only [S]
    linarith [norm_nonneg CX, norm_nonneg COne]
  have hP : 0 ≤ P := Real.rpow_nonneg hx.le _
  have hlogx0 : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  have hlogone0 : 0 ≤ Real.log (1 + x) :=
    Real.log_nonneg (by linarith)
  have hlogone1 : Real.log (1 + x) ≤ 1 := by
    calc
      Real.log (1 + x) ≤ x := by
        simpa only [add_sub_cancel_left] using
          Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
      _ ≤ 1 := hx1
  have hprofile := one_add_abs_log_le_seventeen_mul_rpow_neg_sixteenth hx hx1
  have hCXaff : ‖(Real.log x : ℂ) + CX‖ ≤ 17 * S * P := by
    calc
      _ ≤ |Real.log x| + ‖CX‖ := by
        have h := norm_add_le (Real.log x : ℂ) CX
        simpa only [norm_real] using h
      _ ≤ S * (1 + |Real.log x|) := by
        dsimp only [S]
        nlinarith [abs_nonneg (Real.log x), norm_nonneg CX, norm_nonneg COne]
      _ ≤ S * (17 * P) :=
        mul_le_mul_of_nonneg_left hprofile (zero_le_one.trans hS)
      _ = 17 * S * P := by ring
  have hOneAff : ‖(Real.log (1 + x) : ℂ) + COne‖ ≤ 17 * S * P := by
    calc
      _ ≤ Real.log (1 + x) + ‖COne‖ := by
        have h := norm_add_le (Real.log (1 + x) : ℂ) COne
        calc
          _ ≤ ‖(Real.log (1 + x) : ℂ)‖ + ‖COne‖ := h
          _ = Real.log (1 + x) + ‖COne‖ := by
            rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hlogone0]
      _ ≤ S * (1 + |Real.log x|) := by
        dsimp only [S]
        nlinarith [abs_nonneg (Real.log x), norm_nonneg CX, norm_nonneg COne]
      _ ≤ S * (17 * P) :=
        mul_le_mul_of_nonneg_left hprofile (zero_le_one.trans hS)
      _ = 17 * S * P := by ring
  have hbase := hughesYoungCriticalBetaPower_near_le
    (t := t) (u := u) hx hx1 hc0 hc4
  have hPP : P * P = x ^ (-(1 / 8 : ℝ)) := by
    dsimp only [P]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hcombine : x ^ (-(1 / 8 : ℝ)) * x ^ (-(3 / 4 : ℝ)) =
      x ^ (-(7 / 8 : ℝ)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  unfold hughesYoungCriticalAffineBetaIntegrand
  dsimp only
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (17 * S * P) * (17 * S * P) * x ^ (-(3 / 4 : ℝ)) := by
      gcongr
    _ = 289 * S ^ 2 * x ^ (-(7 / 8 : ℝ)) := by
      rw [show (17 * S * P) * (17 * S * P) * x ^ (-(3 / 4 : ℝ)) =
          289 * S ^ 2 * (P * P) * x ^ (-(3 / 4 : ℝ)) by ring,
        hPP]
      calc
        289 * S ^ 2 * x ^ (-(1 / 8 : ℝ)) * x ^ (-(3 / 4 : ℝ)) =
            289 * S ^ 2 *
              (x ^ (-(1 / 8 : ℝ)) * x ^ (-(3 / 4 : ℝ))) := by ring
        _ = 289 * S ^ 2 * x ^ (-(7 / 8 : ℝ)) := by rw [hcombine]
    _ = 289 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * x ^ (-(7 / 8 : ℝ)) := by
      rfl

theorem norm_hughesYoungCriticalAffineBetaIntegrand_tail_le
    {t u c x : ℝ} {CX COne : ℂ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hx : 1 ≤ x) :
    ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
      9 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * c⁻¹ ^ 2 *
        x ^ (-1 - c) := by
  let S : ℝ := 1 + ‖CX‖ + ‖COne‖
  let P : ℝ := x ^ (c / 2)
  have hS : 1 ≤ S := by
    dsimp only [S]
    linarith [norm_nonneg CX, norm_nonneg COne]
  have hP : 0 ≤ P := Real.rpow_nonneg (zero_le_one.trans hx) _
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogone0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hprofile := one_add_log_le_three_mul_inv_mul_rpow_half hc hc1 hx
  have hCXaff : ‖(Real.log x : ℂ) + CX‖ ≤ 3 * S * c⁻¹ * P := by
    calc
      _ ≤ Real.log x + ‖CX‖ := by
        have h := norm_add_le (Real.log x : ℂ) CX
        calc
          _ ≤ ‖(Real.log x : ℂ)‖ + ‖CX‖ := h
          _ = Real.log x + ‖CX‖ := by
            rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hlogx0]
      _ ≤ S * (1 + Real.log x) := by
        dsimp only [S]
        nlinarith [norm_nonneg CX, norm_nonneg COne]
      _ ≤ S * (3 * c⁻¹ * P) :=
        mul_le_mul_of_nonneg_left hprofile (zero_le_one.trans hS)
      _ = 3 * S * c⁻¹ * P := by ring
  have hOneAff : ‖(Real.log (1 + x) : ℂ) + COne‖ ≤
      3 * S * c⁻¹ * P := by
    calc
      _ ≤ Real.log (1 + x) + ‖COne‖ := by
        have h := norm_add_le (Real.log (1 + x) : ℂ) COne
        calc
          _ ≤ ‖(Real.log (1 + x) : ℂ)‖ + ‖COne‖ := h
          _ = Real.log (1 + x) + ‖COne‖ := by
            rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hlogone0]
      _ ≤ 1 + Real.log x + ‖COne‖ := by
        linarith [log_one_add_le_one_add_log hx]
      _ ≤ S * (1 + Real.log x) := by
        dsimp only [S]
        nlinarith [norm_nonneg CX, norm_nonneg COne]
      _ ≤ S * (3 * c⁻¹ * P) :=
        mul_le_mul_of_nonneg_left hprofile (zero_le_one.trans hS)
      _ = 3 * S * c⁻¹ * P := by ring
  have hbase := hughesYoungCriticalBetaPower_tail_le
    (t := t) (u := u) hx hc.le
  have hPP : P * P = x ^ c := by
    dsimp only [P]
    rw [← Real.rpow_add (zero_lt_one.trans_le hx)]
    congr 1
    ring
  have hcombine : x ^ c * x ^ (-1 - 2 * c) = x ^ (-1 - c) := by
    rw [← Real.rpow_add (zero_lt_one.trans_le hx)]
    congr 1
    ring
  unfold hughesYoungCriticalAffineBetaIntegrand
  dsimp only
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (3 * S * c⁻¹ * P) * (3 * S * c⁻¹ * P) *
          x ^ (-1 - 2 * c) := by gcongr
    _ = 9 * S ^ 2 * c⁻¹ ^ 2 * x ^ (-1 - c) := by
      rw [show (3 * S * c⁻¹ * P) * (3 * S * c⁻¹ * P) *
          x ^ (-1 - 2 * c) =
          9 * S ^ 2 * c⁻¹ ^ 2 * (P * P) * x ^ (-1 - 2 * c) by ring,
        hPP]
      calc
        9 * S ^ 2 * c⁻¹ ^ 2 * x ^ c * x ^ (-1 - 2 * c) =
            9 * S ^ 2 * c⁻¹ ^ 2 *
              (x ^ c * x ^ (-1 - 2 * c)) := by ring
        _ = 9 * S ^ 2 * c⁻¹ ^ 2 * x ^ (-1 - c) := by rw [hcombine]
    _ = 9 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * c⁻¹ ^ 2 *
          x ^ (-1 - c) := by rfl

/-- The `hughesYoungCriticalAffineBetaMajorant` definition used by the source-facing construction in `HughesYoungSmallContourQuantitative`. -/
noncomputable def hughesYoungCriticalAffineBetaMajorant
    (c S x : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator
      (fun y => 289 * S ^ 2 * y ^ (-(7 / 8 : ℝ))) x +
    (Set.Ioi (1 : ℝ)).indicator
      (fun y => 9 * S ^ 2 * c⁻¹ ^ 2 * y ^ (-1 - c)) x

theorem integrable_hughesYoungCriticalAffineBetaMajorant
    {c S : ℝ} (hc : 0 < c) :
    Integrable (hughesYoungCriticalAffineBetaMajorant c S) := by
  have hnearInterval : IntervalIntegrable
      (fun x : ℝ => x ^ (-(7 / 8 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hnear : IntegrableOn (fun x : ℝ =>
      289 * S ^ 2 * x ^ (-(7 / 8 : ℝ))) (Set.Ioc 0 1) := by
    have hraw : IntegrableOn (fun x : ℝ => x ^ (-(7 / 8 : ℝ)))
        (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        hnearInterval
    exact hraw.const_mul (289 * S ^ 2)
  have htail : IntegrableOn (fun x : ℝ =>
      9 * S ^ 2 * c⁻¹ ^ 2 * x ^ (-1 - c)) (Set.Ioi 1) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul
      (9 * S ^ 2 * c⁻¹ ^ 2)
  have hnearInd : Integrable ((Set.Ioc (0 : ℝ) 1).indicator
      (fun x : ℝ => 289 * S ^ 2 * x ^ (-(7 / 8 : ℝ)))) :=
    (integrable_indicator_iff measurableSet_Ioc).2 hnear
  have htailInd : Integrable ((Set.Ioi (1 : ℝ)).indicator
      (fun x : ℝ => 9 * S ^ 2 * c⁻¹ ^ 2 * x ^ (-1 - c))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 htail
  unfold hughesYoungCriticalAffineBetaMajorant
  exact hnearInd.add htailInd

theorem integral_hughesYoungCriticalAffineBetaMajorant_eq
    {c S : ℝ} (hc : 0 < c) :
    ∫ x : ℝ, hughesYoungCriticalAffineBetaMajorant c S x =
      2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 := by
  have hnearInterval : IntervalIntegrable
      (fun x : ℝ => x ^ (-(7 / 8 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hnear : IntegrableOn (fun x : ℝ =>
      289 * S ^ 2 * x ^ (-(7 / 8 : ℝ))) (Set.Ioc 0 1) := by
    have hraw : IntegrableOn (fun x : ℝ => x ^ (-(7 / 8 : ℝ)))
        (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        hnearInterval
    exact hraw.const_mul (289 * S ^ 2)
  have htail : IntegrableOn (fun x : ℝ =>
      9 * S ^ 2 * c⁻¹ ^ 2 * x ^ (-1 - c)) (Set.Ioi 1) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul
      (9 * S ^ 2 * c⁻¹ ^ 2)
  have hnearInd : Integrable ((Set.Ioc (0 : ℝ) 1).indicator
      (fun x : ℝ => 289 * S ^ 2 * x ^ (-(7 / 8 : ℝ)))) :=
    (integrable_indicator_iff measurableSet_Ioc).2 hnear
  have htailInd : Integrable ((Set.Ioi (1 : ℝ)).indicator
      (fun x : ℝ => 9 * S ^ 2 * c⁻¹ ^ 2 * x ^ (-1 - c))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 htail
  unfold hughesYoungCriticalAffineBetaMajorant
  rw [MeasureTheory.integral_add hnearInd htailInd]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioi]
  change (∫ x in Set.Ioc (0 : ℝ) 1,
      289 * S ^ 2 * x ^ (-(7 / 8 : ℝ))) +
    (∫ x in Set.Ioi (1 : ℝ),
      9 * S ^ 2 * c⁻¹ ^ 2 * x ^ (-1 - c)) = _
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [integral_rpow (Or.inl (by norm_num : (-(1 : ℝ)) < -(7 / 8 : ℝ)))]
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  have hcne : c ≠ 0 := hc.ne'
  norm_num [Real.zero_rpow]
  rw [show -1 - c + 1 = -c by ring]
  field_simp [hcne]
  ring

theorem norm_hughesYoungCriticalAffineBetaIntegrand_le_majorant
    {t u c x : ℝ} {CX COne : ℂ}
    (hc : 0 < c) (hc4 : c ≤ 1 / 4) (hx : 0 < x) :
    ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
      hughesYoungCriticalAffineBetaMajorant
        c (1 + ‖CX‖ + ‖COne‖) x := by
  by_cases hx1 : x ≤ 1
  · have hnear := norm_hughesYoungCriticalAffineBetaIntegrand_near_le
      (t := t) (u := u) (c := c) (CX := CX) (COne := COne)
      hx hx1 hc.le hc4
    simpa [hughesYoungCriticalAffineBetaMajorant, hx, hx1,
      not_lt_of_ge hx1] using hnear
  · have hx1' : 1 < x := lt_of_not_ge hx1
    have htail := norm_hughesYoungCriticalAffineBetaIntegrand_tail_le
      (t := t) (u := u) (c := c) (CX := CX) (COne := COne)
      hc (hc4.trans (by norm_num)) hx1'.le
    simpa [hughesYoungCriticalAffineBetaMajorant, hx, hx1',
      not_le_of_gt hx1'] using htail

theorem hughesYoungCriticalAffineBetaMajorant_nonneg
    {c S x : ℝ} : 0 ≤ hughesYoungCriticalAffineBetaMajorant c S x := by
  unfold hughesYoungCriticalAffineBetaMajorant
  apply add_nonneg
  · apply Set.indicator_nonneg
    intro y hy
    exact mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg S))
      (Real.rpow_nonneg hy.1.le _)
  · apply Set.indicator_nonneg
    intro y hy
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg S)) (sq_nonneg c⁻¹))
      (Real.rpow_nonneg (le_trans (by norm_num) hy.le) _)

/-- Uniform form of the equation-(84) beta estimate.  Unlike the earlier
fixed-`c` compactness statement, the constant here is absolute and the
entire contour dependence is the explicit factor `c⁻¹^3`. -/
theorem norm_hughesYoungAffineLogBetaContinuation_critical_le_inv_cube
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (t u : ℝ) (CX COne : ℂ) :
    ‖hughesYoungAffineLogBetaContinuation
        (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
        (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
        CX COne‖ ≤
      2321 * c⁻¹ ^ 3 * (1 + ‖CX‖ + ‖COne‖) ^ 2 := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let A : ℂ := -(afeCriticalPoint (-t) + w)
  let D : ℂ := -(afeCriticalPoint t + w)
  let S : ℝ := 1 + ‖CX‖ + ‖COne‖
  have hstrip := hughesYoungEquation83_exponents_in_betaStrip
    t u hc (hc4.trans_lt (by norm_num))
  have hA : 0 < (A + 1).re := by simpa only [A, w] using hstrip.1
  have hAD : (A + D + 1).re < 0 := by simpa only [A, D, w] using hstrip.2
  rw [← hughesYoungAffineLogBetaIntegral_eq_continuation hA hAD]
  change ‖∫ x in Set.Ioi (0 : ℝ),
      hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤ _
  have hmajorInt := integrable_hughesYoungCriticalAffineBetaMajorant
    (S := S) hc
  have hmajorOn : IntegrableOn
      (hughesYoungCriticalAffineBetaMajorant c S) (Set.Ioi (0 : ℝ)) :=
    hmajorInt.integrableOn
  have hpoint : ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
        hughesYoungCriticalAffineBetaMajorant c S x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_hughesYoungCriticalAffineBetaIntegrand_le_majorant
      hc hc4 hx
  have hnorm := norm_integral_le_of_norm_le hmajorOn hpoint
  have hrestrict :
      (∫ x in Set.Ioi (0 : ℝ), hughesYoungCriticalAffineBetaMajorant c S x) ≤
        ∫ x : ℝ, hughesYoungCriticalAffineBetaMajorant c S x :=
    MeasureTheory.setIntegral_le_integral hmajorInt
      (Filter.Eventually.of_forall fun x =>
        hughesYoungCriticalAffineBetaMajorant_nonneg)
  have hmass := integral_hughesYoungCriticalAffineBetaMajorant_eq
    (S := S) hc
  have hcinv : 1 ≤ c⁻¹ :=
    (one_le_inv₀ hc).mpr (hc4.trans (by norm_num))
  have hcinv3 : 1 ≤ c⁻¹ ^ 3 := by nlinarith [sq_nonneg c⁻¹]
  have hSsq : 0 ≤ S ^ 2 := sq_nonneg S
  calc
    _ ≤ ∫ x in Set.Ioi (0 : ℝ),
        hughesYoungCriticalAffineBetaMajorant c S x := hnorm
    _ ≤ ∫ x : ℝ, hughesYoungCriticalAffineBetaMajorant c S x := hrestrict
    _ = 2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 := hmass
    _ ≤ 2321 * c⁻¹ ^ 3 * S ^ 2 := by nlinarith
    _ = 2321 * c⁻¹ ^ 3 * (1 + ‖CX‖ + ‖COne‖) ^ 2 := by rfl

/-- The literal critical beta kernel in Hughes--Young equation (84) has an
absolute bound with all dependence on the moving contour displayed as
`c⁻¹ ^ 3`.  This is the uniform replacement for the fixed-contour
compactness estimate. -/
theorem norm_hughesYoungEquation84CriticalBetaKernel_low_le_inv_cube
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (t u : ℝ) (CX COne : ℂ) :
    ‖hughesYoungEquation84CriticalBetaKernel t
        ((c : ℂ) + (u : ℂ) * I) CX COne‖ ≤
      2321 * c⁻¹ ^ 3 * (1 + ‖CX‖ + ‖COne‖) ^ 2 := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hLeft : 0 < (afeCriticalPoint t - w).re := by
    dsimp only [w, afeCriticalPoint]
    simp
    linarith
  have hW : 0 < w.re := by simp [w, hc]
  have heq := hughesYoungAffineLogBetaContinuation_critical_eq_explicit
    (t := t) (w := w) (CX := CX) (COne := COne) hLeft hW
  have hbound :=
    norm_hughesYoungAffineLogBetaContinuation_critical_le_inv_cube
      hc hc4 t u CX COne
  change ‖hughesYoungAffineLogBetaContinuation
      (-(afeCriticalPoint (-t) + w))
      (-(afeCriticalPoint t + w)) CX COne‖ ≤ _ at hbound
  rw [heq] at hbound
  simpa only [w, hughesYoungEquation84CriticalBetaKernel] using hbound

/-- Uniform equation-(84) contour-kernel estimate on every moving line
`0 < c ≤ 1/4`.  The contour loss is explicit (`c⁻¹ ^ 4`), so the theorem
can be specialized to `c = 1 / log T` without choosing a height-dependent
compactness constant. -/
theorem exists_norm_hughesYoungEquation84RegularizedContourKernel_le_inv_four :
    ∃ C : ℝ, 0 < C ∧ ∀ {T t u c : ℝ}, 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 / 4 →
      ∀ (CX COne : ℂ),
      ‖hughesYoungEquation84RegularizedContourKernel t
          ((c : ℂ) + (u : ℂ) * I) CX COne‖ ≤
        2321 * (1 + ‖CX‖ + ‖COne‖) ^ 2 *
          (c⁻¹ ^ 4 * T ^ (4 * C * c) *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  refine ⟨C, hC, ?_⟩
  intro T t u c hT ht hc hc4 CX COne
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hc1 : c ≤ 1 := hc4.trans (by norm_num)
  have hz : 0 < (afeCriticalPoint t - w).re := by
    dsimp only [w, afeCriticalPoint]
    simp
    linarith
  have hproduct :=
    hughesYoungRightContourWeightComplex_mul_equation84_eq_regularized
      (t := t) (w := w) (CX := CX) (COne := COne) hz
  rw [← hproduct, norm_mul,
    hughesYoungRightContourWeightComplex_vertical]
  have hw := hweight T t u c hT ht hc hc1
  have hb :=
    norm_hughesYoungEquation84CriticalBetaKernel_low_le_inv_cube
      hc hc4 t u CX COne
  calc
    ‖hughesYoungRightContourWeight t c u‖ *
        ‖hughesYoungEquation84CriticalBetaKernel t w CX COne‖ ≤
      (c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8)) *
        (2321 * c⁻¹ ^ 3 * (1 + ‖CX‖ + ‖COne‖) ^ 2) := by
          gcongr
    _ = 2321 * (1 + ‖CX‖ + ‖COne‖) ^ 2 *
          (c⁻¹ ^ 4 * T ^ (4 * C * c) *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) := by ring

/-- Uniform finite-difference coefficient form of the preceding estimate.
The numerical factor `36` is the cost of recovering four bilinear
coefficients from the values at `(0,0)`, `(1,0)`, `(0,1)`, and `(1,1)`. -/
theorem exists_norm_hughesYoungEquation84KernelCoefficients_le_inv_four :
    ∃ C : ℝ, 0 < C ∧ ∀ {T t u c : ℝ}, 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 / 4 →
      let E := c⁻¹ ^ 4 * T ^ (4 * C * c) *
        (Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (6 * (|u| + 1))) *
          (25 + 8 * u ^ 2) ^ 8)
      ‖hughesYoungEquation84Kernel00 t ((c : ℂ) + (u : ℂ) * I)‖ ≤
          (36 * 2321) * E ∧
      ‖hughesYoungEquation84Kernel10 t ((c : ℂ) + (u : ℂ) * I)‖ ≤
          (36 * 2321) * E ∧
      ‖hughesYoungEquation84Kernel01 t ((c : ℂ) + (u : ℂ) * I)‖ ≤
          (36 * 2321) * E ∧
      ‖hughesYoungEquation84Kernel11 t ((c : ℂ) + (u : ℂ) * I)‖ ≤
          (36 * 2321) * E := by
  obtain ⟨C, hC, hkernel⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_le_inv_four
  refine ⟨C, hC, ?_⟩
  intro T t u c hT ht hc hc4
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let E : ℝ := c⁻¹ ^ 4 * T ^ (4 * C * c) *
    (Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have h00 :
      ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤
        2321 * E := by
    simpa only [w, E, norm_zero, add_zero, one_pow, mul_one] using
      hkernel hT ht hc hc4 (0 : ℂ) (0 : ℂ)
  have h10 :
      ‖hughesYoungEquation84RegularizedContourKernel t w 1 0‖ ≤
        (4 * 2321) * E := by
    have h := hkernel (u := u) hT ht hc hc4 (1 : ℂ) (0 : ℂ)
    norm_num at h ⊢
    exact h.trans_eq (by ring)
  have h01 :
      ‖hughesYoungEquation84RegularizedContourKernel t w 0 1‖ ≤
        (4 * 2321) * E := by
    have h := hkernel (u := u) hT ht hc hc4 (0 : ℂ) (1 : ℂ)
    norm_num at h ⊢
    exact h.trans_eq (by ring)
  have h11 :
      ‖hughesYoungEquation84RegularizedContourKernel t w 1 1‖ ≤
        (9 * 2321) * E := by
    have h := hkernel (u := u) hT ht hc hc4 (1 : ℂ) (1 : ℂ)
    norm_num at h ⊢
    exact h.trans_eq (by ring)
  dsimp only
  constructor
  · change ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤ _
    exact h00.trans <| mul_le_mul_of_nonneg_right (by norm_num) hE
  constructor
  · change ‖hughesYoungEquation84RegularizedContourKernel t w 1 0 -
        hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤ _
    calc
      _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t w 1 0‖ +
          ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ :=
        norm_sub_le _ _
      _ ≤ ((4 * 2321) + 2321) * E := by
        calc
          _ ≤ (4 * 2321) * E + 2321 * E := add_le_add h10 h00
          _ = _ := by ring
      _ ≤ (36 * 2321) * E :=
        mul_le_mul_of_nonneg_right (by norm_num) hE

  constructor
  · change ‖hughesYoungEquation84RegularizedContourKernel t w 0 1 -
        hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤ _
    calc
      _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t w 0 1‖ +
          ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ :=
        norm_sub_le _ _
      _ ≤ ((4 * 2321) + 2321) * E := by
        calc
          _ ≤ (4 * 2321) * E + 2321 * E := add_le_add h01 h00
          _ = _ := by ring
      _ ≤ (36 * 2321) * E :=
        mul_le_mul_of_nonneg_right (by norm_num) hE
  · change ‖hughesYoungEquation84RegularizedContourKernel t w 1 1 -
        (hughesYoungEquation84RegularizedContourKernel t w 1 0 -
          hughesYoungEquation84RegularizedContourKernel t w 0 0) -
        (hughesYoungEquation84RegularizedContourKernel t w 0 1 -
          hughesYoungEquation84RegularizedContourKernel t w 0 0) -
        hughesYoungEquation84RegularizedContourKernel t w 0 0‖ ≤ _
    rw [show
      hughesYoungEquation84RegularizedContourKernel t w 1 1 -
          (hughesYoungEquation84RegularizedContourKernel t w 1 0 -
            hughesYoungEquation84RegularizedContourKernel t w 0 0) -
          (hughesYoungEquation84RegularizedContourKernel t w 0 1 -
            hughesYoungEquation84RegularizedContourKernel t w 0 0) -
          hughesYoungEquation84RegularizedContourKernel t w 0 0 =
        (hughesYoungEquation84RegularizedContourKernel t w 1 1 -
            hughesYoungEquation84RegularizedContourKernel t w 1 0 -
            hughesYoungEquation84RegularizedContourKernel t w 0 1) +
          hughesYoungEquation84RegularizedContourKernel t w 0 0 by ring]
    calc
      _ ≤ (‖hughesYoungEquation84RegularizedContourKernel t w 1 1‖ +
            ‖hughesYoungEquation84RegularizedContourKernel t w 1 0‖ +
            ‖hughesYoungEquation84RegularizedContourKernel t w 0 1‖) +
          ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ := by
            calc
              _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t w 1 1 -
                    hughesYoungEquation84RegularizedContourKernel t w 1 0 -
                    hughesYoungEquation84RegularizedContourKernel t w 0 1‖ +
                  ‖hughesYoungEquation84RegularizedContourKernel t w 0 0‖ :=
                    norm_add_le _ _
              _ ≤ _ := by
                have hsub := norm_sub_le
                  (hughesYoungEquation84RegularizedContourKernel t w 1 1)
                  (hughesYoungEquation84RegularizedContourKernel t w 1 0)
                have hsub' := norm_sub_le
                  (hughesYoungEquation84RegularizedContourKernel t w 1 1 -
                    hughesYoungEquation84RegularizedContourKernel t w 1 0)
                  (hughesYoungEquation84RegularizedContourKernel t w 0 1)
                linarith
      _ ≤ ((9 * 2321) + (4 * 2321) + (4 * 2321) + 2321) * E := by
        calc
          _ ≤ ((9 * 2321) * E + (4 * 2321) * E + (4 * 2321) * E) +
              2321 * E := by gcongr
          _ = _ := by ring
      _ ≤ (36 * 2321) * E :=
        mul_le_mul_of_nonneg_right (by norm_num) hE

/-- On the native contour `c = 1 / log T`, the four equation-(84)
coefficients have one common Gaussian profile.  The only surviving height
growth is the explicit fourth power coming from the contour pole. -/
theorem exists_norm_hughesYoungEquation84KernelCoefficients_smallContour_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ {T t u : ℝ},
      Real.exp 4 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
      4 * C * hughesYoungSmallContour T ≤ 1 →
      let E := D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
        (1 + |u|) ^ 17
      ‖hughesYoungEquation84Kernel00 t
          ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤ E ∧
      ‖hughesYoungEquation84Kernel10 t
          ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤ E ∧
      ‖hughesYoungEquation84Kernel01 t
          ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤ E ∧
      ‖hughesYoungEquation84Kernel11 t
          ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤ E := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_le_inv_four
  let D₀ : ℝ := Real.exp (4 * C) * Real.exp 100 * 6 * 33 ^ 8
  let D : ℝ := (36 * 2321) * D₀
  have hD : 0 < D := by dsimp only [D, D₀]; positivity
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t u hT ht hcontour
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hTone : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hTone
  obtain ⟨hc, _hc1, hcinv⟩ := hughesYoungSmallContour_spec hT1
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hT
  have hlog0 : 0 < Real.log T := by linarith
  have hc4 : hughesYoungSmallContour T ≤ 1 / 4 := by
    unfold hughesYoungSmallContour
    rw [inv_le_iff_one_le_mul₀' hlog0]
    nlinarith
  rcases hcoeff (T := T) (t := t) (u := u)
      (c := hughesYoungSmallContour T) hTone ht hc hc4 with
    ⟨h00, h10, h01, h11⟩
  let c : ℝ := hughesYoungSmallContour T
  let A : ℝ := 6 * (|u| + 1)
  let Eraw : ℝ := c⁻¹ ^ 4 * T ^ (4 * C * c) *
    (Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 + 4 * C * c * Real.log A) *
      (25 + 8 * u ^ 2) ^ 8)
  have hA : 1 ≤ A := by dsimp only [A]; nlinarith [abs_nonneg u]
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hdcLog : 4 * C * c * Real.log A ≤ Real.log A := by
    exact mul_le_of_le_one_left hlogA hcontour
  have hcSq : c ^ 2 ≤ 1 := by
    have hc1 : c ≤ 1 := by dsimp only [c]; exact hc4.trans (by norm_num)
    have hc0 : 0 ≤ c := by dsimp only [c]; exact hc.le
    nlinarith
  have hExp : Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 + 4 * C * c * Real.log A) ≤
      Real.exp 100 * Real.exp (-84 * u ^ 2) * A := by
    have hinside :
        100 * c ^ 2 - 84 * u ^ 2 + 4 * C * c * Real.log A ≤
          100 + (-84 * u ^ 2) + Real.log A := by nlinarith
    calc
      _ ≤ Real.exp (100 + (-84 * u ^ 2) + Real.log A) :=
        Real.exp_le_exp.mpr hinside
      _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity : 0 < A)]
  have hpolyBase : 25 + 8 * u ^ 2 ≤ 33 * (1 + |u|) ^ 2 := by
    rw [show u ^ 2 = |u| ^ 2 by exact (sq_abs u).symm]
    nlinarith [abs_nonneg u, sq_nonneg |u|]
  have hpoly : (25 + 8 * u ^ 2) ^ 8 ≤
      33 ^ 8 * (1 + |u|) ^ 16 := by
    calc
      _ ≤ (33 * (1 + |u|) ^ 2) ^ 8 := by gcongr
      _ = 33 ^ 8 * (1 + |u|) ^ 16 := by ring
  have hlogT : Real.log T ≤ T := Real.log_le_self hT0.le
  have hlogPow : (Real.log T) ^ 4 ≤ T ^ (4 : ℕ) :=
    pow_le_pow_left₀ (Real.log_nonneg hTone) hlogT 4
  have hrpow : T ^ (4 * C * c) = Real.exp (4 * C) := by
    dsimp only [c]
    exact rpow_smallContour_four_mul_eq C hT1
  have hraw : Eraw ≤ D₀ * T ^ (4 : ℕ) *
      Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17 := by
    dsimp only [Eraw]
    rw [hcinv, hrpow]
    calc
      Real.log T ^ 4 * Real.exp (4 * C) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 + 4 * C * c * Real.log A) *
            (25 + 8 * u ^ 2) ^ 8) ≤
        T ^ (4 : ℕ) * Real.exp (4 * C) *
          ((Real.exp 100 * Real.exp (-84 * u ^ 2) * A) *
            (33 ^ 8 * (1 + |u|) ^ 16)) := by gcongr
      _ = D₀ * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
          (1 + |u|) ^ 17 := by
        dsimp only [D₀, A]
        ring
  let E : ℝ := D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
    (1 + |u|) ^ 17
  change ‖hughesYoungEquation84Kernel00 t
      ((c : ℂ) + (u : ℂ) * I)‖ ≤ (36 * 2321) * Eraw at h00
  change ‖hughesYoungEquation84Kernel10 t
      ((c : ℂ) + (u : ℂ) * I)‖ ≤ (36 * 2321) * Eraw at h10
  change ‖hughesYoungEquation84Kernel01 t
      ((c : ℂ) + (u : ℂ) * I)‖ ≤ (36 * 2321) * Eraw at h01
  change ‖hughesYoungEquation84Kernel11 t
      ((c : ℂ) + (u : ℂ) * I)‖ ≤ (36 * 2321) * Eraw at h11
  have hscaled : (36 * 2321 : ℝ) * Eraw ≤ E := by
    dsimp only [E, D]
    nlinarith [hraw]
  dsimp only
  exact ⟨h00.trans hscaled, h10.trans hscaled,
    h01.trans hscaled, h11.trans hscaled⟩

/-- Scalar form of the native moving-contour simplification.  It is kept
separate so the exact positive and negative equation-(84) series estimates
can reuse the same analytic calculation. -/
theorem hughesYoungEquation84MovingEnvelope_smallContour_le
    {C T u : ℝ} (hT : Real.exp 4 ≤ T)
    (hcontour : 4 * C * hughesYoungSmallContour T ≤ 1) :
    (hughesYoungSmallContour T)⁻¹ ^ 4 *
        T ^ (4 * C * hughesYoungSmallContour T) *
      (Real.exp
        (100 * hughesYoungSmallContour T ^ 2 - 84 * u ^ 2 +
          4 * C * hughesYoungSmallContour T *
            Real.log (6 * (|u| + 1))) *
        (25 + 8 * u ^ 2) ^ 8) ≤
      (Real.exp (4 * C) * Real.exp 100 * 6 * 33 ^ 8) *
        T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17 := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hTone : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hTone
  obtain ⟨hc, hc1, hcinv⟩ := hughesYoungSmallContour_spec hT1
  let c : ℝ := hughesYoungSmallContour T
  let A : ℝ := 6 * (|u| + 1)
  have hA : 1 ≤ A := by dsimp only [A]; nlinarith [abs_nonneg u]
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hdcLog : 4 * C * c * Real.log A ≤ Real.log A := by
    exact mul_le_of_le_one_left hlogA hcontour
  have hcSq : c ^ 2 ≤ 1 := by
    have hc0 : 0 ≤ c := by dsimp only [c]; exact hc.le
    have hcOne : c ≤ 1 := by dsimp only [c]; exact hc1
    nlinarith
  have hExp : Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 + 4 * C * c * Real.log A) ≤
      Real.exp 100 * Real.exp (-84 * u ^ 2) * A := by
    have hinside :
        100 * c ^ 2 - 84 * u ^ 2 + 4 * C * c * Real.log A ≤
          100 + (-84 * u ^ 2) + Real.log A := by nlinarith
    calc
      _ ≤ Real.exp (100 + (-84 * u ^ 2) + Real.log A) :=
        Real.exp_le_exp.mpr hinside
      _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity : 0 < A)]
  have hpolyBase : 25 + 8 * u ^ 2 ≤ 33 * (1 + |u|) ^ 2 := by
    rw [show u ^ 2 = |u| ^ 2 by exact (sq_abs u).symm]
    nlinarith [abs_nonneg u, sq_nonneg |u|]
  have hpoly : (25 + 8 * u ^ 2) ^ 8 ≤
      33 ^ 8 * (1 + |u|) ^ 16 := by
    calc
      _ ≤ (33 * (1 + |u|) ^ 2) ^ 8 := by gcongr
      _ = 33 ^ 8 * (1 + |u|) ^ 16 := by ring
  have hlogT : Real.log T ≤ T := Real.log_le_self hT0.le
  have hlogPow : (Real.log T) ^ 4 ≤ T ^ (4 : ℕ) :=
    pow_le_pow_left₀ (Real.log_nonneg hTone) hlogT 4
  have hrpow : T ^ (4 * C * c) = Real.exp (4 * C) := by
    dsimp only [c]
    exact rpow_smallContour_four_mul_eq C hT1
  change c⁻¹ ^ 4 * T ^ (4 * C * c) *
      (Real.exp (100 * c ^ 2 - 84 * u ^ 2 + 4 * C * c * Real.log A) *
        (25 + 8 * u ^ 2) ^ 8) ≤ _
  rw [hcinv, hrpow]
  calc
    Real.log T ^ 4 * Real.exp (4 * C) *
        (Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 + 4 * C * c * Real.log A) *
          (25 + 8 * u ^ 2) ^ 8) ≤
      T ^ (4 : ℕ) * Real.exp (4 * C) *
        ((Real.exp 100 * Real.exp (-84 * u ^ 2) * A) *
          (33 ^ 8 * (1 + |u|) ^ 16)) := by gcongr
    _ = (Real.exp (4 * C) * Real.exp 100 * 6 * 33 ^ 8) *
        T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17 := by
      dsimp only [A]
      ring

/-- Exact norm of the positive equation-(84) outer factor on a moving
small contour.  This keeps the shift power visible for the subsequent
finite-window summation. -/
theorem norm_hughesYoungEquation84PositiveOuter_reduced_eq
    {h k r : ℕ} (hh : 0 < h) (hk : 0 < k) (hr : 0 < r)
    (T t c u : ℝ) :
    ‖hughesYoungEquation84PositiveOuter T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        ((c : ℂ) + (u : ℂ) * I)‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
        (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2) *
        (r : ℝ) ^ (-2 * c) := by
  have hstatic :=
    norm_inv_reduced_mul_hughesYoungReducedMellinStaticComplex_eq
      hh hk T t c u
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hshift :
      ‖hughesYoungCentralShiftPower r ((c : ℂ) + (u : ℂ) * I)‖ =
        (r : ℝ) ^ (-2 * c) := by
    rw [hughesYoungCentralShiftPower_eq_cpow hr,
      ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hrR]
    congr 1
    simp
  unfold hughesYoungEquation84PositiveOuter
  simp only [norm_mul]
  rw [hshift]
  calc
    ‖((hughesYoungReducedLeft h k : ℂ) *
          (hughesYoungReducedRight h k : ℂ))⁻¹‖ *
        (‖hughesYoungReducedMellinStaticComplex T t h k
            ((c : ℂ) + (u : ℂ) * I)‖ * (r : ℝ) ^ (-2 * c)) =
      ‖(((hughesYoungReducedLeft h k : ℕ) : ℂ) *
          (hughesYoungReducedRight h k : ℕ))⁻¹ *
        hughesYoungReducedMellinStaticComplex T t h k
          ((c : ℂ) + (u : ℂ) * I)‖ * (r : ℝ) ^ (-2 * c) := by
            rw [norm_mul]
            ring
    _ = _ := congrArg (fun x : ℝ => x * (r : ℝ) ^ (-2 * c)) hstatic

/-- The negative equation-(84) outer factor has the same norm after the
coprime reduced variables are exchanged. -/
theorem norm_hughesYoungEquation84NegativeOuter_reduced_eq
    {h k r : ℕ} (hh : 0 < h) (hk : 0 < k) (hr : 0 < r)
    (T t c u : ℝ) :
    ‖hughesYoungEquation84NegativeOuter T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        ((c : ℂ) + (u : ℂ) * I)‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
        (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2) *
        (r : ℝ) ^ (-2 * c) := by
  rw [show hughesYoungEquation84NegativeOuter T t h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        ((c : ℂ) + (u : ℂ) * I) =
      hughesYoungEquation84PositiveOuter T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
          ((c : ℂ) + (u : ℂ) * I) by
    unfold hughesYoungEquation84NegativeOuter
      hughesYoungEquation84PositiveOuter
    ring]
  exact norm_hughesYoungEquation84PositiveOuter_reduced_eq
    hh hk hr T t c u

/-- Pointwise moving-contour estimate for the literal positive modulus
series in equation (84), with every arithmetic and contour factor shown. -/
theorem exists_norm_hughesYoungEquation84PositiveContourSeries_le_movingMajorant :
    ∃ C : ℝ, 0 < C ∧ ∀ {T t u c : ℝ} {h k r : ℕ},
      1 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
      0 < c → c ≤ 1 / 4 → 0 < h → 0 < k → 0 < r →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      let E := c⁻¹ ^ 4 * T ^ (4 * C * c) *
        (Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (6 * (|u| + 1))) *
          (25 + 8 * u ^ 2) ^ 8)
      ‖hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((c : ℂ) + (u : ℂ) * I)‖ ≤
        (‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2) *
          (r : ℝ) ^ (-2 * c)) *
        (4 * (((a * b * r ^ 2 : ℕ) : ℝ) *
          hughesYoungEquation84LogBudget a b r ^ 2 *
          hughesYoungEquation84LogProfileMass) * ((36 * 2321) * E)) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_le_inv_four
  refine ⟨C, hC, ?_⟩
  intro T t u c h k r hT ht hc hc4 hh hk hr
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let E := c⁻¹ ^ 4 * T ^ (4 * C * c) *
    (Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)
  let M := ((a * b * r ^ 2 : ℕ) : ℝ) *
    hughesYoungEquation84LogBudget a b r ^ 2 *
    hughesYoungEquation84LogProfileMass
  let D := (36 * 2321 : ℝ) * E
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  rcases hcoeff hT ht hc hc4 with ⟨hk00, hk10, hk01, hk11⟩
  change ‖hughesYoungEquation84Kernel00 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ D at hk00
  change ‖hughesYoungEquation84Kernel10 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ D at hk10
  change ‖hughesYoungEquation84Kernel01 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ D at hk01
  change ‖hughesYoungEquation84Kernel11 t ((c : ℂ) + (u : ℂ) * I)‖ ≤ D at hk11
  have hm00 := norm_hughesYoungEquation84PositiveArithmeticMoment_le
    ha hb hr false false
  have hm10 := norm_hughesYoungEquation84PositiveArithmeticMoment_le
    ha hb hr true false
  have hm01 := norm_hughesYoungEquation84PositiveArithmeticMoment_le
    ha hb hr false true
  have hm11 := norm_hughesYoungEquation84PositiveArithmeticMoment_le
    ha hb hr true true
  change ‖hughesYoungEquation84PositiveArithmeticMoment a b r false false‖ ≤ M at hm00
  change ‖hughesYoungEquation84PositiveArithmeticMoment a b r true false‖ ≤ M at hm10
  change ‖hughesYoungEquation84PositiveArithmeticMoment a b r false true‖ ≤ M at hm01
  change ‖hughesYoungEquation84PositiveArithmeticMoment a b r true true‖ ≤ M at hm11
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      hughesYoungEquation84LogProfileMass_pos.le
  have hD : 0 ≤ D := by dsimp only [D, E]; positivity
  dsimp only
  rw [hughesYoungEquation84PositiveContourSeries_eq_fourMoments
    T t h k a b r ha hb hr, norm_mul]
  rw [norm_hughesYoungEquation84PositiveOuter_reduced_eq
    hh hk hr T t c u]
  have hinside :
      ‖hughesYoungEquation84PositiveArithmeticMoment a b r false false *
            hughesYoungEquation84Kernel00 t ((c : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment a b r true false *
            hughesYoungEquation84Kernel10 t ((c : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment a b r false true *
            hughesYoungEquation84Kernel01 t ((c : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment a b r true true *
            hughesYoungEquation84Kernel11 t ((c : ℂ) + (u : ℂ) * I)‖ ≤
        4 * M * D := by
    calc
      _ ≤ ‖hughesYoungEquation84PositiveArithmeticMoment a b r false false‖ *
              ‖hughesYoungEquation84Kernel00 t ((c : ℂ) + (u : ℂ) * I)‖ +
            ‖hughesYoungEquation84PositiveArithmeticMoment a b r true false‖ *
              ‖hughesYoungEquation84Kernel10 t ((c : ℂ) + (u : ℂ) * I)‖ +
            ‖hughesYoungEquation84PositiveArithmeticMoment a b r false true‖ *
              ‖hughesYoungEquation84Kernel01 t ((c : ℂ) + (u : ℂ) * I)‖ +
            ‖hughesYoungEquation84PositiveArithmeticMoment a b r true true‖ *
              ‖hughesYoungEquation84Kernel11 t ((c : ℂ) + (u : ℂ) * I)‖ := by
          calc
            _ ≤ ‖_ + _ + _‖ + ‖_‖ := norm_add_le _ _
            _ ≤ (‖_ + _‖ + ‖_‖) + ‖_‖ := by
              gcongr
              exact norm_add_le _ _
            _ ≤ ((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖ := by
              gcongr
              exact norm_add_le _ _
            _ = _ := by simp only [norm_mul]
      _ ≤ M * D + M * D + M * D + M * D := by gcongr
      _ = 4 * M * D := by ring
  exact mul_le_mul_of_nonneg_left hinside (by positivity)

/-- Coordinate-swapped negative companion of the moving-contour modulus
series estimate. -/
theorem exists_norm_hughesYoungEquation84NegativeContourSeries_le_movingMajorant :
    ∃ C : ℝ, 0 < C ∧ ∀ {T t u c : ℝ} {h k r : ℕ},
      1 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
      0 < c → c ≤ 1 / 4 → 0 < h → 0 < k → 0 < r →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      let E := c⁻¹ ^ 4 * T ^ (4 * C * c) *
        (Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (6 * (|u| + 1))) *
          (25 + 8 * u ^ 2) ^ 8)
      ‖hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((c : ℂ) + (u : ℂ) * I)‖ ≤
        (‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2) *
          (r : ℝ) ^ (-2 * c)) *
        (4 * (((b * a * r ^ 2 : ℕ) : ℝ) *
          hughesYoungEquation84LogBudget b a r ^ 2 *
          hughesYoungEquation84LogProfileMass) * ((36 * 2321) * E)) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_le_inv_four
  refine ⟨C, hC, ?_⟩
  intro T t u c h k r hT ht hc hc4 hh hk hr
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let E := c⁻¹ ^ 4 * T ^ (4 * C * c) *
    (Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)
  let M := ((b * a * r ^ 2 : ℕ) : ℝ) *
    hughesYoungEquation84LogBudget b a r ^ 2 *
    hughesYoungEquation84LogProfileMass
  let D := (36 * 2321 : ℝ) * E
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have htneg : |-t| ∈ Set.Icc (T / 4) (4 * T) := by simpa using ht
  rcases hcoeff hT htneg hc hc4 with ⟨hk00, hk10, hk01, hk11⟩
  change ‖hughesYoungEquation84Kernel00 (-t) ((c : ℂ) + (u : ℂ) * I)‖ ≤ D at hk00
  change ‖hughesYoungEquation84Kernel10 (-t) ((c : ℂ) + (u : ℂ) * I)‖ ≤ D at hk10
  change ‖hughesYoungEquation84Kernel01 (-t) ((c : ℂ) + (u : ℂ) * I)‖ ≤ D at hk01
  change ‖hughesYoungEquation84Kernel11 (-t) ((c : ℂ) + (u : ℂ) * I)‖ ≤ D at hk11
  have hm00 := norm_hughesYoungEquation84PositiveArithmeticMoment_le
    hb ha hr false false
  have hm10 := norm_hughesYoungEquation84PositiveArithmeticMoment_le
    hb ha hr true false
  have hm01 := norm_hughesYoungEquation84PositiveArithmeticMoment_le
    hb ha hr false true
  have hm11 := norm_hughesYoungEquation84PositiveArithmeticMoment_le
    hb ha hr true true
  change ‖hughesYoungEquation84PositiveArithmeticMoment b a r false false‖ ≤ M at hm00
  change ‖hughesYoungEquation84PositiveArithmeticMoment b a r true false‖ ≤ M at hm10
  change ‖hughesYoungEquation84PositiveArithmeticMoment b a r false true‖ ≤ M at hm01
  change ‖hughesYoungEquation84PositiveArithmeticMoment b a r true true‖ ≤ M at hm11
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      hughesYoungEquation84LogProfileMass_pos.le
  have hD : 0 ≤ D := by dsimp only [D, E]; positivity
  dsimp only
  rw [hughesYoungEquation84NegativeContourSeries_eq_fourMoments
    T t h k a b r ha hb hr, norm_mul]
  rw [norm_hughesYoungEquation84NegativeOuter_reduced_eq
    hh hk hr T t c u]
  have hinside :
      ‖hughesYoungEquation84PositiveArithmeticMoment b a r false false *
            hughesYoungEquation84Kernel00 (-t) ((c : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment b a r true false *
            hughesYoungEquation84Kernel10 (-t) ((c : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment b a r false true *
            hughesYoungEquation84Kernel01 (-t) ((c : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment b a r true true *
            hughesYoungEquation84Kernel11 (-t) ((c : ℂ) + (u : ℂ) * I)‖ ≤
        4 * M * D := by
    calc
      _ ≤ ‖hughesYoungEquation84PositiveArithmeticMoment b a r false false‖ *
              ‖hughesYoungEquation84Kernel00 (-t) ((c : ℂ) + (u : ℂ) * I)‖ +
            ‖hughesYoungEquation84PositiveArithmeticMoment b a r true false‖ *
              ‖hughesYoungEquation84Kernel10 (-t) ((c : ℂ) + (u : ℂ) * I)‖ +
            ‖hughesYoungEquation84PositiveArithmeticMoment b a r false true‖ *
              ‖hughesYoungEquation84Kernel01 (-t) ((c : ℂ) + (u : ℂ) * I)‖ +
            ‖hughesYoungEquation84PositiveArithmeticMoment b a r true true‖ *
              ‖hughesYoungEquation84Kernel11 (-t) ((c : ℂ) + (u : ℂ) * I)‖ := by
          calc
            _ ≤ ‖_ + _ + _‖ + ‖_‖ := norm_add_le _ _
            _ ≤ (‖_ + _‖ + ‖_‖) + ‖_‖ := by
              gcongr
              exact norm_add_le _ _
            _ ≤ ((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖ := by
              gcongr
              exact norm_add_le _ _
            _ = _ := by simp only [norm_mul]
      _ ≤ M * D + M * D + M * D + M * D := by gcongr
      _ = 4 * M * D := by ring
  exact mul_le_mul_of_nonneg_left hinside (by positivity)

/-- Native-contour specialization of the positive equation-(84) series.
The arithmetic coefficient is unchanged; all Mellin-ordinate dependence is
now carried by the fixed Gaussian profile. -/
theorem exists_norm_hughesYoungEquation84PositiveContourSeries_smallContour_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ {T t u : ℝ} {h k r : ℕ},
      Real.exp 4 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
      4 * C * hughesYoungSmallContour T ≤ 1 →
      0 < h → 0 < k → 0 < r →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤
        (‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (r : ℝ) ^ (-2 * hughesYoungSmallContour T)) *
        (4 * ((((a * b * r ^ 2 : ℕ) : ℝ) *
          hughesYoungEquation84LogBudget a b r ^ 2 *
          hughesYoungEquation84LogProfileMass) *
          (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
            (1 + |u|) ^ 17))) := by
  obtain ⟨C, hC, hseries⟩ :=
    exists_norm_hughesYoungEquation84PositiveContourSeries_le_movingMajorant
  let D₀ : ℝ := Real.exp (4 * C) * Real.exp 100 * 6 * 33 ^ 8
  let D : ℝ := (36 * 2321) * D₀
  have hD : 0 < D := by dsimp only [D, D₀]; positivity
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t u h k r hT ht hcontour hh hk hr
  have hT1 : 1 ≤ T := by
    have hExpOne : 1 ≤ Real.exp 4 := by
      calc
        1 = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
    exact hExpOne.trans hT
  have hc := hughesYoungSmallContour_spec
    ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hT
  have hc4 : hughesYoungSmallContour T ≤ 1 / 4 := by
    unfold hughesYoungSmallContour
    have hlog0 : 0 < Real.log T := by linarith
    rw [inv_le_iff_one_le_mul₀' hlog0]
    nlinarith
  have hraw := hseries (T := T) (t := t) (u := u)
    (c := hughesYoungSmallContour T) (h := h) (k := k) (r := r)
    hT1 ht hc.1 hc4 hh hk hr
  have henv := hughesYoungEquation84MovingEnvelope_smallContour_le
    (C := C) (T := T) (u := u) hT hcontour
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let M : ℝ := ((a * b * r ^ 2 : ℕ) : ℝ) *
    hughesYoungEquation84LogBudget a b r ^ 2 *
    hughesYoungEquation84LogProfileMass
  let Eraw : ℝ := (hughesYoungSmallContour T)⁻¹ ^ 4 *
    T ^ (4 * C * hughesYoungSmallContour T) *
    (Real.exp
      (100 * hughesYoungSmallContour T ^ 2 - 84 * u ^ 2 +
        4 * C * hughesYoungSmallContour T * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)
  let E : ℝ := D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
    (1 + |u|) ^ 17
  change Eraw ≤ D₀ * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
    (1 + |u|) ^ 17 at henv
  have hscaled : (36 * 2321 : ℝ) * Eraw ≤ E := by
    dsimp only [E, D]
    nlinarith [henv]
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      hughesYoungEquation84LogProfileMass_pos.le
  have hraw' :
      ‖hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤
        (‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (r : ℝ) ^ (-2 * hughesYoungSmallContour T)) *
          (4 * (M * ((36 * 2321) * Eraw))) := by
    simpa only [a, b, M, Eraw, mul_assoc] using hraw
  dsimp only [a, b] at hraw' ⊢
  change ‖hughesYoungEquation84PositiveContourSeries T t h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
      ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤
    (‖hughesYoungLocalizedStaticScalar T h k‖ *
      (hughesYoungReducedLeft h k : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
      (hughesYoungReducedRight h k : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
      (r : ℝ) ^ (-2 * hughesYoungSmallContour T)) * (4 * (M * E))
  exact hraw'.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hscaled hM) (by norm_num))
    (by positivity))

/-- Coordinate-swapped negative companion of the native-contour series
bound. -/
theorem exists_norm_hughesYoungEquation84NegativeContourSeries_smallContour_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ {T t u : ℝ} {h k r : ℕ},
      Real.exp 4 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
      4 * C * hughesYoungSmallContour T ≤ 1 →
      0 < h → 0 < k → 0 < r →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤
        (‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (r : ℝ) ^ (-2 * hughesYoungSmallContour T)) *
        (4 * ((((b * a * r ^ 2 : ℕ) : ℝ) *
          hughesYoungEquation84LogBudget b a r ^ 2 *
          hughesYoungEquation84LogProfileMass) *
          (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
            (1 + |u|) ^ 17))) := by
  obtain ⟨C, hC, hseries⟩ :=
    exists_norm_hughesYoungEquation84NegativeContourSeries_le_movingMajorant
  let D₀ : ℝ := Real.exp (4 * C) * Real.exp 100 * 6 * 33 ^ 8
  let D : ℝ := (36 * 2321) * D₀
  have hD : 0 < D := by dsimp only [D, D₀]; positivity
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t u h k r hT ht hcontour hh hk hr
  have hT1 : 1 ≤ T := by
    have hExpOne : 1 ≤ Real.exp 4 := by
      calc
        1 = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
    exact hExpOne.trans hT
  have hc := hughesYoungSmallContour_spec
    ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hT
  have hc4 : hughesYoungSmallContour T ≤ 1 / 4 := by
    unfold hughesYoungSmallContour
    have hlog0 : 0 < Real.log T := by linarith
    rw [inv_le_iff_one_le_mul₀' hlog0]
    nlinarith
  have hraw := hseries (T := T) (t := t) (u := u)
    (c := hughesYoungSmallContour T) (h := h) (k := k) (r := r)
    hT1 ht hc.1 hc4 hh hk hr
  have henv := hughesYoungEquation84MovingEnvelope_smallContour_le
    (C := C) (T := T) (u := u) hT hcontour
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let M : ℝ := ((b * a * r ^ 2 : ℕ) : ℝ) *
    hughesYoungEquation84LogBudget b a r ^ 2 *
    hughesYoungEquation84LogProfileMass
  let Eraw : ℝ := (hughesYoungSmallContour T)⁻¹ ^ 4 *
    T ^ (4 * C * hughesYoungSmallContour T) *
    (Real.exp
      (100 * hughesYoungSmallContour T ^ 2 - 84 * u ^ 2 +
        4 * C * hughesYoungSmallContour T * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)
  let E : ℝ := D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
    (1 + |u|) ^ 17
  change Eraw ≤ D₀ * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
    (1 + |u|) ^ 17 at henv
  have hscaled : (36 * 2321 : ℝ) * Eraw ≤ E := by
    dsimp only [E, D]
    nlinarith [henv]
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      hughesYoungEquation84LogProfileMass_pos.le
  have hraw' :
      ‖hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤
        (‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (r : ℝ) ^ (-2 * hughesYoungSmallContour T)) *
          (4 * (M * ((36 * 2321) * Eraw))) := by
    simpa only [a, b, M, Eraw, mul_assoc] using hraw
  dsimp only [a, b] at hraw' ⊢
  change ‖hughesYoungEquation84NegativeContourSeries T t h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
      ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤
    (‖hughesYoungLocalizedStaticScalar T h k‖ *
      (hughesYoungReducedLeft h k : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
      (hughesYoungReducedRight h k : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
      (r : ℝ) ^ (-2 * hughesYoungSmallContour T)) * (4 * (M * E))
  exact hraw'.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hscaled hM) (by norm_num))
    (by positivity))

/-- Explicit arithmetic coefficient of one nonzero signed shift in the
native small-contour tail.  It contains no Mellin-ordinate dependence. -/
noncomputable def hughesYoungSmallContourSignedShiftCoefficient
    (T : ℝ) (h k : ℕ) (r : ℤ) : ℝ :=
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let c := hughesYoungSmallContour T
  if r = 0 then 0
  else if 0 ≤ r then
    (‖hughesYoungLocalizedStaticScalar T h k‖ *
      (a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2) *
      (r.toNat : ℝ) ^ (-2 * c)) *
      (4 * (((a * b * r.toNat ^ 2 : ℕ) : ℝ) *
        hughesYoungEquation84LogBudget a b r.toNat ^ 2 *
        hughesYoungEquation84LogProfileMass))
  else
    (‖hughesYoungLocalizedStaticScalar T h k‖ *
      (a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2) *
      ((-r).toNat : ℝ) ^ (-2 * c)) *
      (4 * (((b * a * (-r).toNat ^ 2 : ℕ) : ℝ) *
        hughesYoungEquation84LogBudget b a (-r).toNat ^ 2 *
        hughesYoungEquation84LogProfileMass))

theorem hughesYoungSmallContourSignedShiftCoefficient_nonneg
    (T : ℝ) (h k : ℕ) (r : ℤ) :
    0 ≤ hughesYoungSmallContourSignedShiftCoefficient T h k r := by
  unfold hughesYoungSmallContourSignedShiftCoefficient
  split_ifs with hr hsign
  · positivity
  · have hrpos : 0 < r := lt_of_le_of_ne hsign (Ne.symm hr)
    have hto : 0 < r.toNat := by omega
    have hbudget : 0 < hughesYoungEquation84LogBudget
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        r.toNat :=
      lt_of_lt_of_le zero_lt_one (one_le_hughesYoungEquation84LogBudget _ _ _)
    have hmass : 0 < hughesYoungEquation84LogProfileMass :=
      hughesYoungEquation84LogProfileMass_pos
    positivity
  · have hrneg : r < 0 := lt_of_not_ge hsign
    have hto : 0 < (-r).toNat := by omega
    have hbudget : 0 < hughesYoungEquation84LogBudget
        (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)
        (-r).toNat :=
      lt_of_lt_of_le zero_lt_one (one_le_hughesYoungEquation84LogBudget _ _ _)
    have hmass : 0 < hughesYoungEquation84LogProfileMass :=
      hughesYoungEquation84LogProfileMass_pos
    positivity

/-- Both signs of the literal DFI central series inherit one uniform
native-contour Gaussian bound.  This theorem is the exact bridge from the
equation-(84) estimates to the signed finite source. -/
theorem exists_norm_dfiSignedCentralSeries_pure_smallContour_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ {T t u : ℝ} {h k : ℕ} {r : ℤ},
      Real.exp 4 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
      4 * C * hughesYoungSmallContour T ≤ 1 →
      0 < h → 0 < k → r ≠ 0 →
      ‖dfiSignedCentralSeries
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
          (hughesYoungPureReducedMellinWeight T t
            (hughesYoungSmallContour T) u h k)‖ ≤
        hughesYoungSmallContourSignedShiftCoefficient T h k r *
          (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
            (1 + |u|) ^ 17) := by
  obtain ⟨Cpos, Dpos, hCpos, hDpos, hpos⟩ :=
    exists_norm_hughesYoungEquation84PositiveContourSeries_smallContour_le
  obtain ⟨Cneg, Dneg, hCneg, hDneg, hneg⟩ :=
    exists_norm_hughesYoungEquation84NegativeContourSeries_smallContour_le
  let C : ℝ := max Cpos Cneg
  let D : ℝ := max Dpos Dneg
  have hC : 0 < C := hCpos.trans_le (le_max_left _ _)
  have hD : 0 < D := hDpos.trans_le (le_max_left _ _)
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t u h k r hT ht hcontour hh hk hr0
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hc : 0 ≤ hughesYoungSmallContour T :=
    (hughesYoungSmallContour_spec
      ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)).1.le
  have hcontourPos : 4 * Cpos * hughesYoungSmallContour T ≤ 1 := by
    calc
      4 * Cpos * hughesYoungSmallContour T ≤
          4 * C * hughesYoungSmallContour T := by
            gcongr
            exact le_max_left _ _
      _ ≤ 1 := hcontour
  have hcontourNeg : 4 * Cneg * hughesYoungSmallContour T ≤ 1 := by
    calc
      4 * Cneg * hughesYoungSmallContour T ≤
          4 * C * hughesYoungSmallContour T := by
            gcongr
            exact le_max_right _ _
      _ ≤ 1 := hcontour
  have hcHalf : hughesYoungSmallContour T < 1 / 2 := by
    have hlog4 : 4 ≤ Real.log T := by
      simpa using Real.log_le_log (Real.exp_pos 4) hT
    unfold hughesYoungSmallContour
    calc
      (Real.log T)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlog4
      _ < 1 / 2 := by norm_num
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        by_contra hn0
        apply hr0
        simp [Nat.eq_zero_of_not_pos hn0]
      have heq :
          dfiSignedCentralSeries a b (n : ℤ)
              (hughesYoungPureReducedMellinWeight T t
                (hughesYoungSmallContour T) u h k) =
            hughesYoungEquation84PositiveContourSeries T t h k a b n
              ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I) := by
        rw [dfiSignedCentralSeries_ofNat_pureReduced_eq_equation83
            T t (hughesYoungSmallContour T) u a b hn,
          hughesYoungEquation83PositiveCentral_eq_equation84
            T t u
              (hughesYoungSmallContour_spec
                ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)).1
              hcHalf
              h k a b n,
          hughesYoungEquation84Positive_eq_contourSeries
            T t u hcHalf h k a b hn]
      have hp := hpos (T := T) (t := t) (u := u)
        (h := h) (k := k) (r := n) hT ht hcontourPos hh hk hn
      change ‖dfiSignedCentralSeries a b (n : ℤ)
          (hughesYoungPureReducedMellinWeight T t
            (hughesYoungSmallContour T) u h k)‖ ≤ _
      rw [heq]
      let P : ℝ :=
        (‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (n : ℝ) ^ (-2 * hughesYoungSmallContour T)) *
          (4 * (((a * b * n ^ 2 : ℕ) : ℝ) *
            hughesYoungEquation84LogBudget a b n ^ 2 *
            hughesYoungEquation84LogProfileMass))
      let G : ℝ := T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17
      have hbudget : 0 < hughesYoungEquation84LogBudget a b n :=
        lt_of_lt_of_le zero_lt_one (one_le_hughesYoungEquation84LogBudget _ _ _)
      have hmass : 0 < hughesYoungEquation84LogProfileMass :=
        hughesYoungEquation84LogProfileMass_pos
      have hfront : 0 ≤
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
            (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
            (n : ℝ) ^ (-2 * hughesYoungSmallContour T) := by positivity
      have hback : 0 ≤
          4 * (((a * b * n ^ 2 : ℕ) : ℝ) *
            hughesYoungEquation84LogBudget a b n ^ 2 *
            hughesYoungEquation84LogProfileMass) := by positivity
      have hP : 0 ≤ P := by
        dsimp only [P]
        exact mul_nonneg hfront hback
      have hG : 0 ≤ G := by dsimp only [G]; positivity
      have hp' :
          ‖hughesYoungEquation84PositiveContourSeries T t h k a b n
              ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤
            P * Dpos * G := by
        calc
          _ ≤ _ := hp
          _ = P * Dpos * G := by dsimp only [P, G, a, b]; ring
      have hcoeff :
          hughesYoungSmallContourSignedShiftCoefficient T h k (n : ℤ) = P := by
        simp [hughesYoungSmallContourSignedShiftCoefficient, hn.ne', P, a, b]
      have hDD : Dpos ≤ max Dpos Dneg := le_max_left _ _
      calc
        _ ≤ P * Dpos * G := hp'
        _ ≤ P * D * G := by dsimp only [D]; gcongr
        _ = hughesYoungSmallContourSignedShiftCoefficient T h k (n : ℤ) *
              (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
                (1 + |u|) ^ 17) := by rw [hcoeff]; dsimp only [G]; ring
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by
        dsimp only [n]
        omega
      have heq :
          dfiSignedCentralSeries a b (-(n : ℤ))
              (hughesYoungPureReducedMellinWeight T t
                (hughesYoungSmallContour T) u h k) =
            hughesYoungEquation84NegativeContourSeries T t h k a b n
              ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I) := by
        rw [dfiSignedCentralSeries_neg_pureReduced_eq_equation83
            T t (hughesYoungSmallContour T) u a b hn,
          hughesYoungEquation83NegativeCentral_eq_equation84
            T t u
              (hughesYoungSmallContour_spec
                ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)).1
              hcHalf
              h k a b n,
          hughesYoungEquation84Negative_eq_contourSeries
            T t u hcHalf h k a b hn]
      have hp := hneg (T := T) (t := t) (u := u)
        (h := h) (k := k) (r := n) hT ht hcontourNeg hh hk hn
      change ‖dfiSignedCentralSeries a b (Int.negSucc m)
          (hughesYoungPureReducedMellinWeight T t
            (hughesYoungSmallContour T) u h k)‖ ≤ _
      rw [hrCast, heq]
      let P : ℝ :=
        (‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (n : ℝ) ^ (-2 * hughesYoungSmallContour T)) *
          (4 * (((b * a * n ^ 2 : ℕ) : ℝ) *
            hughesYoungEquation84LogBudget b a n ^ 2 *
            hughesYoungEquation84LogProfileMass))
      let G : ℝ := T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17
      have hbudget : 0 < hughesYoungEquation84LogBudget b a n :=
        lt_of_lt_of_le zero_lt_one (one_le_hughesYoungEquation84LogBudget _ _ _)
      have hmass : 0 < hughesYoungEquation84LogProfileMass :=
        hughesYoungEquation84LogProfileMass_pos
      have hfront : 0 ≤
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
            (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
            (n : ℝ) ^ (-2 * hughesYoungSmallContour T) := by positivity
      have hback : 0 ≤
          4 * (((b * a * n ^ 2 : ℕ) : ℝ) *
            hughesYoungEquation84LogBudget b a n ^ 2 *
            hughesYoungEquation84LogProfileMass) := by positivity
      have hP : 0 ≤ P := by
        dsimp only [P]
        exact mul_nonneg hfront hback
      have hG : 0 ≤ G := by dsimp only [G]; positivity
      have hp' :
          ‖hughesYoungEquation84NegativeContourSeries T t h k a b n
              ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)‖ ≤
            P * Dneg * G := by
        calc
          _ ≤ _ := hp
          _ = P * Dneg * G := by dsimp only [P, G, a, b]; ring
      have hcoeff :
          hughesYoungSmallContourSignedShiftCoefficient T h k (-(n : ℤ)) = P := by
        simp [hughesYoungSmallContourSignedShiftCoefficient, hn.ne', P, a, b]
      have hDD : Dneg ≤ max Dpos Dneg := le_max_right _ _
      calc
        _ ≤ P * Dneg * G := hp'
        _ ≤ P * D * G := by dsimp only [D]; gcongr
        _ = hughesYoungSmallContourSignedShiftCoefficient T h k (-(n : ℤ)) *
              (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
                (1 + |u|) ^ 17) := by rw [hcoeff]; dsimp only [G]; ring

/-- The finite arithmetic mass left after taking norms of the literal signed
shift family on the small contour. -/
noncomputable def hughesYoungFiniteSmallContourShiftMass
    (T : ℝ) (h k K : ℕ) : ℝ :=
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let B := hughesYoungFullDyadicBound (K + 1)
  ∑ r ∈ hughesYoungShiftInterval a b B B,
    hughesYoungSmallContourSignedShiftCoefficient T h k r

theorem hughesYoungFiniteSmallContourShiftMass_nonneg
    (T : ℝ) (h k K : ℕ) :
    0 ≤ hughesYoungFiniteSmallContourShiftMass T h k K := by
  unfold hughesYoungFiniteSmallContourShiftMass
  apply Finset.sum_nonneg
  intro r _hr
  exact hughesYoungSmallContourSignedShiftCoefficient_nonneg T h k r

/-- Pointwise Gaussian domination of the actual finite pure signed source.
The source is the object integrated in the Hughes--Young small rectangle;
the estimate does not replace it by an independently supplied family. -/
theorem exists_norm_hughesYoungFinitePureSignedCentralAtHeight_smallContour_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T t u : ℝ} {h k K : ℕ},
        Real.exp 4 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
        4 * C * hughesYoungSmallContour T ≤ 1 →
        0 < h → 0 < k →
        ‖hughesYoungFinitePureSignedCentralAtHeight T t
            (hughesYoungSmallContour T) u h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K‖ ≤
          hughesYoungFiniteSmallContourShiftMass T h k K *
            (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
              (1 + |u|) ^ 17) := by
  obtain ⟨C, D, hC, hD, hterm⟩ :=
    exists_norm_dfiSignedCentralSeries_pure_smallContour_le
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t u h k K hT ht hcontour hh hk
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let B := hughesYoungFullDyadicBound (K + 1)
  let G : ℝ := D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hsum :
      ∑ r ∈ hughesYoungShiftInterval a b B B,
          ‖if r = 0 then (0 : ℂ) else
            dfiSignedCentralSeries a b r
              (hughesYoungPureReducedMellinWeight T t
                (hughesYoungSmallContour T) u h k)‖ ≤
        ∑ r ∈ hughesYoungShiftInterval a b B B,
          hughesYoungSmallContourSignedShiftCoefficient T h k r * G := by
    apply Finset.sum_le_sum
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      simp [hughesYoungSmallContourSignedShiftCoefficient]
    · simp only [hr0, if_false]
      exact hterm hT ht hcontour hh hk hr0
  calc
    ‖hughesYoungFinitePureSignedCentralAtHeight T t
        (hughesYoungSmallContour T) u h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K‖
        ≤ ∑ r ∈ hughesYoungShiftInterval a b B B,
            ‖if r = 0 then (0 : ℂ) else
              dfiSignedCentralSeries a b r
                (hughesYoungPureReducedMellinWeight T t
                  (hughesYoungSmallContour T) u h k)‖ := by
            unfold hughesYoungFinitePureSignedCentralAtHeight
            dsimp only [a, b, B]
            exact norm_sum_le _ _
    _ ≤ ∑ r ∈ hughesYoungShiftInterval a b B B,
          hughesYoungSmallContourSignedShiftCoefficient T h k r * G := hsum
    _ = hughesYoungFiniteSmallContourShiftMass T h k K * G := by
          rw [← Finset.sum_mul]
          rfl
    _ = hughesYoungFiniteSmallContourShiftMass T h k K *
          (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
            (1 + |u|) ^ 17) := rfl

/-- Whole-line integrability of the actual finite signed source. -/
theorem integrable_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight
    {T c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (t : ℝ) {h k a b : ℕ} (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    Integrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFinitePureSignedCentralAtHeight T t c u h k a b K) := by
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let f : ℤ → ℝ → ℂ := fun r u =>
    if r = 0 then 0 else
      (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungPureReducedMellinWeight T t c u h k)
  have hf : ∀ r ∈ S, Integrable (f r) := by
    intro r _hr
    by_cases hr0 : r = 0
    · simp [f, hr0]
    · simp only [f, hr0, if_false]
      exact integrable_heightWeight_mul_dfiSignedCentralSeries_pure
        hc hcHalf t ha hb hr0
  have hsum : Integrable (fun u => ∑ r ∈ S, f r u) := by
    exact integrable_finsetSum S hf
  refine hsum.congr ?_
  filter_upwards [] with u
  unfold hughesYoungFinitePureSignedCentralAtHeight
  simp only [B, S, f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hr0 : r = 0 <;> simp [hr0]

/-- At a fixed physical height and mollifier pair, replacing the native
small contour by the whole equation-(84) line has a Gaussian tail. -/
theorem exists_norm_hughesYoungFinitePureContourTailAtHeight_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T t H : ℝ} {h k K : ℕ},
        Real.exp 4 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
        4 * C * hughesYoungSmallContour T ≤ 1 →
        0 < h → 0 < k → 1 ≤ H →
        ‖(∫ u : ℝ,
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungFinitePureSignedCentralAtHeight T t
                  (hughesYoungSmallContour T) u h k
                  (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) K) -
            ∫ u in -H..H,
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungFinitePureSignedCentralAtHeight T t
                  (hughesYoungSmallContour T) u h k
                  (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) K‖ ≤
          hughesYoungFiniteSmallContourShiftMass T h k K *
            (D * T ^ (4 : ℕ)) *
              hughesYoungSmallContourGaussianTailConstant *
                Real.exp (-40 * H ^ 2) := by
  obtain ⟨C, D, hC, hD, hsource⟩ :=
    exists_norm_hughesYoungFinitePureSignedCentralAtHeight_smallContour_le
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t H h k K hT ht hcontour hh hk hH
  have hT0 : 0 < T := (Real.exp_pos 4).trans_le hT
  have hcSpec := hughesYoungSmallContour_spec
    ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hT
  have hcHalf : hughesYoungSmallContour T < 1 / 2 := by
    unfold hughesYoungSmallContour
    calc
      (Real.log T)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlog4
      _ < 1 / 2 := by norm_num
  let f : ℝ → ℂ := fun u =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFinitePureSignedCentralAtHeight T t
        (hughesYoungSmallContour T) u h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K
  let A : ℝ := hughesYoungFiniteSmallContourShiftMass T h k K *
    (D * T ^ (4 : ℕ))
  let p : ℝ → ℝ := fun u => Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17
  have hf : Integrable f := by
    exact integrable_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight
      hcSpec.1 hcHalf t (hughesYoungReducedLeft_pos hh)
        (hughesYoungReducedRight_pos hh hk) K
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (hughesYoungFiniteSmallContourShiftMass_nonneg T h k K)
      (mul_nonneg hD.le (by positivity))
  have hp : Integrable p := by
    exact integrable_exp_neg_84_mul_one_add_abs_pow 17
  have hAp : Integrable (fun u => A * p u) := hp.const_mul A
  have hpoint : ∀ u : ℝ, ‖f u‖ ≤ A * p u := by
    intro u
    by_cases hw : hughesYoungHeightWeight T t = 0
    · have hpu : 0 ≤ p u := by dsimp only [p]; positivity
      simp [f, hw, mul_nonneg hA hpu]
    · have hwt : 0 ≤ hughesYoungHeightWeight T t :=
        hughesYoungHeightWeight_nonneg T t
      have hw1 : hughesYoungHeightWeight T t ≤ 1 :=
        hughesYoungHeightWeight_le_one T t
      have hs := hsource (u := u) (K := K) hT ht hcontour hh hk
      change ‖(hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFinitePureSignedCentralAtHeight T t
            (hughesYoungSmallContour T) u h k
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) K‖ ≤ A * p u
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hwt]
      calc
        _ ≤ 1 * (hughesYoungFiniteSmallContourShiftMass T h k K *
              (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
                (1 + |u|) ^ 17)) := by
              gcongr
        _ = A * p u := by dsimp only [A, p]; ring
  have htail := norm_integral_sub_symmetricIntervalIntegral_le_compl_norm
    hf (zero_le_one.trans hH)
  calc
    ‖(∫ u : ℝ, f u) - ∫ u in -H..H, f u‖
        ≤ ∫ u in (Set.Ioc (-H) H)ᶜ, ‖f u‖ := htail
    _ ≤ ∫ u in (Set.Ioc (-H) H)ᶜ, A * p u :=
      MeasureTheory.setIntegral_mono_on hf.norm.integrableOn hAp.integrableOn
        measurableSet_Ioc.compl fun u _hu => hpoint u
    _ = A * ∫ u in (Set.Ioc (-H) H)ᶜ, p u := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ A * (hughesYoungSmallContourGaussianTailConstant *
          Real.exp (-40 * H ^ 2)) := by
      gcongr
      exact integral_compl_Ioc_exp_neg84_mul_one_add_abs_pow_seventeen_le hH
    _ = hughesYoungFiniteSmallContourShiftMass T h k K *
          (D * T ^ (4 : ℕ)) * hughesYoungSmallContourGaussianTailConstant *
            Real.exp (-40 * H ^ 2) := by dsimp only [A]; ring

/-- A polynomial upper bound for the actual terminal dyadic cutoff.  The
lower bound used for the shift tail and this upper bound together pin the
finite equation-(84) window to its physical scale. -/
theorem hughesYoungTerminalFullDyadicBound_le_seven_mul_pow_hundred
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) ≤
      7 * T ^ (100 : ℕ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_two]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hceil : (hughesYoungGlobalDepth T : ℝ) < 100 * Real.log T + 1 := by
    simpa only [hughesYoungGlobalDepth] using
      Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hlogT0)
  have hlogRatio0 : 0 ≤ Real.log hughesYoungDyadicRatio :=
    (Real.log_pos one_lt_hughesYoungDyadicRatio).le
  have hlogRatio1 : Real.log hughesYoungDyadicRatio ≤ 1 := by
    rw [Real.log_le_iff_le_exp hughesYoungDyadicRatio_pos]
    exact hughesYoungDyadicRatio_lt_two.le.trans Real.exp_one_gt_two.le
  have harg : Real.log hughesYoungDyadicRatio *
      (hughesYoungGlobalDepth T : ℝ) ≤ 100 * Real.log T + 1 := by
    calc
      _ ≤ 1 * (hughesYoungGlobalDepth T : ℝ) := by gcongr
      _ ≤ 100 * Real.log T + 1 := by simpa using hceil.le
  have hscale : hughesYoungFullDyadicScale (hughesYoungGlobalDepth T + 1) ≤
      3 * T ^ (100 : ℕ) := by
    rw [hughesYoungFullDyadicScale, hughesYoungDyadicScale]
    calc
      hughesYoungDyadicRatio ^ hughesYoungGlobalDepth T =
          Real.exp (Real.log hughesYoungDyadicRatio *
            (hughesYoungGlobalDepth T : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hughesYoungDyadicRatio_pos]
      _ ≤ Real.exp (100 * Real.log T + 1) := Real.exp_le_exp.mpr harg
      _ = Real.exp 1 * T ^ (100 : ℕ) := by
        rw [add_comm, Real.exp_add]
        congr 1
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hT0]
        congr 1
        ring
      _ ≤ 3 * T ^ (100 : ℕ) := by
        gcongr
        exact Real.exp_one_lt_three.le
  have hceilBound :
      (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) <
        2 * hughesYoungFullDyadicScale (hughesYoungGlobalDepth T + 1) + 1 := by
    unfold hughesYoungFullDyadicBound
    simpa using Nat.ceil_lt_add_one
      (mul_nonneg (by norm_num)
        (hughesYoungFullDyadicScale_pos (hughesYoungGlobalDepth T + 1)).le)
  have hpowOne : 1 ≤ T ^ (100 : ℕ) := one_le_pow₀ hT1
  calc
    _ ≤ 2 * hughesYoungFullDyadicScale (hughesYoungGlobalDepth T + 1) + 1 :=
      hceilBound.le
    _ ≤ 2 * (3 * T ^ (100 : ℕ)) + 1 := by gcongr
    _ ≤ 7 * T ^ (100 : ℕ) := by linarith

theorem abs_log_natCast_le_natCast {n : ℕ} (hn : 0 < n) :
    |Real.log (n : ℝ)| ≤ (n : ℝ) := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnOne
  rw [abs_of_nonneg hlog0]
  exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)

/-- The logarithmic coefficient in equation (84) is polynomially bounded
on a common positive arithmetic scale. -/
theorem hughesYoungEquation84LogBudget_le_commonScale
    {a b r : ℕ} {E : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hE : 1 ≤ E) (haE : (a : ℝ) ≤ E) (hbE : (b : ℝ) ≤ E)
    (hrE : (r : ℝ) ≤ E) :
    hughesYoungEquation84LogBudget a b r ≤
      (5 + 4 * |Real.eulerMascheroniConstant|) * E := by
  have hla := (abs_log_natCast_le_natCast ha).trans haE
  have hlb := (abs_log_natCast_le_natCast hb).trans hbE
  have hlr := (abs_log_natCast_le_natCast hr).trans hrE
  have hgamma : 0 ≤ |Real.eulerMascheroniConstant| := abs_nonneg _
  unfold hughesYoungEquation84LogBudget
  nlinarith

/-- Polynomial domination of one positive signed-shift coefficient in the
literal finite window. -/
theorem hughesYoungSmallContourSignedShiftCoefficient_ofNat_le_polynomial
    {T ell B : ℝ} {h k M n : ℕ}
    (hT : Real.exp 4 ≤ T) (hell : 1 ≤ ell) (hB : 1 ≤ B)
    (hh : 0 < h) (hk : 0 < k)
    (hhle : (h : ℝ) ≤ ell) (hkle : (k : ℝ) ≤ ell)
    (hMB : (M : ℝ) ≤ B) (hn : 0 < n)
    (hnM : n ≤ hughesYoungReducedLeft h k * M) :
    hughesYoungSmallContourSignedShiftCoefficient T h k (n : ℤ) ≤
      4 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungEquation84LogProfileMass * ell ^ (8 : ℕ) * B ^ (4 : ℕ) := by
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let c := hughesYoungSmallContour T
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have haCast : (a : ℝ) ≤ h := by
    exact_mod_cast hughesYoungReducedLeft_le h k
  have hbCast : (b : ℝ) ≤ k := by
    exact_mod_cast hughesYoungReducedRight_le h k
  have haell : (a : ℝ) ≤ ell := haCast.trans hhle
  have hbell : (b : ℝ) ≤ ell := hbCast.trans hkle
  have hc := hughesYoungSmallContour_spec
    ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hT
  have hcHalf : c ≤ 1 / 2 := by
    dsimp only [c]
    unfold hughesYoungSmallContour
    calc
      (Real.log T)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlog4
      _ ≤ 1 / 2 := by norm_num
  have hscalar := norm_hughesYoungLocalizedStaticScalar_le_coefficients
    (T := T) hh hk
  have hdivh : ((h.divisors.card : ℕ) : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self h
  have hdivk : ((k.divisors.card : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self k
  have hcoeffh : ‖shortMobiusSquareCoeff T h‖ ≤ ell :=
    (norm_shortMobiusSquareCoeff_le_divisors T hh).trans (hdivh.trans hhle)
  have hcoeffk : ‖shortMobiusSquareCoeff T k‖ ≤ ell :=
    (norm_shortMobiusSquareCoeff_le_divisors T hk).trans (hdivk.trans hkle)
  have hscalarEll : ‖hughesYoungLocalizedStaticScalar T h k‖ ≤ ell ^ (2 : ℕ) := by
    calc
      _ ≤ ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ := hscalar
      _ ≤ ell * ell := mul_le_mul hcoeffh hcoeffk (norm_nonneg _)
        (zero_le_one.trans hell)
      _ = ell ^ (2 : ℕ) := by ring
  have haPow : (a : ℝ) ^ (c - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast ha) (by linarith)
  have hbPow : (b : ℝ) ^ (c - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hb) (by linarith)
  have hnPow : (n : ℝ) ^ (-2 * c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hc.1.le)
  have hnCast : (n : ℝ) ≤ ell * B := by
    calc
      (n : ℝ) ≤ ((a * M : ℕ) : ℝ) := by exact_mod_cast hnM
      _ = (a : ℝ) * (M : ℝ) := by norm_cast
      _ ≤ ell * B := mul_le_mul haell hMB (by positivity) (by positivity)
  have hE : 1 ≤ ell * B := by nlinarith
  have haE : (a : ℝ) ≤ ell * B := haell.trans (by nlinarith)
  have hbE : (b : ℝ) ≤ ell * B := hbell.trans (by nlinarith)
  have hbudget := hughesYoungEquation84LogBudget_le_commonScale
    ha hb hn hE haE hbE hnCast
  have hnat : ((a * b * n ^ 2 : ℕ) : ℝ) ≤ ell ^ (4 : ℕ) * B ^ (2 : ℕ) := by
    push_cast
    calc
      (a : ℝ) * (b : ℝ) * (n : ℝ) ^ 2 ≤
          ell * ell * (ell * B) ^ 2 := by gcongr
      _ = ell ^ (4 : ℕ) * B ^ (2 : ℕ) := by ring
  have hmass := hughesYoungEquation84LogProfileMass_pos.le
  have hbudget0 : 0 ≤ hughesYoungEquation84LogBudget a b n :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b n)
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [hughesYoungSmallContourSignedShiftCoefficient, hnZ,
    Int.natCast_nonneg, Int.toNat_natCast, if_false, if_true]
  calc
    _ ≤ (ell ^ (2 : ℕ) * 1 * 1 * 1) *
        (4 * ((ell ^ (4 : ℕ) * B ^ (2 : ℕ)) *
          ((5 + 4 * |Real.eulerMascheroniConstant|) * (ell * B)) ^ 2 *
          hughesYoungEquation84LogProfileMass)) := by gcongr
    _ = 4 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungEquation84LogProfileMass * ell ^ (8 : ℕ) * B ^ (4 : ℕ) := by ring

theorem hughesYoungSmallContourSignedShiftCoefficient_neg_eq_swap
    (T : ℝ) (h k n : ℕ) (hn : 0 < n) :
    hughesYoungSmallContourSignedShiftCoefficient T h k (-(n : ℤ)) =
      hughesYoungSmallContourSignedShiftCoefficient T k h (n : ℤ) := by
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hneg : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
  have hnegZ : -(n : ℤ) ≠ 0 := by omega
  simp only [hughesYoungSmallContourSignedShiftCoefficient, hnZ, hnegZ,
    if_false, hneg, Int.natCast_nonneg, if_true, neg_neg, Int.toNat_natCast]
  rw [hughesYoungReducedLeft_swap h k, hughesYoungReducedRight_swap h k,
    hughesYoungLocalizedStaticScalar_swap T h k]
  push_cast
  ring

theorem hughesYoungSmallContourSignedShiftCoefficient_neg_le_polynomial
    {T ell B : ℝ} {h k M n : ℕ}
    (hT : Real.exp 4 ≤ T) (hell : 1 ≤ ell) (hB : 1 ≤ B)
    (hh : 0 < h) (hk : 0 < k)
    (hhle : (h : ℝ) ≤ ell) (hkle : (k : ℝ) ≤ ell)
    (hMB : (M : ℝ) ≤ B) (hn : 0 < n)
    (hnM : n ≤ hughesYoungReducedRight h k * M) :
    hughesYoungSmallContourSignedShiftCoefficient T h k (-(n : ℤ)) ≤
      4 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungEquation84LogProfileMass * ell ^ (8 : ℕ) * B ^ (4 : ℕ) := by
  rw [hughesYoungSmallContourSignedShiftCoefficient_neg_eq_swap T h k n hn]
  apply hughesYoungSmallContourSignedShiftCoefficient_ofNat_le_polynomial
    hT hell hB hk hh hkle hhle hMB hn
  simpa only [hughesYoungReducedLeft_swap] using hnM

/-- The complete finite signed-shift mass has a uniform polynomial majorant
once the mollifier and dyadic cutoffs are placed below common scales. -/
theorem hughesYoungFiniteSmallContourShiftMass_le_polynomial
    {T ell B : ℝ} {h k K : ℕ}
    (hT : Real.exp 4 ≤ T) (hell : 1 ≤ ell) (hB : 1 ≤ B)
    (hh : 0 < h) (hk : 0 < k)
    (hhle : (h : ℝ) ≤ ell) (hkle : (k : ℝ) ≤ ell)
    (hKB : (hughesYoungFullDyadicBound (K + 1) : ℝ) ≤ B) :
    hughesYoungFiniteSmallContourShiftMass T h k K ≤
      12 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungEquation84LogProfileMass * ell ^ (9 : ℕ) * B ^ (5 : ℕ) := by
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let M := hughesYoungFullDyadicBound (K + 1)
  let E : ℝ := 4 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungEquation84LogProfileMass * ell ^ (8 : ℕ) * B ^ (4 : ℕ)
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have haCast : (a : ℝ) ≤ h := by
    exact_mod_cast hughesYoungReducedLeft_le h k
  have hbCast : (b : ℝ) ≤ k := by
    exact_mod_cast hughesYoungReducedRight_le h k
  have haell : (a : ℝ) ≤ ell := haCast.trans hhle
  have hbell : (b : ℝ) ≤ ell := hbCast.trans hkle
  have hE : 0 ≤ E := by
    dsimp only [E]
    have hmass := hughesYoungEquation84LogProfileMass_pos.le
    positivity
  have hterm : ∀ r ∈ hughesYoungShiftInterval a b M M,
      hughesYoungSmallContourSignedShiftCoefficient T h k r ≤ E := by
    intro r hr
    simp only [hughesYoungShiftInterval, Finset.mem_Icc] at hr
    cases r with
    | ofNat n =>
        by_cases hn0 : n = 0
        · subst n
          simp only [hughesYoungSmallContourSignedShiftCoefficient, Int.ofNat_eq_natCast,
            Int.ofNat_zero, ite_true]
          exact hE
        · have hn : 0 < n := Nat.pos_of_ne_zero hn0
          have hnM : n ≤ a * M := by
            exact Int.ofNat_le.mp (by
              simpa only [Int.natCast_mul] using hr.2)
          simpa only [E, a, b, M] using
            hughesYoungSmallContourSignedShiftCoefficient_ofNat_le_polynomial
              hT hell hB hh hk hhle hkle hKB hn hnM
    | negSucc m =>
        let n := m + 1
        have hn : 0 < n := by dsimp only [n]; omega
        have hrEq : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
        have hnM : n ≤ b * M := by
          have hlower : (-(b * M : ℕ) : ℤ) ≤ -(n : ℤ) := by simpa [hrEq] using hr.1
          exact_mod_cast (neg_le_neg_iff.mp hlower)
        rw [hrEq]
        simpa only [E, a, b, M] using
          hughesYoungSmallContourSignedShiftCoefficient_neg_le_polynomial
            hT hell hB hh hk hhle hkle hKB hn hnM
  have hcardEq : (hughesYoungShiftInterval a b M M).card = a * M + b * M + 1 := by
    unfold hughesYoungShiftInterval
    rw [Int.card_Icc]
    norm_num
    omega
  have hcard : ((hughesYoungShiftInterval a b M M).card : ℝ) ≤ 3 * ell * B := by
    rw [hcardEq]
    push_cast
    have haM : (a : ℝ) * (M : ℝ) ≤ ell * B :=
      mul_le_mul haell hKB (by positivity) (by positivity)
    have hbM : (b : ℝ) * (M : ℝ) ≤ ell * B :=
      mul_le_mul hbell hKB (by positivity) (by positivity)
    nlinarith [mul_le_mul hell hB]
  unfold hughesYoungFiniteSmallContourShiftMass
  change ∑ r ∈ hughesYoungShiftInterval a b M M,
      hughesYoungSmallContourSignedShiftCoefficient T h k r ≤ _
  calc
    _ ≤ ∑ _r ∈ hughesYoungShiftInterval a b M M, E := Finset.sum_le_sum hterm
    _ = ((hughesYoungShiftInterval a b M M).card : ℝ) * E := by simp
    _ ≤ (3 * ell * B) * E := mul_le_mul_of_nonneg_right hcard hE
    _ = 12 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungEquation84LogProfileMass * ell ^ (9 : ℕ) * B ^ (5 : ℕ) := by
      dsimp only [E]
      ring

/-- The `hughesYoungTerminalSmallContourTotalMass` definition used by the source-facing construction in `HughesYoungSmallContourQuantitative`. -/
noncomputable def hughesYoungTerminalSmallContourTotalMass (T : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungFiniteSmallContourShiftMass T h k (hughesYoungGlobalDepth T)

theorem hughesYoungTerminalSmallContourTotalMass_le_pow_fiveHundredTwentyTwo
    {T : ℝ} (hT : Real.exp 4 ≤ T) :
    hughesYoungTerminalSmallContourTotalMass T ≤
      (12 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungEquation84LogProfileMass * 9 ^ (11 : ℕ) * 7 ^ (5 : ℕ)) *
          T ^ (522 : ℕ) := by
  let ell : ℝ := 9 * T ^ (2 : ℕ)
  let B : ℝ := 7 * T ^ (100 : ℕ)
  let E : ℝ := 12 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungEquation84LogProfileMass * ell ^ (9 : ℕ) * B ^ (5 : ℕ)
  have hT1 : 1 ≤ T := by
    have hexp : Real.exp 1 ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_gt_two, hexp.trans hT]
  have hTexp1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hcut := detectorCutoff_le_three_mul T hT1
  have hcutSq : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ ell := by
    dsimp only [ell]
    push_cast
    calc
      (detectorCutoff T : ℝ) ^ 2 ≤ (3 * T) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcut 2
      _ = 9 * T ^ (2 : ℕ) := by ring
  have hpow2 : 1 ≤ T ^ (2 : ℕ) := one_le_pow₀ hT1
  have hpow100 : 1 ≤ T ^ (100 : ℕ) := one_le_pow₀ hT1
  have hell : 1 ≤ ell := by dsimp only [ell]; nlinarith
  have hB : 1 ≤ B := by dsimp only [B]; nlinarith
  have hterminal :
      (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) ≤ B := by
    simpa only [B] using
      hughesYoungTerminalFullDyadicBound_le_seven_mul_pow_hundred hTexp1
  have hE : 0 ≤ E := by
    dsimp only [E]
    have hmass := hughesYoungEquation84LogProfileMass_pos.le
    positivity
  have hterm : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        hughesYoungFiniteSmallContourShiftMass T h k (hughesYoungGlobalDepth T) ≤ E := by
    intro h hhmem k hkmem
    have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    have hhCast : (h : ℝ) ≤ ((detectorCutoff T) ^ 2 : ℕ) := by
      exact_mod_cast (Finset.mem_Icc.mp hhmem).2
    have hkCast : (k : ℝ) ≤ ((detectorCutoff T) ^ 2 : ℕ) := by
      exact_mod_cast (Finset.mem_Icc.mp hkmem).2
    have hhle : (h : ℝ) ≤ ell := hhCast.trans hcutSq
    have hkle : (k : ℝ) ≤ ell := hkCast.trans hcutSq
    simpa only [E] using hughesYoungFiniteSmallContourShiftMass_le_polynomial
      hT hell hB hh hk hhle hkle hterminal
  have hcardNat : (Finset.Icc 1 ((detectorCutoff T) ^ 2)).card ≤
      (detectorCutoff T) ^ 2 := by simp
  have hcardCast : ((Finset.Icc 1 ((detectorCutoff T) ^ 2)).card : ℝ) ≤
      (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hcard : ((Finset.Icc 1 ((detectorCutoff T) ^ 2)).card : ℝ) ≤ ell :=
    hcardCast.trans hcutSq
  unfold hughesYoungTerminalSmallContourTotalMass
  calc
    _ ≤ ∑ _h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ _k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2), E := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      exact hterm h hhmem k hkmem
    _ = ((Finset.Icc 1 ((detectorCutoff T) ^ 2)).card : ℝ) ^ 2 * E := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ell ^ (2 : ℕ) * E :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard 2) hE
    _ = (12 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungEquation84LogProfileMass * 9 ^ (11 : ℕ) * 7 ^ (5 : ℕ)) *
            T ^ (522 : ℕ) := by dsimp only [E, ell, B]; ring

end RiemannZeta.GuthMaynard
