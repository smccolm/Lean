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

end RiemannZeta.GuthMaynard
