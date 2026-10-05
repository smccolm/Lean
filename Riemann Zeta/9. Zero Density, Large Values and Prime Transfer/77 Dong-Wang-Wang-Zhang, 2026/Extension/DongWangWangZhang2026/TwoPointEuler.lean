import DongWangWangZhang2026.MeanValueEuler
import PrimeNumberTheoremAnd.MediumPNT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Two-frequency Euler-product inputs

The finite trigonometric majorant has mean strictly below two thirds. This
provides room for the source's one-third Lipschitz specialization without
requiring an optimal Fourier expansion of the absolute cosine.
-/

open Complex Filter MeasureTheory
open scoped Topology

namespace DongWangWangZhang2026
noncomputable section

theorem abs_le_sextic_majorant {r : ℝ} (hr : |r| ≤ 1) :
    |r| ≤ (5 / 113 : ℝ) * (5 + 30 * r ^ 2 - 20 * r ^ 4 + 8 * r ^ 6) := by
  have hr2 : r ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg r) hr 2
  have hpoly : 0 ≤ 5 + 30 * r ^ 2 - 20 * r ^ 4 + 8 * r ^ 6 := by
    have h24 : r ^ 4 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
    nlinarith [sq_nonneg (r ^ 3)]
  have hpositive : 0 ≤ (2 * r ^ 2 - 1) ^ 4 * (4 * (r ^ 2 - 3 / 2) ^ 2 + 16) :=
    mul_nonneg (by positivity) (by positivity)
  have hidentity : 25 * (5 + 30 * r ^ 2 - 20 * r ^ 4 + 8 * r ^ 6) ^ 2 -
      12769 * r ^ 2 =
        25 * ((2 * r ^ 2 - 1) ^ 4 * (4 * (r ^ 2 - 3 / 2) ^ 2 + 16)) + 31 * r ^ 2 := by
    ring
  nlinarith [sq_abs r, abs_nonneg r]

theorem abs_cos_le_three_frequency_majorant (u : ℝ) :
    |Real.cos u| ≤ 75 / 113 + (175 / 452 : ℝ) * Real.cos (2 * u) -
      (5 / 113 : ℝ) * Real.cos (4 * u) + (5 / 452 : ℝ) * Real.cos (6 * u) := by
  have h := abs_le_sextic_majorant (Real.abs_cos_le_one u)
  have h4 : Real.cos (4 * u) = 8 * Real.cos u ^ 4 - 8 * Real.cos u ^ 2 + 1 := by
    rw [show 4 * u = 2 * (2 * u) by ring, Real.cos_two_mul, Real.cos_two_mul]
    ring
  have h6 : Real.cos (6 * u) = 32 * Real.cos u ^ 6 - 48 * Real.cos u ^ 4 +
      18 * Real.cos u ^ 2 - 1 := by
    rw [show 6 * u = 3 * (2 * u) by ring, Real.cos_three_mul, Real.cos_two_mul]
    ring
  rw [Real.cos_two_mul, h4, h6]
  nlinarith

theorem three_frequency_mean_lt_two_thirds : (75 / 113 : ℝ) < 2 / 3 := by norm_num

private theorem eventually_exp_rpow_le_inverse_power {c r K : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hK : 0 < K) (A : ℝ) :
    ∀ᶠ u : ℝ in atTop, K * Real.exp (-c * u ^ r) ≤ u ^ (-A) := by
  have h := ((isLittleO_exp_neg_mul_rpow_atTop hc (-A / r)).comp_tendsto
    (tendsto_rpow_atTop hr)).bound (show 0 < 1 / K by positivity)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with u hu hu0
  simp only [Function.comp_apply, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hu0.le _) _)] at hu
  rw [← Real.rpow_mul hu0.le, show r * (-A / r) = -A by field_simp] at hu
  have hh := mul_le_mul_of_nonneg_left hu hK.le
  simpa only [← mul_assoc, mul_one_div_cancel hK.ne', one_mul] using hh

/-- The installed, audited medium-strength PNT supplies every fixed
logarithmic saving for the actual prime-weight function. The prime-power
error is removed using Mathlib's explicit square-root estimate. -/
theorem exists_theta_logarithmic_error (A : ℕ) :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      |Chebyshev.theta x - x| ≤ x / (Real.log x) ^ A := by
  obtain ⟨c, hc, hPNT⟩ := MediumPNT
  obtain ⟨K, hK, hbound⟩ := hPNT.exists_pos
  have hdecay := Real.tendsto_log_atTop.eventually
    (eventually_exp_rpow_le_inverse_power hc (by norm_num : (0 : ℝ) < 1 / 10)
      (show 0 < 2 * K by positivity) (A : ℝ))
  have hsmall := (isLittleO_log_rpow_rpow_atTop ((A + 1 : ℕ) : ℝ)
    (s := (1 / 2 : ℝ)) (by norm_num)).bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hevent : ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧
      |Chebyshev.theta x - x| ≤ x / (Real.log x) ^ A := by
    filter_upwards [hbound.bound, hdecay, hsmall, eventually_ge_atTop (3 : ℝ)]
      with x hpsi hdec hxSmall hx
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hp : 0 < (Real.log x) ^ A := pow_pos hlog _
    simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hpsi
    rw [abs_of_pos (mul_pos hx0 (Real.exp_pos _))] at hpsi
    rw [Real.rpow_neg hlog.le, Real.rpow_natCast] at hdec
    have hpsi' : |Chebyshev.psi x - x| ≤ x / (2 * (Real.log x) ^ A) := by
      have hm := mul_le_mul_of_nonneg_left hdec hx0.le
      have hid : x * ((Real.log x ^ A)⁻¹) = 2 * (x / (2 * Real.log x ^ A)) := by ring
      rw [hid] at hm
      nlinarith
    rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow,
      Real.norm_of_nonneg (pow_nonneg hlog.le _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hxSmall
    have hroot : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hxSmall (show 0 ≤ 4 * Real.sqrt x by positivity)
    rw [pow_succ] at hmul
    have hpower : 4 * Real.sqrt x * (Real.log x ^ A * Real.log x) ≤ x := by
      nlinarith [Real.sq_sqrt hx0.le]
    have hprimePower : 2 * Real.sqrt x * Real.log x ≤ x / (2 * Real.log x ^ A) := by
      apply (le_div_iff₀ (show 0 < 2 * Real.log x ^ A by positivity)).mpr
      nlinarith
    have htheta : |Chebyshev.theta x - x| ≤
        |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
      have h := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
      rw [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at h
      linarith
    refine ⟨hx, htheta.trans ?_⟩
    have hpp := (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1).trans hprimePower
    have hid : x / (2 * Real.log x ^ A) + x / (2 * Real.log x ^ A) =
        x / Real.log x ^ A := by ring
    rw [← hid]
    exact add_le_add hpsi' hpp
  obtain ⟨X, hX⟩ := eventually_atTop.mp hevent
  exact ⟨max X 3, le_max_right _ _, fun x hx =>
    (hX x ((le_max_left _ _).trans hx)).2⟩

/-- Exact partial summation against the actual prime measure, with its
Lebesgue main term separated from the PNT discrepancy. -/
theorem prime_weighted_abel_error {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {f f' : ℝ → ℝ} (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (f' u) u)
    (hf' : ContinuousOn f' (Set.Icc a b)) :
    (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, f p * Real.log p) -
        (∫ u : ℝ in a..b, f u) =
      f b * (Chebyshev.theta b - b) - f a * (Chebyshev.theta a - a) -
        ∫ u : ℝ in a..b, f' u * (Chebyshev.theta u - u) := by
  classical
  let c : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have htheta (u : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, c n) = Chebyshev.theta u := by
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  have hdiff : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u :=
    fun u hu => (hf u hu).differentiableAt
  have hderiv : IntegrableOn (deriv f) (Set.Icc a b) :=
    hf'.integrableOn_Icc.congr_fun (fun u hu => (hf u hu).deriv.symm) measurableSet_Icc
  have hs := sum_mul_eq_sub_sub_integral_mul c ha hab hdiff hderiv
  simp_rw [htheta] at hs
  have hleft : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, f p * Real.log p := by
    simp only [c, Finset.sum_filter, mul_ite, mul_zero]
  rw [hleft] at hs
  have hIntegral : (∫ u in Set.Ioc a b, deriv f u * Chebyshev.theta u) =
      ∫ u : ℝ in a..b, f' u * Chebyshev.theta u := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    rw [(hf u ⟨hu.1.le, hu.2⟩).deriv]
  rw [hIntegral] at hs
  have hfint : IntervalIntegrable f volume a b :=
    (show ContinuousOn f (Set.Icc a b) from fun u hu =>
      (hf u hu).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc hab
  have hfpint : IntervalIntegrable f' volume a b := hf'.intervalIntegrable_of_Icc hab
  have hmulId : IntervalIntegrable (fun u => f' u * u) volume a b :=
    hfpint.mul_continuousOn continuousOn_id
  have hmulTheta : IntervalIntegrable (fun u => f' u * Chebyshev.theta u) volume a b := by
    simpa only [mul_comm] using Chebyshev.theta_mono.intervalIntegrable.mul_continuousOn
      (hf'.mono (by rw [Set.uIcc_of_le hab]))
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun u hu => hf u (by simpa only [Set.uIcc_of_le hab] using hu))
    (fun u _ => hasDerivAt_id u) hfpint (intervalIntegrable_const (c := (1 : ℝ)))
  simp only [mul_one, id_eq] at hparts
  rw [intervalIntegral.integral_add hmulId hfint] at hparts
  have herr : (∫ u : ℝ in a..b, f' u * (Chebyshev.theta u - u)) =
      (∫ u : ℝ in a..b, f' u * Chebyshev.theta u) -
        ∫ u : ℝ in a..b, f' u * u := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub hmulTheta hmulId
  rw [herr]
  nlinarith [hs, hparts]

/-- The smooth reciprocal-prime test function for a single frequency. -/
def primeCosineTest (β u : ℝ) : ℝ := Real.cos (β * Real.log u) / (u * Real.log u)

/-- The exact derivative used in prime Abel summation, on `u>1`. -/
def primeCosineTestDeriv (β u : ℝ) : ℝ :=
  -β * Real.sin (β * Real.log u) / (u ^ 2 * Real.log u) -
    Real.cos (β * Real.log u) * (Real.log u + 1) / (u ^ 2 * Real.log u ^ 2)

theorem hasDerivAt_primeCosineTest (β : ℝ) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (primeCosineTest β) (primeCosineTestDeriv β u) u := by
  have hu0 : u ≠ 0 := ne_of_gt (by linarith : 0 < u)
  have hl0 := (Real.log_pos hu).ne'
  have h := (((Real.hasDerivAt_log hu0).const_mul β).cos).div
    ((hasDerivAt_id u).mul (Real.hasDerivAt_log hu0)) (mul_ne_zero hu0 hl0)
  convert h using 1
  dsimp [primeCosineTestDeriv]
  field_simp

theorem continuousOn_primeCosineTestDeriv (β : ℝ) {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (primeCosineTestDeriv β) (Set.Icc a b) := by
  intro u hu
  have hu0 : u ≠ 0 := ne_of_gt (lt_trans zero_lt_one (ha.trans_le hu.1))
  have hlog : Real.log u ≠ 0 := (Real.log_pos (ha.trans_le hu.1)).ne'
  have hden : u ^ 2 * Real.log u ≠ 0 := mul_ne_zero (pow_ne_zero _ hu0) hlog
  have hden2 : u ^ 2 * Real.log u ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hu0) (pow_ne_zero _ hlog)
  apply ContinuousAt.continuousWithinAt
  unfold primeCosineTestDeriv
  fun_prop

theorem abs_primeCosineTest_le (β : ℝ) {u : ℝ} (hu : 1 < u) :
    |primeCosineTest β u| ≤ 1 / (u * Real.log u) := by
  have hu0 : 0 < u := by linarith
  have hlog : 0 < Real.log u := Real.log_pos hu
  rw [primeCosineTest, abs_div, abs_of_pos (mul_pos (by linarith) (Real.log_pos hu))]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)

theorem abs_primeCosineTestDeriv_le (β : ℝ) {u : ℝ} (hu : 1 < u) (hlog1 : 1 ≤ Real.log u) :
    |primeCosineTestDeriv β u| ≤ (|β| + 2) / (u ^ 2 * Real.log u) := by
  have hlog : 0 < Real.log u := by linarith
  have hu0 : 0 < u := by linarith
  have hden : 0 < u ^ 2 * Real.log u := by positivity
  have hden2 : 0 < u ^ 2 * Real.log u ^ 2 := by positivity
  have h1 : |-β * Real.sin (β * Real.log u) / (u ^ 2 * Real.log u)| ≤
      |β| / (u ^ 2 * Real.log u) := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hden]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg β) (Real.abs_sin_le_one _)) hden.le
  have h2 : |Real.cos (β * Real.log u) * (Real.log u + 1) /
      (u ^ 2 * Real.log u ^ 2)| ≤ 2 / (u ^ 2 * Real.log u) := by
    rw [abs_div, abs_mul, abs_of_pos (by linarith : 0 < Real.log u + 1), abs_of_pos hden2]
    calc
      _ ≤ (Real.log u + 1) / (u ^ 2 * Real.log u ^ 2) :=
        div_le_div_of_nonneg_right
          (mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)) hden2.le
      _ ≤ _ := by
        apply (div_le_div_iff₀ hden2 hden).mpr
        nlinarith [mul_nonneg (show 0 ≤ u ^ 2 * Real.log u by positivity) (show 0 ≤ Real.log u - 1 by linarith)]
  have hnorm : |(-β * Real.sin (β * Real.log u) / (u ^ 2 * Real.log u)) -
      (Real.cos (β * Real.log u) * (Real.log u + 1) / (u ^ 2 * Real.log u ^ 2))| ≤
      |-β * Real.sin (β * Real.log u) / (u ^ 2 * Real.log u)| +
        |Real.cos (β * Real.log u) * (Real.log u + 1) / (u ^ 2 * Real.log u ^ 2)| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le
      (-β * Real.sin (β * Real.log u) / (u ^ 2 * Real.log u))
      (Real.cos (β * Real.log u) * (Real.log u + 1) / (u ^ 2 * Real.log u ^ 2))
  have h := hnorm.trans (add_le_add h1 h2)
  simpa only [primeCosineTestDeriv, ← add_div] using h

theorem integral_reciprocal_log_power (A : ℕ) (hA : 1 ≤ A) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) :
    (∫ u : ℝ in a..b, 1 / (u * Real.log u ^ (A + 1))) =
      1 / ((A : ℝ) * Real.log a ^ A) - 1 / ((A : ℝ) * Real.log b ^ A) := by
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hcont : ContinuousOn (fun u : ℝ => 1 / (u * Real.log u ^ (A + 1))) (Set.Icc a b) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans zero_lt_one (ha.trans_le hu.1))
    have hlog0 : Real.log u ≠ 0 := (Real.log_pos (ha.trans_le hu.1)).ne'
    have hd : u * Real.log u ^ (A + 1) ≠ 0 := mul_ne_zero hu0 (pow_ne_zero _ hlog0)
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => -(Real.log u ^ (-(A : ℝ))) / A)
    (f' := fun u : ℝ => 1 / (u * Real.log u ^ (A + 1))) (a := a) (b := b)
    (fun u hu => by
      have huI : u ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hu
      have hu' : 1 < u := ha.trans_le huI.1
      have hu0 : u ≠ 0 := ne_of_gt (lt_trans zero_lt_one hu')
      have hlog : 0 < Real.log u := Real.log_pos hu'
      have h := (((Real.hasDerivAt_log hu0).rpow_const
        (p := -(A : ℝ)) (Or.inl hlog.ne')).neg).div_const (A : ℝ)
      convert h using 1
      dsimp only
      rw [Real.rpow_sub hlog, Real.rpow_neg hlog.le, Real.rpow_natCast, Real.rpow_one, pow_succ]
      field_simp)
    (hcont.intervalIntegrable_of_Icc hab)
  dsimp only at hint
  rw [Real.rpow_neg (Real.log_pos ha).le, Real.rpow_natCast,
    Real.rpow_neg (Real.log_pos (ha.trans_le hab)).le, Real.rpow_natCast] at hint
  convert hint using 1
  ring

theorem prime_cosine_abel_error (β : ℝ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
      Real.cos (β * Real.log p) / p) -
        (∫ u : ℝ in a..b, primeCosineTest β u) =
      primeCosineTest β b * (Chebyshev.theta b - b) -
        primeCosineTest β a * (Chebyshev.theta a - a) -
          ∫ u : ℝ in a..b, primeCosineTestDeriv β u * (Chebyshev.theta u - u) := by
  have h := prime_weighted_abel_error (lt_trans zero_lt_one ha).le hab
    (fun u hu => hasDerivAt_primeCosineTest β (ha.trans_le hu.1))
    (continuousOn_primeCosineTestDeriv β ha)
  have hsum : (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
      primeCosineTest β p * Real.log p) =
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.cos (β * Real.log p) / p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    dsimp [primeCosineTest]
    field_simp [(Real.log_pos hp1).ne']
  rwa [hsum] at h

/-- Oscillatory reciprocal-prime sums are approximated by their actual
integrals, uniformly in frequency and in both real endpoints. The PNT
estimate is discharged, not a premise of this consumer. -/
theorem exists_prime_cosine_integral_error (A : ℕ) (hA : 1 ≤ A) :
    ∃ X : ℝ, 3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ a b β : ℝ, X ≤ a → a ≤ b →
      |(∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
          Real.cos (β * Real.log p) / p) -
        (∫ u : ℝ in a..b, primeCosineTest β u)| ≤ (|β| + 4) / Real.log a ^ A := by
  obtain ⟨X₀, hX₀, htheta⟩ := exists_theta_logarithmic_error A
  let X := max X₀ (Real.exp 1)
  have hX : 3 ≤ X := hX₀.trans (le_max_left _ _)
  have hX0 : 0 < X := by linarith
  have hlogX : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_max_right X₀ (Real.exp 1))
    simpa only [Real.log_exp] using h
  refine ⟨X, hX, hlogX, ?_⟩
  intro a b β ha hab
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hloga : 1 ≤ Real.log a := hlogX.trans (Real.log_le_log hX0 ha)
  have hlogapos : 0 < Real.log a := by linarith
  have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hlocal (u : ℝ) (hu : u ∈ Set.Icc a b) : |Chebyshev.theta u - u| ≤ u / Real.log u ^ A :=
    htheta u ((le_max_left X₀ _).trans (ha.trans hu.1))
  have hloglocal (u : ℝ) (hu : u ∈ Set.Icc a b) : 1 ≤ Real.log u :=
    hloga.trans (Real.log_le_log ha0 hu.1)
  have hend (u : ℝ) (hu : u ∈ Set.Icc a b) :
      |primeCosineTest β u * (Chebyshev.theta u - u)| ≤ 1 / Real.log a ^ A := by
    have hu1 := ha1.trans_le hu.1
    have hu0 : 0 < u := by linarith
    have hlog : 0 < Real.log u := by linarith [hloglocal u hu]
    rw [abs_mul]
    calc
      _ ≤ (1 / (u * Real.log u)) * (u / Real.log u ^ A) :=
        mul_le_mul (abs_primeCosineTest_le β hu1) (hlocal u hu) (abs_nonneg _) (by positivity)
      _ = 1 / (Real.log u * Real.log u ^ A) := by field_simp
      _ ≤ 1 / Real.log a ^ A := by
        apply one_div_le_one_div_of_le (pow_pos hlogapos A)
        calc
          Real.log a ^ A ≤ Real.log u ^ A :=
            pow_le_pow_left₀ hlogapos.le (Real.log_le_log ha0 hu.1) _
          _ ≤ Real.log u * Real.log u ^ A :=
            le_mul_of_one_le_left (by positivity) (hloglocal u hu)
  have hdcont := continuousOn_primeCosineTestDeriv β (b := b) ha1
  have herrint : IntervalIntegrable
      (fun u => primeCosineTestDeriv β u * (Chebyshev.theta u - u)) volume a b := by
    simpa only [mul_comm] using
      (Chebyshev.theta_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable a b)).mul_continuousOn
        (hdcont.mono (by rw [Set.uIcc_of_le hab]))
  have hmajorant : ContinuousOn
      (fun u : ℝ => (|β| + 2) / (u * Real.log u ^ (A + 1))) (Set.Icc a b) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (ha0.trans_le hu.1)
    have hl0 : Real.log u ≠ 0 := (Real.log_pos (ha1.trans_le hu.1)).ne'
    have hd : u * Real.log u ^ (A + 1) ≠ 0 := mul_ne_zero hu0 (pow_ne_zero _ hl0)
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hi := intervalIntegral.integral_mono_on hab herrint.norm
    (hmajorant.intervalIntegrable_of_Icc hab) (fun u hu => by
      rw [Real.norm_eq_abs, abs_mul]
      have hu1 := ha1.trans_le hu.1
      have hu0 : 0 < u := by linarith
      have hlog : 0 < Real.log u := by linarith [hloglocal u hu]
      calc
        _ ≤ ((|β| + 2) / (u ^ 2 * Real.log u)) * (u / Real.log u ^ A) :=
          mul_le_mul (abs_primeCosineTestDeriv_le β hu1 (hloglocal u hu))
            (hlocal u hu) (abs_nonneg _) (by positivity)
        _ = _ := by
          rw [pow_succ (Real.log u) A]
          field_simp)
  have heval : (∫ u : ℝ in a..b, (|β| + 2) / (u * Real.log u ^ (A + 1))) =
      (|β| + 2) * (1 / ((A : ℝ) * Real.log a ^ A) - 1 / ((A : ℝ) * Real.log b ^ A)) := by
    simp_rw [div_eq_mul_one_div (|β| + 2)]
    rw [intervalIntegral.integral_const_mul, integral_reciprocal_log_power A hA ha1 hab]
  rw [heval] at hi
  have hibound : |∫ u : ℝ in a..b, primeCosineTestDeriv β u * (Chebyshev.theta u - u)| ≤
      (|β| + 2) / Real.log a ^ A := by
    have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab
      (f := fun u => primeCosineTestDeriv β u * (Chebyshev.theta u - u))
    rw [Real.norm_eq_abs] at hn
    have hrec : 1 / ((A : ℝ) * Real.log a ^ A) ≤ 1 / Real.log a ^ A :=
      one_div_le_one_div_of_le (pow_pos hlogapos A) (le_mul_of_one_le_left (by positivity) hAreal)
    have hnonneg : 0 ≤ 1 / ((A : ℝ) * Real.log b ^ A) := by
      have : 0 < Real.log b := Real.log_pos (ha1.trans_le hab)
      positivity
    have hm := mul_le_mul_of_nonneg_left hrec (show 0 ≤ |β| + 2 by positivity)
    have hm' := mul_nonneg (show 0 ≤ |β| + 2 by positivity) hnonneg
    rw [div_eq_mul_one_div (|β| + 2)]
    nlinarith [hn.trans hi]
  rw [prime_cosine_abel_error β ha1 hab]
  have h1 := norm_sub_le
    (primeCosineTest β b * (Chebyshev.theta b - b))
    (primeCosineTest β a * (Chebyshev.theta a - a))
  have h2 := norm_sub_le
    (primeCosineTest β b * (Chebyshev.theta b - b) - primeCosineTest β a * (Chebyshev.theta a - a))
    (∫ u : ℝ in a..b, primeCosineTestDeriv β u * (Chebyshev.theta u - u))
  simp only [Real.norm_eq_abs] at h1 h2
  have hb := hend b ⟨hab, le_rfl⟩
  have ha' := hend a ⟨le_rfl, hab⟩
  have hid : 1 / Real.log a ^ A + 1 / Real.log a ^ A +
      (|β| + 2) / Real.log a ^ A = (|β| + 4) / Real.log a ^ A := by ring
  linarith

theorem integral_primeCosineTest_zero {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ u : ℝ in a..b, primeCosineTest 0 u) = Real.log (Real.log b) - Real.log (Real.log a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    have huI : u ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hu
    have hu1 := ha.trans_le huI.1
    have h := (Real.hasDerivAt_log (ne_of_gt (lt_trans zero_lt_one hu1))).log
      (Real.log_pos hu1).ne'
    convert h using 1
    simp [primeCosineTest, div_eq_mul_inv, mul_comm]
  · exact (show ContinuousOn (primeCosineTest 0) (Set.Icc a b) from fun u hu =>
      (hasDerivAt_primeCosineTest 0 (ha.trans_le hu.1)).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc hab

/-- Cancellation of a nonzero logarithmic frequency in the continuous
prime model. Both boundary terms and the integrable remainder are retained. -/
theorem abs_integral_primeCosineTest_le {β a b : ℝ} (hβ : β ≠ 0)
    (ha : 1 < a) (hab : a ≤ b) :
    |∫ u : ℝ in a..b, primeCosineTest β u| ≤ 3 / (|β| * Real.log a) := by
  let F := fun u : ℝ => Real.sin (β * Real.log u) / (β * Real.log u)
  let R := fun u : ℝ => Real.sin (β * Real.log u) / (β * u * Real.log u ^ 2)
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hβ0 : 0 < |β| := abs_pos.mpr hβ
  have hRcont : ContinuousOn R (Set.Icc a b) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (ha0.trans_le hu.1)
    have hl0 : Real.log u ≠ 0 := (Real.log_pos (ha.trans_le hu.1)).ne'
    have hd : β * u * Real.log u ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero hβ hu0) (pow_ne_zero _ hl0)
    apply ContinuousAt.continuousWithinAt
    dsimp [R]
    fun_prop
  have htest : ContinuousOn (primeCosineTest β) (Set.Icc a b) := fun u hu =>
    (hasDerivAt_primeCosineTest β (ha.trans_le hu.1)).continuousAt.continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (f' := fun u => primeCosineTest β u - R u) (a := a) (b := b)
    (fun u hu => by
      have huI : u ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hu
      have hu0 : u ≠ 0 := ne_of_gt (ha0.trans_le huI.1)
      have hl0 : Real.log u ≠ 0 := (Real.log_pos (ha.trans_le huI.1)).ne'
      have h := (((Real.hasDerivAt_log hu0).const_mul β).sin).div
        ((Real.hasDerivAt_log hu0).const_mul β) (mul_ne_zero hβ hl0)
      convert h using 1
      dsimp [primeCosineTest, R]
      field_simp)
    ((htest.sub hRcont).intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_sub (htest.intervalIntegrable_of_Icc hab)
    (hRcont.intervalIntegrable_of_Icc hab)] at hFTC
  have hF (u : ℝ) (hu : u ∈ Set.Icc a b) : |F u| ≤ 1 / (|β| * Real.log a) := by
    have hlog : 0 < Real.log u := Real.log_pos (ha.trans_le hu.1)
    dsimp [F]
    rw [abs_div, abs_mul, abs_of_pos hlog]
    calc
      _ ≤ 1 / (|β| * Real.log u) :=
        div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
      _ ≤ _ := one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (Real.log_le_log ha0 hu.1) hβ0.le)
  have hmajCont : ContinuousOn (fun u : ℝ => 1 / (|β| * u * Real.log u ^ 2)) (Set.Icc a b) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (ha0.trans_le hu.1)
    have hl0 : Real.log u ≠ 0 := (Real.log_pos (ha.trans_le hu.1)).ne'
    have hd : |β| * u * Real.log u ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero hβ0.ne' hu0) (pow_ne_zero _ hl0)
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (hRcont.intervalIntegrable_of_Icc hab).norm (hmajCont.intervalIntegrable_of_Icc hab)
    (fun u hu => by
      have hu0 : 0 < u := ha0.trans_le hu.1
      have hl0 : 0 < Real.log u := Real.log_pos (ha.trans_le hu.1)
      dsimp [R]
      rw [abs_div, abs_mul, abs_mul, abs_of_pos hu0, abs_of_pos (sq_pos_of_pos hl0)]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity))
  have hev : (∫ u : ℝ in a..b, 1 / (|β| * u * Real.log u ^ 2)) =
      (1 / |β|) * (1 / Real.log a - 1 / Real.log b) := by
    have hid (u : ℝ) : 1 / (|β| * u * Real.log u ^ 2) =
        (1 / |β|) * (1 / (u * Real.log u ^ 2)) := by ring
    simp_rw [hid]
    rw [intervalIntegral.integral_const_mul]
    simpa using congrArg (fun z : ℝ => (1 / |β|) * z)
      (integral_reciprocal_log_power 1 (by omega) ha hab)
  rw [hev] at hi
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab (f := R)
  rw [Real.norm_eq_abs] at hn
  have hRbound : |∫ u : ℝ in a..b, R u| ≤ 1 / (|β| * Real.log a) := by
    have hbpos : 0 < Real.log b := Real.log_pos (ha.trans_le hab)
    have hid : 1 / (|β| * Real.log a) = (1 / |β|) * (1 / Real.log a) := by ring
    rw [hid]
    have hnonneg : 0 ≤ (1 / |β|) * (1 / Real.log b) := by positivity
    nlinarith [hn.trans hi]
  have hId : (∫ u : ℝ in a..b, primeCosineTest β u) = F b - F a + ∫ u : ℝ in a..b, R u := by
    linarith
  rw [hId]
  have h1 := norm_sub_le (F b) (F a)
  have h2 := norm_add_le (F b - F a) (∫ u : ℝ in a..b, R u)
  simp only [Real.norm_eq_abs] at h1 h2
  have hfa := hF a ⟨le_rfl, hab⟩
  have hfb := hF b ⟨hab, le_rfl⟩
  have hid : 3 / (|β| * Real.log a) = 3 * (1 / (|β| * Real.log a)) := by ring
  rw [hid]
  linarith

/-- The actual prime cosine correlation has a leading coefficient strictly
below two thirds. The threshold depends only on the chosen logarithmic
saving, not the two endpoints or frequency. -/
theorem exists_prime_absolute_cosine_bound (A : ℕ) (hA : 1 ≤ A) :
    ∃ X : ℝ, 3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ a b β : ℝ, X ≤ a → a ≤ b →
      1 ≤ |β| * Real.log a → |β| ≤ Real.log a ^ A →
      (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
        |Real.cos (β * Real.log p / 2)| / p) ≤
          (75 / 113 : ℝ) * (Real.log (Real.log b) - Real.log (Real.log a)) + 8 := by
  classical
  obtain ⟨X, hX, hlogX, herror⟩ := exists_prime_cosine_integral_error A hA
  refine ⟨X, hX, hlogX, ?_⟩
  intro a b β ha hab hfreq hfreqUpper
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hloga : 1 ≤ Real.log a := hlogX.trans
    (Real.log_le_log (by linarith : 0 < X) ha)
  have hlogapos : 0 < Real.log a := by linarith
  have hP : 1 ≤ Real.log a ^ A := one_le_pow₀ hloga
  have hP0 : 0 < Real.log a ^ A := by positivity
  have hβ : β ≠ 0 := by intro h; norm_num [h] at hfreq
  let P := (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime
  let S := fun γ : ℝ => ∑ p ∈ P, Real.cos (γ * Real.log p) / p
  have hosc (k : ℝ) (hk : 1 ≤ k) (hk3 : k ≤ 3) : |S (k * β)| ≤ 10 := by
    have hk0 : 0 < k := by linarith
    have hkb : k * β ≠ 0 := mul_ne_zero hk0.ne' hβ
    have he := herror a b (k * β) ha hab
    have hi := abs_integral_primeCosineTest_le hkb ha1 hab
    have hprod : 1 ≤ |k * β| * Real.log a := by
      rw [abs_mul, abs_of_pos hk0]
      have hm := mul_le_mul_of_nonneg_left hk (show 0 ≤ |β| * Real.log a by positivity)
      nlinarith
    have hir : 3 / (|k * β| * Real.log a) ≤ 3 := by
      apply (div_le_iff₀ (by positivity : 0 < |k * β| * Real.log a)).mpr
      linarith
    have her : (|k * β| + 4) / Real.log a ^ A ≤ 7 := by
      rw [abs_mul, abs_of_pos hk0]
      apply (div_le_iff₀ hP0).mpr
      have hm := mul_le_mul_of_nonneg_left hfreqUpper hk0.le
      nlinarith
    have hnorm := norm_sub_norm_le (S (k * β))
      (∫ u : ℝ in a..b, primeCosineTest (k * β) u)
    simp only [Real.norm_eq_abs] at hnorm
    change |S (k * β) - (∫ u : ℝ in a..b, primeCosineTest (k * β) u)| ≤ _ at he
    linarith
  have hmass : (∑ p ∈ P, (1 : ℝ) / p) ≤
      Real.log (Real.log b) - Real.log (Real.log a) + 4 := by
    have he := herror a b 0 ha hab
    rw [integral_primeCosineTest_zero ha1 hab] at he
    simp only [zero_mul, Real.cos_zero, abs_zero, zero_add] at he
    have hfrac : 4 / Real.log a ^ A ≤ 4 := by
      apply (div_le_iff₀ hP0).mpr
      linarith
    have hupper := (abs_le.mp he).2
    change (∑ p ∈ P, (1 : ℝ) / p) - _ ≤ _ at hupper
    linarith
  have hmajorant : (∑ p ∈ P, |Real.cos (β * Real.log p / 2)| / p) ≤
      (75 / 113 : ℝ) * (∑ p ∈ P, (1 : ℝ) / p) + (175 / 452 : ℝ) * S β -
        (5 / 113 : ℝ) * S (2 * β) + (5 / 452 : ℝ) * S (3 * β) := by
    have hp (p : ℕ) (_hp : p ∈ P) :
        |Real.cos (β * Real.log p / 2)| / p ≤
          (75 / 113 : ℝ) * (1 / p) + (175 / 452 : ℝ) * (Real.cos (β * Real.log p) / p) -
            (5 / 113 : ℝ) * (Real.cos ((2 * β) * Real.log p) / p) +
              (5 / 452 : ℝ) * (Real.cos ((3 * β) * Real.log p) / p) := by
      have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
      have hh := div_le_div_of_nonneg_right
        (abs_cos_le_three_frequency_majorant (β * Real.log p / 2)) hp0
      rw [show 2 * (β * Real.log p / 2) = β * Real.log p by ring,
        show 4 * (β * Real.log p / 2) = (2 * β) * Real.log p by ring,
        show 6 * (β * Real.log p / 2) = (3 * β) * Real.log p by ring] at hh
      convert hh using 1
      ring
    have hh := Finset.sum_le_sum hp
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
    exact hh
  have h1 := (abs_le.mp (by simpa using hosc 1 (by norm_num) (by norm_num))).2
  have h2 := (abs_le.mp (hosc 2 (by norm_num) (by norm_num))).1
  have h3 := (abs_le.mp (hosc 3 (by norm_num) (by norm_num))).2
  change (∑ p ∈ P, |Real.cos (β * Real.log p / 2)| / p) ≤ _
  linarith

theorem zetaTerm_re_eq_cos (τ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (zetaTerm τ n).re = Real.cos (τ * Real.log n) := by
  rw [zetaTerm_eq_exp τ hn, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_self, Real.exp_zero,
    mul_one, add_zero, one_mul]

theorem prime_phase_pair_re_le (τ υ : ℝ) {p : ℕ} (hp : p.Prime) :
    (zetaTerm τ p).re + (zetaTerm υ p).re ≤
      2 * |Real.cos ((τ - υ) * Real.log p / 2)| := by
  rw [zetaTerm_re_eq_cos τ hp.ne_zero, zetaTerm_re_eq_cos υ hp.ne_zero, Real.cos_add_cos]
  have h := le_abs_self
    (Real.cos ((τ * Real.log p + υ * Real.log p) / 2) *
      Real.cos ((τ * Real.log p - υ * Real.log p) / 2))
  rw [abs_mul] at h
  have hc := mul_le_of_le_one_left
    (abs_nonneg (Real.cos ((τ * Real.log p - υ * Real.log p) / 2)))
    (Real.abs_cos_le_one ((τ * Real.log p + υ * Real.log p) / 2))
  rw [show (τ - υ) * Real.log p = τ * Real.log p - υ * Real.log p by ring]
  nlinarith

/-- The same finite prime distance occurring in the source controls two
frequencies together. Discarding the low-prime range is justified by
nonnegativity, not by changing the distance's definition. -/
theorem primePhaseDistance_pair_lower_tail (a x τ υ : ℝ) :
    2 * ((∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) -
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊x⌋₊).filter Nat.Prime,
        |Real.cos ((τ - υ) * Real.log p / 2)| / p) ≤
      primePhaseDistance x τ + primePhaseDistance x υ := by
  classical
  let P := (Finset.Ioc ⌊a⌋₊ ⌊x⌋₊).filter Nat.Prime
  let Q := (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime
  let d := fun p : ℕ => ((1 - (zetaTerm τ p).re) / p + (1 - (zetaTerm υ p).re) / p)
  have hPQ : P ⊆ Q := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hmem.2.pos, (Finset.mem_Ioc.mp hmem.1).2⟩, hmem.2⟩
  have hnonneg (p : ℕ) (hp : p ∈ Q) : 0 ≤ d p := by
    have hp0 := (Finset.mem_filter.mp hp).2.pos
    have hτ := Complex.re_le_norm (zetaTerm τ p)
    have hυ := Complex.re_le_norm (zetaTerm υ p)
    rw [norm_zetaTerm τ hp0] at hτ
    rw [norm_zetaTerm υ hp0] at hυ
    exact add_nonneg (div_nonneg (sub_nonneg.mpr hτ) (Nat.cast_nonneg p))
      (div_nonneg (sub_nonneg.mpr hυ) (Nat.cast_nonneg p))
  have hpoint (p : ℕ) (hp : p ∈ P) :
      2 * ((1 : ℝ) / p - |Real.cos ((τ - υ) * Real.log p / 2)| / p) ≤ d p := by
    have hr := prime_phase_pair_re_le τ υ (Finset.mem_filter.mp hp).2
    have hd := div_le_div_of_nonneg_right hr (Nat.cast_nonneg p)
    dsimp [d]
    simp only [add_div] at hd
    calc
      _ = (2 - 2 * |Real.cos ((τ - υ) * Real.log p / 2)|) / p := by ring
      _ ≤ (2 - ((zetaTerm τ p).re + (zetaTerm υ p).re)) / p :=
        div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg p)
      _ = _ := by ring
  have hs := (Finset.sum_le_sum hpoint).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hPQ (fun p hp _ => hnonneg p hp))
  simpa only [d, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    primePhaseDistance, P, Q] using hs

/-- Quantitative two-frequency repulsion for the actual source distances,
from the proved prime-correlation estimate. -/
theorem exists_primePhaseDistance_pair_lower (A : ℕ) (hA : 1 ≤ A) :
    ∃ X : ℝ, 3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ a x τ υ : ℝ, X ≤ a → a ≤ x →
      1 ≤ |τ - υ| * Real.log a → |τ - υ| ≤ Real.log a ^ A →
      (76 / 113 : ℝ) * (Real.log (Real.log x) - Real.log (Real.log a)) - 24 ≤
        primePhaseDistance x τ + primePhaseDistance x υ := by
  obtain ⟨X₁, hX₁, hlog₁, hcos⟩ := exists_prime_absolute_cosine_bound A hA
  obtain ⟨X₂, hX₂, _hlog₂, herror⟩ := exists_prime_cosine_integral_error A hA
  refine ⟨max X₁ X₂, hX₁.trans (le_max_left _ _),
    hlog₁.trans (Real.log_le_log (by linarith : 0 < X₁) (le_max_left _ _)), ?_⟩
  intro a x τ υ ha hax hfreq hfreqUpper
  have ha1 : 1 < a := by linarith [le_max_left X₁ X₂]
  have hloga : 1 ≤ Real.log a := hlog₁.trans
    (Real.log_le_log (by linarith : 0 < X₁) ((le_max_left _ _).trans ha))
  have hp : 1 ≤ Real.log a ^ A := one_le_pow₀ hloga
  have hc := hcos a x (τ - υ) ((le_max_left _ _).trans ha) hax hfreq hfreqUpper
  have he := herror a x 0 ((le_max_right _ _).trans ha) hax
  rw [integral_primeCosineTest_zero ha1 hax] at he
  simp only [zero_mul, Real.cos_zero, abs_zero, zero_add] at he
  have hmass := (abs_le.mp he).1
  have hfrac : 4 / Real.log a ^ A ≤ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.log a ^ A)).mpr
    linarith
  have hd := primePhaseDistance_pair_lower_tail a x τ υ
  linarith

/-- An actual two-point zeta bound on the original source abscissa. The
frequency difference, finite cutoff and PNT scale are linked in this
consumer; there is no assumed Euler-product or correlation bound. -/
theorem exists_two_point_zeta_bound (A : ℕ) (hA : 1 ≤ A) :
    ∃ X : ℝ, 3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ a x τ υ : ℝ, X ≤ a → a ≤ x →
      1 ≤ |τ - υ| * Real.log a → |τ - υ| ≤ Real.log a ^ A →
      ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) - (τ : ℂ) * I)‖ *
        ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) - (υ : ℂ) * I)‖ ≤
          (1 + Real.log x) ^ 2 * Real.exp
            (8 * (Real.log 4 + 4) + 24 -
              (76 / 113 : ℝ) * (Real.log (Real.log x) - Real.log (Real.log a))) := by
  obtain ⟨X, hX, hlogX, hpair⟩ := exists_primePhaseDistance_pair_lower A hA
  refine ⟨X, hX, hlogX, ?_⟩
  intro a x τ υ ha hax hfreq hfreqUpper
  have hx : 1 < x := by linarith
  have hlog : 1 ≤ Real.log x := hlogX.trans
    (Real.log_le_log (by linarith : 0 < X) (ha.trans hax))
  have hτ := norm_zeta_shift_le_primePhaseDistance x τ hx hlog
  have hυ := norm_zeta_shift_le_primePhaseDistance x υ hx hlog
  have hmul := mul_le_mul hτ hυ (norm_nonneg _) (by positivity)
  have hd := hpair a x τ υ ha hax hfreq hfreqUpper
  have he : Real.exp (8 * (Real.log 4 + 4) - (primePhaseDistance x τ + primePhaseDistance x υ)) ≤
      Real.exp (8 * (Real.log 4 + 4) + 24 -
        (76 / 113 : ℝ) * (Real.log (Real.log x) - Real.log (Real.log a))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hid :
      ((1 + Real.log x) * Real.exp (4 * (Real.log 4 + 4) - primePhaseDistance x τ)) *
        ((1 + Real.log x) * Real.exp (4 * (Real.log 4 + 4) - primePhaseDistance x υ)) =
      (1 + Real.log x) ^ 2 *
        Real.exp (8 * (Real.log 4 + 4) - (primePhaseDistance x τ + primePhaseDistance x υ)) := by
    rw [mul_mul_mul_comm, ← Real.exp_add]
    congr 1
    · ring
    · congr 1; ring
  rw [hid] at hmul
  exact hmul.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))

/-- The source maximization condition converts the actual two-point product
into an off-frequency bound for the same selected twist. -/
theorem exists_maximizingTwist_off_frequency_bound (A : ℕ) (hA : 1 ≤ A) :
    ∃ X : ℝ, 3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ a x t t₀ y : ℝ, X ≤ a → a ≤ x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀ + y| ≤ Real.log x → 1 ≤ |y| * Real.log a → |y| ≤ Real.log a ^ A →
      ‖riemannZeta (twistZetaPoint x t (t₀ + y))‖ ≤
        (1 + Real.log x) * Real.exp
          (4 * (Real.log 4 + 4) + 12 -
            (38 / 113 : ℝ) * (Real.log (Real.log x) - Real.log (Real.log a))) := by
  obtain ⟨X, hX, hlogX, hpair⟩ := exists_two_point_zeta_bound A hA
  refine ⟨X, hX, hlogX, ?_⟩
  intro a x t t₀ y ha hax hmax hy hfreq hfreqUpper
  have hdiff : |(t - (t₀ + y)) - (t - t₀)| = |y| := by
    rw [show (t - (t₀ + y)) - (t - t₀) = -y by ring, abs_neg]
  have hp := hpair a x (t - (t₀ + y)) (t - t₀) ha hax
    (by simpa only [hdiff] using hfreq) (by simpa only [hdiff] using hfreqUpper)
  have hpoint (u : ℝ) :
      (((1 + 1 / Real.log x : ℝ) : ℂ) - ((t - u : ℝ) : ℂ) * I) =
        twistZetaPoint x t u := by
    simp only [twistZetaPoint, Complex.ofReal_sub]
    ring
  rw [hpoint, hpoint] at hp
  have hs := (mul_le_mul_of_nonneg_left (hmax (t₀ + y) hy) (norm_nonneg _)).trans hp
  let E := 4 * (Real.log 4 + 4) + 12 -
    (38 / 113 : ℝ) * (Real.log (Real.log x) - Real.log (Real.log a))
  have hE : (Real.exp E) ^ 2 = Real.exp
      (8 * (Real.log 4 + 4) + 24 -
        (76 / 113 : ℝ) * (Real.log (Real.log x) - Real.log (Real.log a))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [E]
    ring
  have hxlog : 0 ≤ Real.log x := (Real.log_pos (by linarith : 1 < x)).le
  have hnonneg : 0 ≤ (1 + Real.log x) * Real.exp E := by positivity
  have hsq : ((1 + Real.log x) * Real.exp E) ^ 2 =
      (1 + Real.log x) ^ 2 * Real.exp
        (8 * (Real.log 4 + 4) + 24 -
          (76 / 113 : ℝ) * (Real.log (Real.log x) - Real.log (Real.log a))) := by
    rw [mul_pow, hE]
  change _ ≤ (1 + Real.log x) * Real.exp E
  nlinarith [hsq, norm_nonneg (riemannZeta (twistZetaPoint x t (t₀ + y)))]

/-- The prime cutoff is chosen internally from the actual frequency and
the source scale. All PNT frequency restrictions are discharged. -/
theorem exists_maximizingTwist_uniform_frequency_bound (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ y : ℝ, 1 < x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 1 / Real.log x ≤ |y| → |y| ≤ Real.log x / 2 →
      ‖riemannZeta (twistZetaPoint x t (t₀ + y))‖ ≤
        (1 + Real.log x) * Real.exp
          (4 * (Real.log 4 + 4) + 12 - (38 / 113 : ℝ) *
            (Real.log (Real.log x) -
              Real.log (max B (max (1 / |y|) ((Real.log x) ^ ((A : ℝ)⁻¹)))))) := by
  obtain ⟨X, hX, hlogX, hbound⟩ := exists_maximizingTwist_off_frequency_bound A hA
  refine ⟨Real.log X, hlogX, ?_⟩
  intro x t t₀ y hx hscale hmax ht₀ hyLower hyUpper
  let L := Real.log x
  let B := max (Real.log X) (max (1 / |y|) (L ^ ((A : ℝ)⁻¹)))
  have hL : 1 ≤ L := hlogX.trans hscale
  have hLpos : 0 < L := by linarith
  have hypos : 0 < |y| := (one_div_pos.mpr hLpos).trans_le hyLower
  have hB₁ : Real.log X ≤ B := le_max_left _ _
  have hB₂ : 1 / |y| ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hB₃ : L ^ ((A : ℝ)⁻¹) ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hBpos : 0 < B := by linarith
  have hAL : (A : ℝ) ≥ 1 := by exact_mod_cast hA
  have hBL : B ≤ L := by
    apply max_le hscale
    apply max_le
    · exact (div_le_iff₀ hypos).mpr (by
        simpa only [mul_comm] using (div_le_iff₀ hLpos).mp hyLower)
    · exact Real.rpow_le_self_of_one_le hL ((inv_le_one₀ (by positivity)).mpr hAL)
  have haX : X ≤ Real.exp B := by
    rw [← Real.exp_log (by linarith : 0 < X)]
    exact Real.exp_le_exp.mpr hB₁
  have hax : Real.exp B ≤ x := by
    rw [← Real.exp_log (by linarith : 0 < x)]
    exact Real.exp_le_exp.mpr hBL
  have hfreq : 1 ≤ |y| * B := by
    have hh := (div_le_iff₀ hypos).mp hB₂
    nlinarith
  have hpower : L ≤ B ^ A := by
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hLpos.le _) hB₃ A
    rw [Real.rpow_inv_natCast_pow hLpos.le (by omega)] at hp
    exact hp
  have hy : |t₀ + y| ≤ L := (abs_add_le _ _).trans (by linarith)
  have hh := hbound (Real.exp B) x t t₀ y haX hax hmax hy
    (by simpa only [Real.log_exp] using hfreq)
    (by simpa only [Real.log_exp] using (show |y| ≤ B ^ A by linarith))
  simpa only [Real.log_exp] using hh

/-- The source-line damping is retained even at zero frequency. The bound
combines the global unit-disk estimate with the small-exponent estimate. -/
theorem norm_damped_difference_factor_le {d b : ℝ} (hd : 0 ≤ d) (hb : 0 ≤ b) (y : ℝ) :
    ‖1 - Complex.exp ((-d : ℂ) + ((-b * y : ℝ) : ℂ) * I)‖ ≤
      min 2 (2 * (d + b * |y|)) := by
  let z : ℂ := (-d : ℂ) + ((-b * y : ℝ) : ℂ) * I
  have hre : z.re = -d := by simp [z]
  have he : ‖Complex.exp z‖ ≤ 1 := by
    rw [Complex.norm_exp, hre]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have htwo : ‖1 - Complex.exp z‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (Complex.exp z)
    rw [norm_one] at h
    linarith
  have hz : ‖z‖ ≤ d + b * |y| := by
    have h := norm_add_le (-d : ℂ) (((-b * y : ℝ) : ℂ) * I)
    simpa only [norm_neg, Complex.norm_real, Real.norm_of_nonneg hd, norm_mul,
      Complex.norm_I, mul_one, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hb] using h
  refine le_min htwo ?_
  by_cases hsmall : d + b * |y| ≤ 1
  · have h := Complex.norm_exp_sub_one_le (hz.trans hsmall)
    rw [norm_sub_rev] at h
    exact h.trans (mul_le_mul_of_nonneg_left hz (by norm_num))
  · exact htwo.trans (by linarith)

/-- Optimization of the internally chosen prime scale against a frequency
difference. This preserves the strict saving in the trigonometric mean. -/
theorem scaled_frequency_envelope_le {a D L v b κ : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hv : 0 < v) (ha : a ≤ D) (hb : b ≤ D)
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1) :
    (max a (1 / v) / L) ^ κ * min 1 (b * v) ≤ (D / L) ^ κ := by
  have hbase : 0 ≤ max a (1 / v) / L :=
    div_nonneg ((one_div_pos.mpr hv).le.trans (le_max_right _ _)) hL.le
  by_cases hinv : 1 / v ≤ D
  · exact (mul_le_of_le_one_right (Real.rpow_nonneg hbase _) (min_le_left _ _)).trans
      (Real.rpow_le_rpow hbase (div_le_div_of_nonneg_right (max_le ha hinv) hL.le) hκ)
  · have hDv : D * v ≤ 1 := ((lt_div_iff₀ hv).mp (lt_of_not_ge hinv)).le
    have hmax : max a (1 / v) = 1 / v := max_eq_right (ha.trans (le_of_lt (lt_of_not_ge hinv)))
    rw [hmax]
    have hmin : min 1 (b * v) ≤ (D * v) ^ κ :=
      ((min_le_right _ _).trans (mul_le_mul_of_nonneg_right hb hv.le)).trans
        (Real.self_le_rpow_of_le_one (mul_nonneg hD.le hv.le) hDv hκ₁)
    calc
      _ ≤ ((1 / v) / L) ^ κ * (D * v) ^ κ :=
        mul_le_mul_of_nonneg_left hmin (Real.rpow_nonneg (by positivity) _)
      _ = _ := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        field_simp

/-- Uniform control of the actual zeta dilation factor at the selected
source maximizer. The PNT cutoff and all frequency cases are discharged. -/
theorem exists_maximizingTwist_dilation_factor_bound (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b y : ℝ, 1 < x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → |y| ≤ Real.log x / 2 →
      ‖riemannZeta (twistZetaPoint x t (t₀ + y)) *
        (1 - Complex.exp (-((b / Real.log x : ℝ) : ℂ) + ((-b * y : ℝ) : ℂ) * I))‖ ≤
          4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
            (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) := by
  obtain ⟨B, hB, hfreq⟩ := exists_maximizingTwist_uniform_frequency_bound A hA
  refine ⟨B, hB, ?_⟩
  intro x t t₀ b y hx hscale hmax ht₀ hb hy
  let L := Real.log x
  let C := Real.exp (4 * (Real.log 4 + 4) + 12)
  let D := max B (max b (L ^ ((A : ℝ)⁻¹)))
  let κ : ℝ := 38 / 113
  have hL : 1 ≤ L := hB.trans hscale
  have hLpos : 0 < L := by linarith
  have hDpos : 0 < D := lt_of_lt_of_le (by linarith : 0 < B) (le_max_left _ _)
  have hbD : b ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hC : 1 ≤ C := Real.one_le_exp_iff.mpr (by positivity)
  have hCpos : 0 < C := Real.exp_pos _
  have hκ : 0 ≤ κ := by norm_num [κ]
  have hκ₁ : κ ≤ 1 := by norm_num [κ]
  have hd := norm_damped_difference_factor_le (div_nonneg hb hLpos.le) hb y
  have hd₂ := hd.trans (min_le_left _ _)
  have hdlin := hd.trans (min_le_right _ _)
  have hglobal : ‖riemannZeta (twistZetaPoint x t (t₀ + y))‖ ≤ 1 + L := by
    have hσ : 1 < 1 + 1 / L := lt_add_of_pos_right 1 (one_div_pos.mpr hLpos)
    have hh := (norm_tsum_logFrequency_le (zetaPhaseCoeff (1 + 1 / L) t)
      (summable_norm_zetaPhaseCoeff (1 + 1 / L) t hσ) (t₀ + y)).trans
        (tsum_norm_zetaPhaseCoeff_le (1 + 1 / L) t hσ)
    rw [tsum_zetaPhaseCoeff_phase (1 + 1 / L) t (t₀ + y) hσ] at hh
    simpa [twistZetaPoint, L] using hh
  rw [norm_mul]
  change _ ≤ 4 * C * (1 + L) * (D / L) ^ κ
  have hrpos : 0 ≤ (D / L) ^ κ := Real.rpow_nonneg (by positivity) _
  by_cases hDL : L ≤ D
  · have hr : 1 ≤ (D / L) ^ κ :=
      Real.one_le_rpow ((one_le_div hLpos).mpr hDL) hκ
    have hconst : 2 ≤ 4 * C * (D / L) ^ κ := by nlinarith
    calc
      _ ≤ (1 + L) * 2 := mul_le_mul hglobal hd₂ (norm_nonneg _) (by positivity)
      _ ≤ (1 + L) * (4 * C * (D / L) ^ κ) :=
        mul_le_mul_of_nonneg_left hconst (by positivity)
      _ = _ := by ring
  have hDL' : D ≤ L := (lt_of_not_ge hDL).le
  by_cases hsmall : |y| ≤ 1 / L
  · have hby : b * |y| ≤ b / L := by
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hsmall hb
    have hfactor : ‖1 - Complex.exp (-((b / L : ℝ) : ℂ) + ((-b * y : ℝ) : ℂ) * I)‖ ≤
        4 * b / L := hdlin.trans (by rw [mul_div_assoc]; linarith)
    have hr : b / L ≤ (D / L) ^ κ :=
      (div_le_div_of_nonneg_right hbD hLpos.le).trans
        (Real.self_le_rpow_of_le_one (by positivity) ((div_le_one hLpos).mpr hDL') hκ₁)
    have hf : 4 * b / L ≤ 4 * C * (D / L) ^ κ := by
      rw [mul_div_assoc]
      nlinarith
    calc
      _ ≤ (1 + L) * (4 * b / L) :=
        mul_le_mul hglobal hfactor (norm_nonneg _) (by positivity)
      _ ≤ (1 + L) * (4 * C * (D / L) ^ κ) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := by ring
  have hypos : 0 < |y| := (one_div_pos.mpr hLpos).trans (lt_of_not_ge hsmall)
  let H := max B (max (1 / |y|) (L ^ ((A : ℝ)⁻¹)))
  have hHpos : 0 < H := lt_of_lt_of_le (by linarith : 0 < B) (le_max_left _ _)
  have hz := hfreq x t t₀ y hx hscale hmax ht₀ (lt_of_not_ge hsmall).le hy
  have hform : Real.exp (4 * (Real.log 4 + 4) + 12 -
      κ * (Real.log L - Real.log H)) = C * (H / L) ^ κ := by
    rw [Real.rpow_def_of_pos (div_pos hHpos hLpos), Real.log_div hHpos.ne' hLpos.ne']
    dsimp only [C]
    rw [← Real.exp_add]
    congr 1
    ring
  change _ ≤ (1 + L) * Real.exp (4 * (Real.log 4 + 4) + 12 -
    κ * (Real.log L - Real.log H)) at hz
  rw [hform] at hz
  have hby : b / L ≤ b * |y| := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (lt_of_not_ge hsmall).le hb
  have hfactor : ‖1 - Complex.exp (-((b / L : ℝ) : ℂ) + ((-b * y : ℝ) : ℂ) * I)‖ ≤
      4 * min 1 (b * |y|) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
    exact le_min (hd₂.trans (by norm_num)) (hdlin.trans (by linarith))
  have hHD : H = max (max B (L ^ ((A : ℝ)⁻¹))) (1 / |y|) := by dsimp [H]; ac_rfl
  have hopt : (H / L) ^ κ * min 1 (b * |y|) ≤ (D / L) ^ κ := by
    rw [hHD]
    exact scaled_frequency_envelope_le hLpos hDpos hypos
      (max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))) hbD hκ hκ₁
  calc
    _ ≤ ((1 + L) * (C * (H / L) ^ κ)) * (4 * min 1 (b * |y|)) :=
      mul_le_mul hz hfactor (norm_nonneg _) (by positivity)
    _ = (4 * C * (1 + L)) * ((H / L) ^ κ * min 1 (b * |y|)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hopt (by positivity)

/-- The optimized difference-factor bound is transported rightward without
reselecting the source maximizer or dropping the initial damping. -/
theorem exists_maximizingTwist_dilation_rightward_bound (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b α y : ℝ, 1 < x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → 0 < α → |y| ≤ Real.log x / 4 →
      ‖riemannZeta (((1 + 1 / Real.log x + α : ℝ) : ℂ) +
          ((y - (t - t₀) : ℝ) : ℂ) * I) *
        (1 - Complex.exp (-(((1 / Real.log x + α) * b : ℝ) : ℂ) +
          ((-b * y : ℝ) : ℂ) * I))‖ ≤
          4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
            (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) +
              (1 + Real.log x) * (16 * α / (Real.pi * Real.log x)) := by
  obtain ⟨B, hB, hsource⟩ := exists_maximizingTwist_dilation_factor_bound A hA
  refine ⟨B, hB, ?_⟩
  intro x t t₀ b α y hx hscale hmax ht₀ hb hα hy
  let L := Real.log x
  let M := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
    (max B (max b (L ^ ((A : ℝ)⁻¹))) / L) ^ (38 / 113 : ℝ)
  let c : ℂ := Complex.exp (-((b / L : ℝ) : ℂ))
  have hL : 0 < L := Real.log_pos hx
  have hσ : 1 < 1 + 1 / L := lt_add_of_pos_right 1 (one_div_pos.mpr hL)
  have hc : ‖c‖ ≤ 1 := by
    dsimp only [c]
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hb hL.le))
  have hpoint (u : ℝ) :
      (((1 + 1 / L : ℝ) : ℂ) + ((u - (t - t₀) : ℝ) : ℂ) * I) =
        twistZetaPoint x t (t₀ + u) := by
    dsimp only [twistZetaPoint, L]
    push_cast
    ring
  have hlocal (u : ℝ) (hu : |u| ≤ 2 * (L / 4)) :
      ‖riemannZeta (((1 + 1 / L : ℝ) : ℂ) + ((u - (t - t₀) : ℝ) : ℂ) * I) *
        (1 - c * Complex.exp (((-b * u : ℝ) : ℂ) * I))‖ ≤ M := by
    dsimp only [c]
    rw [hpoint, ← Complex.exp_add]
    exact hsource x t t₀ b u hx hscale hmax ht₀ hb (by dsimp only [L] at hu; linarith)
  have hr := norm_shifted_zeta_difference_rightward_le (1 + 1 / L) (t - t₀) α
    (L / 4) M y b c hσ hα (by positivity) hb hc hlocal hy
  dsimp only [c] at hr
  rw [← Complex.exp_add] at hr
  have hexp : -((b / L : ℝ) : ℂ) +
      (((-α * b : ℝ) : ℂ) + ((-b * y : ℝ) : ℂ) * I) =
        -(((1 / L + α) * b : ℝ) : ℂ) + ((-b * y : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hexp] at hr
  have herr : (1 + 1 / (1 + 1 / L - 1)) * (4 * α / (Real.pi * (L / 4))) =
      (1 + L) * (16 * α / (Real.pi * L)) := by
    simp only [add_sub_cancel_left, one_div_one_div]
    ring
  rw [herr] at hr
  exact hr

end
end DongWangWangZhang2026
