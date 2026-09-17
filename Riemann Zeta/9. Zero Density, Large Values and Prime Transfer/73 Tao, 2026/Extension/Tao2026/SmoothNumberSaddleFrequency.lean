import Tao2026.SmoothNumberSaddleEulerCharacteristic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Frequency bounds for the smooth saddle

The exact prime-factor contraction formula is converted here into quadratic
decay on the principal frequency window.  These estimates are the analytic
input to the Gaussian approximation and later Fourier inversion.
-/

namespace Tao2026

noncomputable section

/-- On the principal trigonometric period, `1 - cos` dominates a fixed
quadratic. -/
theorem two_div_pi_sq_mul_sq_le_one_sub_cos
    {x : ℝ} (hx : |x| ≤ Real.pi) :
    2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x := by
  have hcos := Real.cos_le_one_sub_mul_cos_sq hx
  linarith

/-- A reciprocal linear contraction is bounded by a Gaussian exponential on
the unit interval. -/
theorem one_div_one_add_le_exp_neg_half
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 / (1 + x) ≤ Real.exp (-x / 2) := by
  have hhalf0 : 0 ≤ x / 2 := by positivity
  have hhalf1 : x / 2 < 1 := by linarith
  have hexp : Real.exp (x / 2) ≤ 1 / (1 - x / 2) :=
    Real.exp_bound_div_one_sub_of_interval hhalf0 hhalf1
  have hrat : 1 / (1 - x / 2) ≤ 1 + x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc
    1 / (1 + x) ≤ 1 / Real.exp (x / 2) :=
      one_div_le_one_div_of_le (Real.exp_pos _) (hexp.trans hrat)
    _ = Real.exp (-x / 2) := by
      rw [one_div, ← Real.exp_neg]
      congr 1
      ring

/-- A convenient uniform criterion that implies both local central-window
conditions. -/
theorem local_frequency_conditions_of_abs_le
    {a d theta : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hd0 : 0 ≤ d) (hda : d ≤ 1 - a)
    (htheta : |theta| ≤ Real.pi / 2 * d) :
    |theta| ≤ Real.pi ∧
      4 / Real.pi ^ 2 * a * theta ^ 2 ≤ (1 - a) ^ 2 := by
  have hd1 : d ≤ 1 := by linarith
  have hphase : |theta| ≤ Real.pi := by
    calc
      |theta| ≤ Real.pi / 2 * d := htheta
      _ ≤ Real.pi / 2 * 1 := by
        exact mul_le_mul_of_nonneg_left hd1 (by positivity)
      _ ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hthetaSq : theta ^ 2 ≤ (Real.pi / 2 * d) ^ 2 := by
    rw [← sq_abs theta]
    exact (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (by positivity) hd0)).2 htheta
  have hquad :
      4 / Real.pi ^ 2 * a * theta ^ 2 ≤ d ^ 2 := by
    calc
      4 / Real.pi ^ 2 * a * theta ^ 2 ≤
          4 / Real.pi ^ 2 * 1 * (Real.pi / 2 * d) ^ 2 := by
        gcongr
      _ = d ^ 2 := by
        field_simp [Real.pi_ne_zero]
        ring
  exact ⟨hphase, hquad.trans
    ((sq_le_sq₀ hd0 (sub_nonneg.mpr ha1)).2 hda)⟩

/-- A prime-local characteristic factor contracts at least quadratically
while its phase remains in the principal period. -/
theorem norm_smoothTiltedPrimeCharacteristic_sq_le_quadratic
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ)
    (ht : |t * Real.log (p : ℝ)| ≤ Real.pi) :
    ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 ≤
      (1 - (p : ℝ) ^ (-sigma)) ^ 2 /
        ((1 - (p : ℝ) ^ (-sigma)) ^ 2 +
          4 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
            (t * Real.log (p : ℝ)) ^ 2) := by
  rw [norm_smoothTiltedPrimeCharacteristic_sq hp hsigma t]
  have haPos : 0 < (p : ℝ) ^ (-sigma) :=
    Real.rpow_pos_of_pos (by positivity) _
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp) (neg_neg_of_pos hsigma)
  have hcos := two_div_pi_sq_mul_sq_le_one_sub_cos ht
  have hloss :
      4 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
          (t * Real.log (p : ℝ)) ^ 2 ≤
        2 * (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
    calc
      4 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
          (t * Real.log (p : ℝ)) ^ 2 =
          (2 * (p : ℝ) ^ (-sigma)) *
            (2 / Real.pi ^ 2 * (t * Real.log (p : ℝ)) ^ 2) := by ring
      _ ≤ (2 * (p : ℝ) ^ (-sigma)) *
          (1 - Real.cos (t * Real.log (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
  have hden :
      (1 - (p : ℝ) ^ (-sigma)) ^ 2 +
          4 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
            (t * Real.log (p : ℝ)) ^ 2 ≤
        (1 - (p : ℝ) ^ (-sigma)) ^ 2 +
          2 * (p : ℝ) ^ (-sigma) *
            (1 - Real.cos (t * Real.log (p : ℝ))) := by
    linarith
  exact div_le_div_of_nonneg_left (sq_nonneg _)
    (by positivity [sub_pos.mpr haLt]) hden

/-- In the central window, a prime-local factor has an explicit Gaussian
upper bound. -/
theorem norm_smoothTiltedPrimeCharacteristic_sq_le_exp
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ)
    (ht : |t * Real.log (p : ℝ)| ≤ Real.pi)
    (hsmall :
      4 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
          (t * Real.log (p : ℝ)) ^ 2 ≤
        (1 - (p : ℝ) ^ (-sigma)) ^ 2) :
    ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 ≤
      Real.exp
        (-(2 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
          (t * Real.log (p : ℝ)) ^ 2 /
            (1 - (p : ℝ) ^ (-sigma)) ^ 2)) := by
  let A : ℝ := (1 - (p : ℝ) ^ (-sigma)) ^ 2
  let B : ℝ := 4 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
    (t * Real.log (p : ℝ)) ^ 2
  let q : ℝ := B / A
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp) (neg_neg_of_pos hsigma)
  have hApos : 0 < A := by
    exact sq_pos_of_pos (sub_pos.mpr haLt)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hq0 : 0 ≤ q := div_nonneg hB0 hApos.le
  have hq1 : q ≤ 1 := by
    exact (div_le_one hApos).2 (by simpa [A, B] using hsmall)
  have hratio : A / (A + B) = 1 / (1 + q) := by
    dsimp [q]
    field_simp [hApos.ne']
  calc
    ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 ≤ A / (A + B) := by
      simpa [A, B] using
        norm_smoothTiltedPrimeCharacteristic_sq_le_quadratic
          hp hsigma t ht
    _ = 1 / (1 + q) := hratio
    _ ≤ Real.exp (-q / 2) := one_div_one_add_le_exp_neg_half hq0 hq1
    _ = Real.exp
        (-(2 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
          (t * Real.log (p : ℝ)) ^ 2 /
            (1 - (p : ℝ) ^ (-sigma)) ^ 2)) := by
      congr 1
      dsimp [q, B, A]
      field_simp [hApos.ne']
      ring

/-- The quadratic coefficient in the local contraction is exactly the
corresponding second saddle summand. -/
theorem rpow_neg_mul_log_sq_div_one_sub_sq_eq_secondPrimeTerm
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) :
    (p : ℝ) ^ (-sigma) * (Real.log (p : ℝ)) ^ 2 /
        (1 - (p : ℝ) ^ (-sigma)) ^ 2 =
      smoothSaddleSecondPrimeTerm p sigma := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have hpowPos : 0 < (p : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos hpPos _
  have hdenPos : 0 < (p : ℝ) ^ sigma - 1 :=
    smoothSaddle_denominator_pos (by omega) hsigma
  rw [Real.rpow_neg hpPos.le]
  unfold smoothSaddleSecondPrimeTerm
  field_simp [hpowPos.ne', hdenPos.ne']

/-- Multiplying the central prime-local estimates gives Gaussian decay with
the exact saddle curvature `phiTwo`. -/
theorem norm_smoothTiltedCharacteristic_sq_le_exp_phiTwo
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ)
    (hphase : ∀ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
      |t * Real.log (p : ℝ)| ≤ Real.pi)
    (hsmall : ∀ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
      4 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
          (t * Real.log (p : ℝ)) ^ 2 ≤
        (1 - (p : ℝ) ^ (-sigma)) ^ 2) :
    ‖smoothTiltedCharacteristic y sigma t‖ ^ 2 ≤
      Real.exp (-(2 / Real.pi ^ 2 * t ^ 2 *
        smoothSaddlePhiTwo y sigma)) := by
  let S := (Finset.Icc 2 y).filter Nat.Prime
  let C : ℝ := 2 / Real.pi ^ 2 * t ^ 2
  have hlocal (p : ℕ) (hp : p ∈ S) :
      ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 ≤
        Real.exp (-(C * smoothSaddleSecondPrimeTerm p sigma)) := by
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have h := norm_smoothTiltedPrimeCharacteristic_sq_le_exp
      hpPrime.one_lt hsigma t (hphase p hp) (hsmall p hp)
    convert h using 1
    congr 2
    rw [← rpow_neg_mul_log_sq_div_one_sub_sq_eq_secondPrimeTerm
      hpPrime.one_lt hsigma]
    dsimp [C]
    ring
  rw [smoothTiltedCharacteristic_eq_sourcePrimeProduct y hsigma t,
    norm_prod, ← Finset.prod_pow]
  calc
    (∏ p ∈ S, ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2) ≤
        ∏ p ∈ S,
          Real.exp (-(C * smoothSaddleSecondPrimeTerm p sigma)) := by
      exact Finset.prod_le_prod (fun p hp => sq_nonneg _)
        (fun p hp => hlocal p hp)
    _ = Real.exp (∑ p ∈ S,
          -(C * smoothSaddleSecondPrimeTerm p sigma)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(2 / Real.pi ^ 2 * t ^ 2 *
        smoothSaddlePhiTwo y sigma)) := by
      congr 1
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      rfl

/-- On the central frequency window, variance normalization converts the
curvature-dependent estimate into a universal Gaussian bound. -/
theorem norm_smoothSaddleNormalizedCharacteristic_sq_le_exp
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ)
    (hphase : ∀ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
      |(t / smoothSaddleStandardDeviation X y) *
        Real.log (p : ℝ)| ≤ Real.pi)
    (hsmall : ∀ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
      4 / Real.pi ^ 2 *
          (p : ℝ) ^ (-smoothSaddlePoint X y) *
          ((t / smoothSaddleStandardDeviation X y) *
            Real.log (p : ℝ)) ^ 2 ≤
        (1 - (p : ℝ) ^ (-smoothSaddlePoint X y)) ^ 2) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ^ 2 ≤
      Real.exp (-(2 / Real.pi ^ 2 * t ^ 2)) := by
  have hsdPos := smoothSaddleStandardDeviation_pos hX hy
  have hphiPos := smoothSaddlePhiTwo_pos hy
    (smoothSaddlePoint_pos hX hy)
  have hsdSq : smoothSaddleStandardDeviation X y ^ 2 =
      smoothSaddlePhiTwo y (smoothSaddlePoint X y) := by
    unfold smoothSaddleStandardDeviation
    exact Real.sq_sqrt hphiPos.le
  have h := norm_smoothTiltedCharacteristic_sq_le_exp_phiTwo
    y (smoothSaddlePoint_pos hX hy)
    (t / smoothSaddleStandardDeviation X y) hphase hsmall
  rw [smoothSaddleNormalizedCharacteristic, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  convert h using 1
  congr 2
  rw [div_pow, hsdSq]
  field_simp [hphiPos.ne']

/-- A single source-scale bound on `|t|` automatically supplies every local
central-window condition. -/
theorem norm_smoothSaddleNormalizedCharacteristic_sq_le_exp_of_range
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ)
    (hrange :
      |t| * Real.log (y : ℝ) / smoothSaddleStandardDeviation X y ≤
        Real.pi / 2 *
          (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y))) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ^ 2 ≤
      Real.exp (-(2 / Real.pi ^ 2 * t ^ 2)) := by
  have hsigma := smoothSaddlePoint_pos hX hy
  have hsdPos := smoothSaddleStandardDeviation_pos hX hy
  have htwoLt : (2 : ℝ) ^ (-smoothSaddlePoint X y) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hsigma)
  have hconditions (p : ℕ)
      (hp : p ∈ (Finset.Icc 2 y).filter Nat.Prime) :
      |(t / smoothSaddleStandardDeviation X y) * Real.log (p : ℝ)| ≤
          Real.pi ∧
        4 / Real.pi ^ 2 *
            (p : ℝ) ^ (-smoothSaddlePoint X y) *
            ((t / smoothSaddleStandardDeviation X y) *
              Real.log (p : ℝ)) ^ 2 ≤
          (1 - (p : ℝ) ^ (-smoothSaddlePoint X y)) ^ 2 := by
    have hpBounds := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1)
    have hpPos : (0 : ℝ) < p := by
      exact_mod_cast (show 0 < p by omega)
    have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    have hlogpy : Real.log (p : ℝ) ≤ Real.log (y : ℝ) :=
      Real.log_le_log hpPos (by exact_mod_cast hpBounds.2)
    have htheta :
        |(t / smoothSaddleStandardDeviation X y) * Real.log (p : ℝ)| ≤
          Real.pi / 2 *
            (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y)) := by
      calc
        |(t / smoothSaddleStandardDeviation X y) * Real.log (p : ℝ)| =
            |t| * Real.log (p : ℝ) /
              smoothSaddleStandardDeviation X y := by
          rw [abs_mul, abs_div, abs_of_pos hsdPos, abs_of_nonneg hlogp0]
          ring
        _ ≤ |t| * Real.log (y : ℝ) /
              smoothSaddleStandardDeviation X y := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogpy (abs_nonneg t)) hsdPos.le
        _ ≤ _ := hrange
    have ha0 : 0 ≤ (p : ℝ) ^ (-smoothSaddlePoint X y) :=
      Real.rpow_nonneg (by positivity) _
    have ha1 : (p : ℝ) ^ (-smoothSaddlePoint X y) ≤ 1 :=
      (Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast (show 1 < p by omega))
        (neg_neg_of_pos hsigma)).le
    have haTwo : (p : ℝ) ^ (-smoothSaddlePoint X y) ≤
        (2 : ℝ) ^ (-smoothSaddlePoint X y) :=
      Real.rpow_le_rpow_of_nonpos zero_lt_two
        (by exact_mod_cast hpBounds.1) (neg_nonpos.mpr hsigma.le)
    exact local_frequency_conditions_of_abs_le ha0 ha1
      (sub_nonneg.mpr htwoLt.le) (by linarith) htheta
  apply norm_smoothSaddleNormalizedCharacteristic_sq_le_exp hX hy t
  · intro p hp
    exact (hconditions p hp).1
  · intro p hp
    exact (hconditions p hp).2

/-- Unsquared Gaussian envelope on the same central frequency range. -/
theorem norm_smoothSaddleNormalizedCharacteristic_le_exp_of_range
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ)
    (hrange :
      |t| * Real.log (y : ℝ) / smoothSaddleStandardDeviation X y ≤
        Real.pi / 2 *
          (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y))) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ≤
      Real.exp (-(1 / Real.pi ^ 2 * t ^ 2)) := by
  have hsq := norm_smoothSaddleNormalizedCharacteristic_sq_le_exp_of_range
    hX hy t hrange
  have hgaussSq :
      Real.exp (-(1 / Real.pi ^ 2 * t ^ 2)) ^ 2 =
        Real.exp (-(2 / Real.pi ^ 2 * t ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp
  rw [hgaussSq]
  exact hsq

end

end Tao2026
