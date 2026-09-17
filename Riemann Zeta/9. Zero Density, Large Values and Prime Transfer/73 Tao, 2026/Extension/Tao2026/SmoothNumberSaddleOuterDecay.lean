import Tao2026.SmoothNumberSaddleOuterPerron

/-!
# Global Euler-product decay on the outer Perron line

This module extracts a nonnegative phase-loss sum from the exact finite Euler
product.  A uniform prime-local reciprocal estimate, valid at every phase,
gives global exponential bounds for the tilted characteristic function and
for the literal saddle Perron integrand.  Thus the remaining outer-tail
problem is reduced to a quantitative lower bound for the explicit weighted
cosine loss over source primes.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddlePrimePhaseLoss
    (p : ℕ) (sigma t : ℝ) : ℝ :=
  2 * (p : ℝ) ^ (-sigma) *
      (1 - Real.cos (t * Real.log (p : ℝ))) /
    (1 - (p : ℝ) ^ (-sigma)) ^ 2

noncomputable def smoothSaddlePhaseLoss
    (y : ℕ) (sigma t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
    smoothSaddlePrimePhaseLoss p sigma t

/-- The simpler weighted cosine loss controlling the full Euler product. -/
noncomputable def smoothSaddleCosineLoss
    (y : ℕ) (sigma t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
    (p : ℝ) ^ (-sigma) * (1 - Real.cos (t * Real.log (p : ℝ)))

theorem smoothSaddlePrimePhaseLoss_nonneg
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    0 ≤ smoothSaddlePrimePhaseLoss p sigma t := by
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp)
      (neg_neg_of_pos hsigma)
  unfold smoothSaddlePrimePhaseLoss
  have hcos : 0 ≤ 1 - Real.cos (t * Real.log (p : ℝ)) := by
    linarith [Real.cos_le_one (t * Real.log (p : ℝ))]
  positivity

theorem smoothSaddlePhaseLoss_nonneg
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    0 ≤ smoothSaddlePhaseLoss y sigma t := by
  unfold smoothSaddlePhaseLoss
  exact Finset.sum_nonneg fun p hp =>
    smoothSaddlePrimePhaseLoss_nonneg
      (Finset.mem_filter.mp hp).2.one_lt hsigma t

theorem smoothSaddleCosineLoss_nonneg
    (y : ℕ) (sigma t : ℝ) : 0 ≤ smoothSaddleCosineLoss y sigma t := by
  unfold smoothSaddleCosineLoss
  exact Finset.sum_nonneg fun p hp => mul_nonneg (by positivity)
    (by linarith [Real.cos_le_one (t * Real.log (p : ℝ))])

theorem two_mul_primeCosineLoss_le_phaseLoss
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    2 * ((p : ℝ) ^ (-sigma) *
        (1 - Real.cos (t * Real.log (p : ℝ)))) ≤
      smoothSaddlePrimePhaseLoss p sigma t := by
  have haPos : 0 < (p : ℝ) ^ (-sigma) := by positivity
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp)
      (neg_neg_of_pos hsigma)
  have hApos : 0 < (1 - (p : ℝ) ^ (-sigma)) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr haLt)
  have hAle : (1 - (p : ℝ) ^ (-sigma)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (1 - (p : ℝ) ^ (-sigma))]
  have hN0 : 0 ≤ 2 * ((p : ℝ) ^ (-sigma) *
      (1 - Real.cos (t * Real.log (p : ℝ)))) := by
    have : 0 ≤ 1 - Real.cos (t * Real.log (p : ℝ)) := by
      linarith [Real.cos_le_one (t * Real.log (p : ℝ))]
    positivity
  unfold smoothSaddlePrimePhaseLoss
  rw [le_div_iff₀ hApos]
  nlinarith [mul_le_mul_of_nonneg_left hAle hN0]

theorem two_mul_smoothSaddleCosineLoss_le_phaseLoss
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    2 * smoothSaddleCosineLoss y sigma t ≤
      smoothSaddlePhaseLoss y sigma t := by
  unfold smoothSaddleCosineLoss smoothSaddlePhaseLoss
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun p hp =>
    two_mul_primeCosineLoss_le_phaseLoss
      (Finset.mem_filter.mp hp).2.one_lt hsigma t

theorem norm_smoothTiltedPrimeCharacteristic_sq_le_phaseLoss
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma)
    (t : ℝ) :
    ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 ≤
      Real.exp (-(smoothSaddlePrimePhaseLoss p sigma t / 96)) := by
  have hsigmaPos : 0 < sigma := by linarith
  let A : ℝ := (1 - (p : ℝ) ^ (-sigma)) ^ 2
  let B : ℝ := 2 * (p : ℝ) ^ (-sigma) *
    (1 - Real.cos (t * Real.log (p : ℝ)))
  let q : ℝ := B / A
  have haPos : 0 < (p : ℝ) ^ (-sigma) := by positivity
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp)
      (neg_neg_of_pos hsigmaPos)
  have hApos : 0 < A := sq_pos_of_pos (sub_pos.mpr haLt)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hcos : 0 ≤ 1 - Real.cos (t * Real.log (p : ℝ)) := by
      linarith [Real.cos_le_one (t * Real.log (p : ℝ))]
    positivity
  have hq0 : 0 ≤ q := div_nonneg hB0 hApos.le
  have hpow := four_thirds_le_prime_rpow (show 2 ≤ p by omega) hsigma
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have ha34 : (p : ℝ) ^ (-sigma) ≤ 3 / 4 := by
    rw [Real.rpow_neg hpPos.le]
    rw [inv_le_iff_one_le_mul₀' (Real.rpow_pos_of_pos hpPos sigma)]
    nlinarith
  have hcos : 1 - Real.cos (t * Real.log (p : ℝ)) ≤ 2 := by
    linarith [Real.neg_one_le_cos (t * Real.log (p : ℝ))]
  have hB3 : B ≤ 3 := by
    dsimp [B]
    nlinarith [mul_le_mul ha34 hcos
      (by linarith [Real.cos_le_one (t * Real.log (p : ℝ))] :
        0 ≤ 1 - Real.cos (t * Real.log (p : ℝ)))
      (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  have hA16 : (1 / 16 : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg (1 - (p : ℝ) ^ (-sigma))]
  have hq48 : q ≤ 48 := by
    dsimp [q]
    rw [div_le_iff₀ hApos]
    nlinarith
  have hratio : A / (A + B) = 1 / (1 + q) := by
    dsimp [q]
    field_simp [hApos.ne']
  calc
    ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 = A / (A + B) := by
      simpa [A, B] using
        norm_smoothTiltedPrimeCharacteristic_sq hp hsigmaPos t
    _ = 1 / (1 + q) := hratio
    _ ≤ Real.exp (-q / 96) :=
      one_div_one_add_le_exp_neg_div_96 hq0 hq48
    _ = Real.exp (-(smoothSaddlePrimePhaseLoss p sigma t / 96)) := by
      congr 1
      dsimp [q, B, A, smoothSaddlePrimePhaseLoss]
      ring

theorem norm_smoothTiltedCharacteristic_sq_le_phaseLoss
    (y : ℕ) {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma) (t : ℝ) :
    ‖smoothTiltedCharacteristic y sigma t‖ ^ 2 ≤
      Real.exp (-(smoothSaddlePhaseLoss y sigma t / 96)) := by
  let S := (Finset.Icc 2 y).filter Nat.Prime
  have hsigmaPos : 0 < sigma := by linarith
  rw [smoothTiltedCharacteristic_eq_sourcePrimeProduct y hsigmaPos t,
    norm_prod, ← Finset.prod_pow]
  calc
    (∏ p ∈ S, ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2) ≤
        ∏ p ∈ S,
          Real.exp (-(smoothSaddlePrimePhaseLoss p sigma t / 96)) := by
      exact Finset.prod_le_prod (fun p hp => sq_nonneg _)
        (fun p hp => norm_smoothTiltedPrimeCharacteristic_sq_le_phaseLoss
          (Finset.mem_filter.mp hp).2.one_lt hsigma t)
    _ = Real.exp (∑ p ∈ S,
          -(smoothSaddlePrimePhaseLoss p sigma t / 96)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(smoothSaddlePhaseLoss y sigma t / 96)) := by
      congr 1
      unfold smoothSaddlePhaseLoss
      rw [Finset.sum_neg_distrib, Finset.sum_div]

theorem norm_smoothTiltedCharacteristic_le_phaseLoss
    (y : ℕ) {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma) (t : ℝ) :
    ‖smoothTiltedCharacteristic y sigma t‖ ≤
      Real.exp (-(smoothSaddlePhaseLoss y sigma t / 192)) := by
  have hsq := norm_smoothTiltedCharacteristic_sq_le_phaseLoss y hsigma t
  have hgaussSq : Real.exp (-(smoothSaddlePhaseLoss y sigma t / 192)) ^ 2 =
      Real.exp (-(smoothSaddlePhaseLoss y sigma t / 96)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp
  rw [hgaussSq]
  exact hsq

theorem norm_smoothTiltedCharacteristic_le_cosineLoss
    (y : ℕ) {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma) (t : ℝ) :
    ‖smoothTiltedCharacteristic y sigma t‖ ≤
      Real.exp (-(smoothSaddleCosineLoss y sigma t / 96)) := by
  calc
    ‖smoothTiltedCharacteristic y sigma t‖ ≤
        Real.exp (-(smoothSaddlePhaseLoss y sigma t / 192)) :=
      norm_smoothTiltedCharacteristic_le_phaseLoss y hsigma t
    _ ≤ Real.exp (-(smoothSaddleCosineLoss y sigma t / 96)) := by
      apply Real.exp_le_exp.mpr
      have h := two_mul_smoothSaddleCosineLoss_le_phaseLoss y
        (by linarith : 0 < sigma) t
      linarith

theorem smoothSaddlePhaseLoss_neg (y : ℕ) (sigma t : ℝ) :
    smoothSaddlePhaseLoss y sigma (-t) =
      smoothSaddlePhaseLoss y sigma t := by
  unfold smoothSaddlePhaseLoss smoothSaddlePrimePhaseLoss
  apply Finset.sum_congr rfl
  intro p hp
  rw [neg_mul, Real.cos_neg]

theorem smoothSaddleCosineLoss_neg (y : ℕ) (sigma t : ℝ) :
    smoothSaddleCosineLoss y sigma (-t) =
      smoothSaddleCosineLoss y sigma t := by
  unfold smoothSaddleCosineLoss
  apply Finset.sum_congr rfl
  intro p hp
  rw [neg_mul, Real.cos_neg]

theorem norm_smoothSaddlePerronLineIntegrand_le_phaseLoss
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) (t : ℝ) :
    ‖smoothSaddlePerronLineIntegrand X y t‖ ≤
      Real.exp (-(smoothSaddlePhaseLoss y (smoothSaddlePoint X y) t / 192)) := by
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  rw [smoothSaddlePerronLineIntegrand_eq_characteristic_kernel hX hy,
    norm_mul]
  have hchar :
      ‖smoothSaddleNormalizedCharacteristic X y
          (-t * smoothSaddleStandardDeviation X y)‖ ≤
        Real.exp (-(smoothSaddlePhaseLoss y (smoothSaddlePoint X y) t / 192)) := by
    rw [smoothSaddleNormalizedCharacteristic, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    have harg : -t * smoothSaddleStandardDeviation X y /
        smoothSaddleStandardDeviation X y = -t := by
      field_simp [hsd.ne']
    rw [harg]
    have h := norm_smoothTiltedCharacteristic_le_phaseLoss y hsigma (-t)
    rw [smoothSaddlePhaseLoss_neg] at h
    exact h
  calc
    ‖smoothSaddleNormalizedCharacteristic X y
          (-t * smoothSaddleStandardDeviation X y)‖ *
        ‖smoothSaddleLaplaceFourierKernel X y
          (-t * smoothSaddleStandardDeviation X y)‖ ≤
      Real.exp (-(smoothSaddlePhaseLoss y (smoothSaddlePoint X y) t / 192)) * 1 :=
        mul_le_mul hchar
          (norm_smoothSaddleLaplaceFourierKernel_le_one X y _)
          (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

theorem norm_smoothSaddlePerronLineIntegrand_le_cosineLoss
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) (t : ℝ) :
    ‖smoothSaddlePerronLineIntegrand X y t‖ ≤
      Real.exp (-(smoothSaddleCosineLoss y (smoothSaddlePoint X y) t / 96)) := by
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  rw [smoothSaddlePerronLineIntegrand_eq_characteristic_kernel hX hy,
    norm_mul]
  have hchar :
      ‖smoothSaddleNormalizedCharacteristic X y
          (-t * smoothSaddleStandardDeviation X y)‖ ≤
        Real.exp (-(smoothSaddleCosineLoss y (smoothSaddlePoint X y) t / 96)) := by
    rw [smoothSaddleNormalizedCharacteristic, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    have harg : -t * smoothSaddleStandardDeviation X y /
        smoothSaddleStandardDeviation X y = -t := by
      field_simp [hsd.ne']
    rw [harg]
    have h := norm_smoothTiltedCharacteristic_le_cosineLoss y hsigma (-t)
    rw [smoothSaddleCosineLoss_neg] at h
    exact h
  calc
    ‖smoothSaddleNormalizedCharacteristic X y
          (-t * smoothSaddleStandardDeviation X y)‖ *
        ‖smoothSaddleLaplaceFourierKernel X y
          (-t * smoothSaddleStandardDeviation X y)‖ ≤
      Real.exp (-(smoothSaddleCosineLoss y (smoothSaddlePoint X y) t / 96)) * 1 :=
        mul_le_mul hchar
          (norm_smoothSaddleLaplaceFourierKernel_le_one X y _)
          (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

end

end Tao2026
