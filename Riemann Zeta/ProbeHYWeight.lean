import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

example {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    (h : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-(1 / 2 : ℝ)) *
        (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ^
          (-(1 / 2 : ℝ))) =
      (hughesYoungCommonDivisor h k : ℝ) / ((h : ℝ) * (k : ℝ)) := by
  let d := hughesYoungCommonDivisor h k
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  have hd : 0 < d := hughesYoungCommonDivisor_pos hh
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hha : d * a = h := hughesYoungCommonDivisor_mul_reducedLeft h k
  have hkb : d * b = k := hughesYoungCommonDivisor_mul_reducedRight h k
  change (h : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-(1 / 2 : ℝ)) *
      ((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
        (d : ℝ) / ((h : ℝ) * (k : ℝ))
  rw [← hha, ← hkb]
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg a),
    Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg b),
    Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Real.rpow_neg (Nat.cast_nonneg d), Real.rpow_neg (Nat.cast_nonneg a),
    Real.rpow_neg (Nat.cast_nonneg b)]
  have hdsqrt : (d : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt d := by
    rw [Real.sqrt_eq_rpow]
  have hasqrt : (a : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt a := by
    rw [Real.sqrt_eq_rpow]
  have hbsqrt : (b : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt b := by
    rw [Real.sqrt_eq_rpow]
  rw [hdsqrt, hasqrt, hbsqrt]
  field_simp [ne_of_gt hdR, ne_of_gt haR, ne_of_gt hbR,
    ne_of_gt (Real.sqrt_pos.2 hdR), ne_of_gt (Real.sqrt_pos.2 haR),
    ne_of_gt (Real.sqrt_pos.2 hbR)]
  rw [Real.sq_sqrt (Nat.cast_nonneg d),
    Real.sq_sqrt (Nat.cast_nonneg a),
    Real.sq_sqrt (Nat.cast_nonneg b)]

example {T : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ^
          (-(1 / 2 : ℝ))) =
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) * (1 / Real.pi) := by
  rw [norm_hughesYoungLocalizedStaticScalar_eq_coefficients_mul_rpow hh hk]
  rw [show Nat.gcd h k = hughesYoungCommonDivisor h k by rfl]
  rw [← hughesYoung_criticalWeights_mul_reduced_rpow_eq_gcd_div hh hk]
  ring

end RiemannZeta.GuthMaynard
