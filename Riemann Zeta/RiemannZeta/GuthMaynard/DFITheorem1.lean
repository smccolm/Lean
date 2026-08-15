import RiemannZeta.GuthMaynard.DFIErrorOptimization

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-!
# DFI Theorem 1

This file assembles the source-faithful equations (2) and (9)--(30) into
the quantitative shifted-divisor theorem used by Hughes--Young.  Constants
introduced below depend only on the equation-(2) derivative profile and on
the displayed epsilon; none may depend on the arithmetic parameters.
-/

/-- The optimized second term of DFI equation (30), with its epsilon power,
is exactly the error scale printed in Theorem 1. -/
theorem dfiEquation30_second_with_epsilon_eq_theorem1ErrorScale
    {P X Y Q ε : ℝ} (hP : 0 < P) (hX : 0 < X) (hY : 0 < Y)
    (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ))) *
        (X * Y) ^ ε =
      dfiTheorem1ErrorScale P X Y ε := by
  have hBase := dfiEquation30_second_optimized_eq hP hX hY hQ hQsq
  rw [hBase]
  unfold dfiTheorem1ErrorScale
  have hXY : 0 < X * Y := mul_pos hX hY
  rw [show
      P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ) * (X * Y) ^ ε =
        P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          ((X * Y) ^ (1 / 4 : ℝ) * (X * Y) ^ ε) by ring,
    ← Real.rpow_add hXY]

/-- The complete collection of epsilon losses in a retained one-sided
equation-(29) branch.  The internal contour displacement is `ε/8`.
The source coefficient, the explicit logarithm, the logarithmic main-term
majorant, and the two-gcd divisor average together spend at most `7ε/8`.
The unused `ε/8` is retained as genuine slack. -/
noncomputable def dfiEquation29TwoGcdAverage
    (H A : ℕ) (Q δ : ℝ) : ℝ :=
  divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
    (Real.sqrt ((H.divisors.card : ℝ) *
        (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
      Real.sqrt ((A.divisors.card : ℝ) *
        (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))))

/-- Arithmetic average occurring in the retained double-dual rectangle of
DFI equation (29). -/
noncomputable def dfiEquation29ThreeGcdAverage
    (H A B : ℕ) (Q δ : ℝ) : ℝ :=
  divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
    (Real.sqrt ((H.divisors.card : ℝ) *
        (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
      Real.sqrt (((A * B).divisors.card : ℝ) * ⌈2 * Q⌉₊))

/-- Uniform absorption of the three-gcd average in the source support
range.  The square root of the modulus endpoint is deliberately retained;
it is the `Q^(1/2)` which turns the double-dual `Q^-3` factor into the
second error of DFI equation (30). -/
theorem dfiEquation29_threeGcdAverageLoss_le_rpow_sqrtQ
    {X Y Q δ : ℝ} {H A B : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y)
    (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hHXY : (H : ℝ) ≤ 4 * (X * Y))
    (hAX : (A : ℝ) ≤ 2 * X) (hBY : (B : ℝ) ≤ 2 * Y)
    (hδ : 0 < δ) :
    dfiEquation29ThreeGcdAverage H A B Q δ ≤
      (divisorEpsilonConstant δ * 3 ^ δ *
        Real.sqrt ((divisorEpsilonConstant δ * 4 ^ δ) *
          ((1 + δ⁻¹) * 3 ^ δ)) *
        Real.sqrt ((divisorEpsilonConstant δ * 4 ^ δ) * 3)) *
      Q ^ (1 / 2 : ℝ) * ((X * Y) ^ δ) ^ 3 := by
  let S : ℝ := X * Y
  let L : ℕ := ⌈2 * Q⌉₊
  let Z : ℝ := S ^ δ
  let D : ℝ := divisorEpsilonConstant δ
  let K : ℝ := 1 + δ⁻¹
  let CL : ℝ := 3 ^ δ
  let CH : ℝ := D * 4 ^ δ
  let CAB : ℝ := D * 4 ^ δ
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hS0 : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hZ1 : 1 ≤ Z := by
    dsimp [Z]
    exact Real.one_le_rpow hS1 hδ.le
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact (divisorEpsilonConstant_pos δ).le
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hCL0 : 0 ≤ CL := by dsimp [CL]; positivity
  have hCH0 : 0 ≤ CH := by dsimp [CH]; positivity
  have hCAB0 : 0 ≤ CAB := by dsimp [CAB]; positivity
  have hLpos : 0 < L := by
    have hLower : 2 * Q ≤ (L : ℝ) := by
      dsimp only [L]
      exact Nat.le_ceil _
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  have hLone : (1 : ℝ) ≤ L := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hLpos.ne')
  have hLQ : (L : ℝ) ≤ 3 * Q := by
    dsimp only [L]
    exact natCeil_two_mul_le_three_mul hQ
  have hLupper : (L : ℝ) ≤ 3 * S := hLQ.trans (by gcongr)
  have hLpow : (L : ℝ) ^ δ ≤ CL * Z := by
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg L) hLupper hδ.le
    calc
      (L : ℝ) ^ δ ≤ (3 * S) ^ δ := hpow
      _ = CL * Z := by
        dsimp [CL, Z]
        rw [Real.mul_rpow (by norm_num) hS0.le]
  have hMax : max 1 ((L : ℝ) ^ δ) = (L : ℝ) ^ δ := by
    rw [max_eq_right]
    exact Real.one_le_rpow hLone hδ.le
  have hHpow : (H : ℝ) ^ δ ≤ 4 ^ δ * Z := by
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg H) hHXY hδ.le
    calc
      (H : ℝ) ^ δ ≤ (4 * S) ^ δ := hp
      _ = 4 ^ δ * Z := by
        dsimp [Z]
        rw [Real.mul_rpow (by norm_num) hS0.le]
  have hABXY : ((A * B : ℕ) : ℝ) ≤ 4 * S := by
    push_cast
    dsimp [S]
    nlinarith
  have hABpow : ((A * B : ℕ) : ℝ) ^ δ ≤ 4 ^ δ * Z := by
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg (A * B)) hABXY hδ.le
    calc
      ((A * B : ℕ) : ℝ) ^ δ ≤ (4 * S) ^ δ := hp
      _ = 4 ^ δ * Z := by
        dsimp [Z]
        rw [Real.mul_rpow (by norm_num) hS0.le]
  have hHcard : (H.divisors.card : ℝ) ≤ CH * Z := by
    calc
      (H.divisors.card : ℝ) ≤ D * (H : ℝ) ^ δ := by
        simpa only [D] using card_divisors_le_const_mul_rpow hδ hH.ne'
      _ ≤ D * (4 ^ δ * Z) := by gcongr
      _ = CH * Z := by dsimp [CH]; ring
  have hABcard : ((A * B).divisors.card : ℝ) ≤ CAB * Z := by
    calc
      ((A * B).divisors.card : ℝ) ≤ D * ((A * B : ℕ) : ℝ) ^ δ := by
        simpa only [D] using
          card_divisors_le_const_mul_rpow hδ (Nat.mul_pos hA hB).ne'
      _ ≤ D * (4 ^ δ * Z) := by gcongr
      _ = CAB * Z := by dsimp [CAB]; ring
  have hHarm : (((harmonic L : ℚ) : ℝ)) ≤ (K * CL) * Z := by
    calc
      (((harmonic L : ℚ) : ℝ)) ≤ K * max 1 ((L : ℝ) ^ δ) := by
        simpa only [K] using harmonic_le_epsilon_rpow hδ L
      _ = K * (L : ℝ) ^ δ := by rw [hMax]
      _ ≤ K * (CL * Z) := by gcongr
      _ = (K * CL) * Z := by ring
  have hHarm0 : 0 ≤ (((harmonic L : ℚ) : ℝ)) := by
    exact_mod_cast (harmonic_pos hLpos.ne').le
  have hHsqrt :
      Real.sqrt ((H.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ))) ≤
        Real.sqrt (CH * (K * CL)) * Z :=
    sqrt_mul_le_sqrt_mul_mul hHarm0 hCH0 (mul_nonneg hK0 hCL0) hZ0
      hHcard hHarm
  have hABinside :
      ((A * B).divisors.card : ℝ) * (L : ℝ) ≤
        (CAB * Z) * (3 * Q) :=
    mul_le_mul hABcard hLQ (Nat.cast_nonneg L) (mul_nonneg hCAB0 hZ0)
  have hSqrtZ : Real.sqrt Z ≤ Z := by
    nlinarith [Real.sq_sqrt hZ0, Real.sqrt_nonneg Z]
  have hABsqrt :
      Real.sqrt (((A * B).divisors.card : ℝ) * (L : ℝ)) ≤
        Real.sqrt (CAB * 3) * Z * Q ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt (((A * B).divisors.card : ℝ) * (L : ℝ)) ≤
          Real.sqrt ((CAB * Z) * (3 * Q)) := Real.sqrt_le_sqrt hABinside
      _ = Real.sqrt (CAB * 3) * Real.sqrt Z * Real.sqrt Q := by
        rw [show (CAB * Z) * (3 * Q) = (CAB * 3) * (Z * Q) by ring,
          Real.sqrt_mul (mul_nonneg hCAB0 (by norm_num)),
          Real.sqrt_mul hZ0]
        ring
      _ ≤ Real.sqrt (CAB * 3) * Z * Real.sqrt Q := by gcongr
      _ = Real.sqrt (CAB * 3) * Z * Q ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  change D * max 1 ((L : ℝ) ^ δ) *
      (Real.sqrt ((H.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ))) *
        Real.sqrt (((A * B).divisors.card : ℝ) * (L : ℝ))) ≤ _
  rw [hMax]
  calc
    D * (L : ℝ) ^ δ *
        (Real.sqrt ((H.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ))) *
          Real.sqrt (((A * B).divisors.card : ℝ) * (L : ℝ))) ≤
      D * (CL * Z) *
        ((Real.sqrt (CH * (K * CL)) * Z) *
          (Real.sqrt (CAB * 3) * Z * Q ^ (1 / 2 : ℝ))) := by gcongr
    _ = (D * CL * Real.sqrt (CH * (K * CL)) *
          Real.sqrt (CAB * 3)) * Q ^ (1 / 2 : ℝ) * Z ^ 3 := by ring
    _ = _ := by dsimp [D, K, CL, CH, CAB, Z, S]

/-- The zero-epsilon physical scale of the retained double-dual rectangle
is bounded by DFI equation (30)'s second error. -/
theorem dfiEquation29_doubleRetained_zeroEpsilon_le_secondError
    {X Y Q : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 0 < Q) :
    ((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
        Q ^ (1 / 2 : ℝ) ≤
      2 * ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) *
        Q ^ (-(5 / 2 : ℝ))) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hS0 : 0 < X * Y := mul_pos hX0 hY0
  have hSum0 : 0 < X + Y := add_pos hX0 hY0
  have hMinSum : min X Y * (X + Y) ≤ 2 * (X * Y) := by
    rcases le_total X Y with hXY | hYX
    · rw [min_eq_left hXY]
      nlinarith [mul_nonneg hX0.le (sub_nonneg.mpr hXY)]
    · rw [min_eq_right hYX]
      nlinarith [mul_nonneg hY0.le (sub_nonneg.mpr hYX)]
  have hMinDiv : min X Y ≤ 2 * (X * Y) / (X + Y) := by
    exact (le_div_iff₀ hSum0).2 (by simpa [mul_comm] using hMinSum)
  have hSsplit :
      (X * Y) ^ (1 / 2 : ℝ) * (X * Y) = (X * Y) ^ (3 / 2 : ℝ) := by
    calc
      (X * Y) ^ (1 / 2 : ℝ) * (X * Y) =
          (X * Y) ^ (1 / 2 : ℝ) * (X * Y) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (X * Y) ^ ((1 / 2 : ℝ) + 1) := by rw [Real.rpow_add hS0]
      _ = _ := by congr 1; ring
  have hQsplit : Q ^ (-(3 : ℝ)) * Q ^ (1 / 2 : ℝ) =
      Q ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc
    ((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
        Q ^ (1 / 2 : ℝ) =
      ((X * Y) ^ (1 / 2 : ℝ) * min X Y) *
        (Q ^ (-(3 : ℝ)) * Q ^ (1 / 2 : ℝ)) := by ring
    _ ≤ ((X * Y) ^ (1 / 2 : ℝ) *
        (2 * (X * Y) / (X + Y))) *
        (Q ^ (-(3 : ℝ)) * Q ^ (1 / 2 : ℝ)) := by gcongr
    _ = 2 * ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) *
        Q ^ (-(5 / 2 : ℝ))) := by rw [hQsplit, ← hSsplit]; ring

/-- Complete epsilon-loss absorption for the double-retained rectangle.
The internal displacement is `ε/8`; five such powers are spent, leaving
strict slack in the published `ε` exponent. -/
theorem dfiEquation29_doubleRetained_loss_bundle_le
    {X Y Q ε CA : ℝ} {A B H : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y)
    (hA : 0 < A) (hB : 0 < B)
    (hAX : (A : ℝ) ≤ 2 * X) (hBY : (B : ℝ) ≤ 2 * Y)
    (hε0 : 0 < ε) (hε4 : ε ≤ 4)
    (hCA : 0 ≤ CA)
    (hAverage : dfiEquation29ThreeGcdAverage H A B Q (ε / 8) ≤
      CA * Q ^ (1 / 2 : ℝ) * ((X * Y) ^ (ε / 8)) ^ 3) :
    ((2 ^ (3 / 4 + (ε / 8) / 2) * 2 ^ (3 / 4 + (ε / 8) / 2)) *
        X ^ (1 / 2 + (ε / 8) / 2) * Y ^ (1 / 2 + (ε / 8) / 2) *
        (A : ℝ) ^ ((ε / 8) / 2) * (B : ℝ) ^ ((ε / 8) / 2) *
        (Q ^ ((-2 + ε / 8) * (3 / 4 + (ε / 8) / 2)) *
          Q ^ ((-2 + ε / 8) * (3 / 4 + (ε / 8) / 2))) *
        (min X Y * Real.log Q)) *
        dfiEquation29ThreeGcdAverage H A B Q (ε / 8) ≤
      ((2 ^ (3 / 4 + (ε / 8) / 2) * 2 ^ (3 / 4 + (ε / 8) / 2)) *
        2 ^ (ε / 8) * (8 / ε) * CA) *
        (((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
          Q ^ (1 / 2 : ℝ)) * (X * Y) ^ ε := by
  let η : ℝ := ε / 8
  let S : ℝ := X * Y
  have hη : 0 < η := by dsimp [η]; positivity
  have hηhalf : η ≤ 1 / 2 := by dsimp [η]; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hS0 : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith
  have hAB : (A : ℝ) * B ≤ 4 * S := by dsimp [S]; nlinarith
  have hABpow : (A : ℝ) ^ (η / 2) * (B : ℝ) ^ (η / 2) ≤
      2 ^ η * S ^ (η / 2) := by
    rw [← Real.mul_rpow hA0.le hB0.le]
    have hp := Real.rpow_le_rpow (mul_nonneg hA0.le hB0.le) hAB
      (by positivity : 0 ≤ η / 2)
    calc
      ((A : ℝ) * B) ^ (η / 2) ≤ (4 * S) ^ (η / 2) := hp
      _ = 2 ^ η * S ^ (η / 2) := by
        rw [Real.mul_rpow (by norm_num) hS0.le]
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
          show (2 : ℝ) ^ (2 : ℕ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have hXYpow :
      X ^ (1 / 2 + η / 2) * Y ^ (1 / 2 + η / 2) =
        S ^ (1 / 2 : ℝ) * S ^ (η / 2) := by
    rw [Real.rpow_add hX0, Real.rpow_add hY0,
      show X ^ (1 / 2 : ℝ) * X ^ (η / 2) *
          (Y ^ (1 / 2 : ℝ) * Y ^ (η / 2)) =
        (X ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) *
          (X ^ (η / 2) * Y ^ (η / 2)) by ring,
      ← Real.mul_rpow hX0.le hY0.le,
      ← Real.mul_rpow hX0.le hY0.le]
  let e : ℝ := (-2 + η) * (3 / 4 + η / 2)
  have he : 2 * e ≤ -(3 : ℝ) := by
    dsimp [e]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hη.le
      (by linarith : η - 1 / 2 ≤ 0)]
  have hQpow : Q ^ e * Q ^ e ≤ Q ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by simpa [two_mul] using he)
  have hLog : Real.log Q ≤ (8 / ε) * S ^ η := by
    have hraw := Real.log_le_rpow_div hQ0.le hη
    have hpow := Real.rpow_le_rpow hQ0.le (by simpa [S] using hQXY) hη.le
    calc
      Real.log Q ≤ Q ^ η / η := hraw
      _ ≤ S ^ η / η := by gcongr
      _ = (8 / ε) * S ^ η := by
        dsimp [η]
        field_simp [ne_of_gt hε0]
  have hLossPowers :
      S ^ (η / 2) * S ^ (η / 2) * S ^ η * (S ^ η) ^ 3 ≤ S ^ ε := by
    rw [show (S ^ η) ^ 3 = S ^ (3 * η) by
      rw [show (S ^ η) ^ 3 = (S ^ η) ^ (3 : ℝ) by norm_num,
        ← Real.rpow_mul hS0.le]
      congr 1
      ring,
      ← Real.rpow_add hS0, ← Real.rpow_add hS0,
      ← Real.rpow_add hS0]
    exact Real.rpow_le_rpow_of_exponent_le hS1 (by dsimp [η]; linarith)
  have hMin0 : 0 ≤ min X Y := le_min hX0.le hY0.le
  have hLog0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hAvg0 : 0 ≤ dfiEquation29ThreeGcdAverage H A B Q η := by
    unfold dfiEquation29ThreeGcdAverage
    exact mul_nonneg
      (mul_nonneg (divisorEpsilonConstant_pos η).le
        (zero_le_one.trans (le_max_left _ _)))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  change ((2 ^ (3 / 4 + η / 2) * 2 ^ (3 / 4 + η / 2)) *
      X ^ (1 / 2 + η / 2) * Y ^ (1 / 2 + η / 2) *
      (A : ℝ) ^ (η / 2) * (B : ℝ) ^ (η / 2) *
      (Q ^ e * Q ^ e) * (min X Y * Real.log Q)) *
      dfiEquation29ThreeGcdAverage H A B Q η ≤ _
  calc
    _ = (2 ^ (3 / 4 + η / 2) * 2 ^ (3 / 4 + η / 2)) *
        (X ^ (1 / 2 + η / 2) * Y ^ (1 / 2 + η / 2)) *
        ((A : ℝ) ^ (η / 2) * (B : ℝ) ^ (η / 2)) *
        (Q ^ e * Q ^ e) * (min X Y * Real.log Q) *
        dfiEquation29ThreeGcdAverage H A B Q η := by ring
    _ ≤ (2 ^ (3 / 4 + η / 2) * 2 ^ (3 / 4 + η / 2)) *
        (S ^ (1 / 2 : ℝ) * S ^ (η / 2)) *
        (2 ^ η * S ^ (η / 2)) * Q ^ (-(3 : ℝ)) *
        (min X Y * ((8 / ε) * S ^ η)) *
        (CA * Q ^ (1 / 2 : ℝ) * (S ^ η) ^ 3) := by
      rw [hXYpow]
      gcongr
    _ = ((2 ^ (3 / 4 + η / 2) * 2 ^ (3 / 4 + η / 2)) *
        2 ^ η * (8 / ε) * CA) *
        (((S ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
          Q ^ (1 / 2 : ℝ)) *
          (S ^ (η / 2) * S ^ (η / 2) * S ^ η * (S ^ η) ^ 3)) := by ring
    _ ≤ ((2 ^ (3 / 4 + η / 2) * 2 ^ (3 / 4 + η / 2)) *
        2 ^ η * (8 / ε) * CA) *
        (((S ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
          Q ^ (1 / 2 : ℝ)) * S ^ ε) := by gcongr
    _ = _ := by dsimp [η, S]; ring

theorem dfiEquation29_xRetained_loss_bundle_le
    {X Y Q ε CL CA : ℝ} {H A B : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y) (hA : 0 < A) (hAX : (A : ℝ) ≤ 2 * X)
    (hε0 : 0 < ε) (hε1 : ε ≤ 2)
    (hCL : 0 ≤ CL) (hCA : 0 ≤ CA)
    (hLog : dfiEquation29XSingleLogMajorant Q Y B ≤
      CL * (X * Y) ^ (ε / 8))
    (hAverage : dfiEquation29TwoGcdAverage H A Q (ε / 8) ≤
      CA * ((X * Y) ^ (ε / 8)) ^ 3) :
    dfiEquation29XSingleLogMajorant Q Y B *
        (X ^ (1 / 2 + ε / 8) * (A : ℝ) ^ (ε / 8) *
          Q ^ ((-2 + ε / 8) * (3 / 4 + ε / 8)) *
          (min X Y * Real.log Q)) *
        dfiEquation29TwoGcdAverage H A Q (ε / 8) ≤
      (2 ^ (ε / 8) * (8 / ε) * CL * CA) *
        (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
        (X * Y) ^ ε := by
  let η : ℝ := ε / 8
  let S : ℝ := X * Y
  have hη : 0 < η := by dsimp [η]; positivity
  have hηquarter : η ≤ 1 / 4 := by dsimp [η]; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hS0 : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith
  have hXS : X ≤ S := by dsimp [S]; nlinarith
  have hExp : (-2 + η) * (3 / 4 + η) ≤ -(3 / 2 : ℝ) := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hη.le (by linarith : η - 5 / 4 ≤ 0)]
  have hQpow : Q ^ ((-2 + η) * (3 / 4 + η)) ≤
      Q ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ hExp
  have hAPow : (A : ℝ) ^ η ≤ 2 ^ η * X ^ η := by
    have h := Real.rpow_le_rpow hA0.le hAX hη.le
    calc
      (A : ℝ) ^ η ≤ (2 * X) ^ η := h
      _ = 2 ^ η * X ^ η := by
        rw [Real.mul_rpow (by norm_num) hX0.le]
  have hXpowS : X ^ η ≤ S ^ η :=
    Real.rpow_le_rpow hX0.le hXS hη.le
  have hLogQ : Real.log Q ≤ (8 / ε) * S ^ η := by
    have hraw := Real.log_le_rpow_div hQ0.le hη
    have hQS : Q ≤ S := by simpa only [S] using hQXY
    have hpow := Real.rpow_le_rpow hQ0.le hQS hη.le
    calc
      Real.log Q ≤ Q ^ η / η := hraw
      _ ≤ S ^ η / η := by gcongr
      _ = (8 / ε) * S ^ η := by
        dsimp [η]
        field_simp [ne_of_gt hε0]
  have hXsplit : X ^ (1 / 2 + η) = X ^ (1 / 2 : ℝ) * X ^ η := by
    rw [Real.rpow_add hX0]
  have hSeven : (S ^ η) ^ 7 ≤ S ^ ε := by
    rw [show (S ^ η) ^ 7 = S ^ (7 * η) by
      rw [show (S ^ η) ^ 7 = (S ^ η) ^ (7 : ℝ) by norm_num,
        ← Real.rpow_mul hS0.le]
      congr 1
      ring]
    exact Real.rpow_le_rpow_of_exponent_le hS1 (by dsimp [η]; linarith)
  have hMin0 : 0 ≤ min X Y := le_min hX0.le hY0.le
  have hLogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hAvg0 : 0 ≤ dfiEquation29TwoGcdAverage H A Q η := by
    unfold dfiEquation29TwoGcdAverage
    exact mul_nonneg
      (mul_nonneg (divisorEpsilonConstant_pos η).le
        (zero_le_one.trans (le_max_left _ _)))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  change dfiEquation29XSingleLogMajorant Q Y B *
      (X ^ (1 / 2 + η) * (A : ℝ) ^ η *
        Q ^ ((-2 + η) * (3 / 4 + η)) *
        (min X Y * Real.log Q)) *
      dfiEquation29TwoGcdAverage H A Q η ≤ _
  rw [hXsplit]
  calc
    _ ≤ (CL * S ^ η) *
        ((X ^ (1 / 2 : ℝ) * S ^ η) *
          (2 ^ η * S ^ η) * Q ^ (-(3 / 2 : ℝ)) *
          (min X Y * ((8 / ε) * S ^ η))) *
        (CA * (S ^ η) ^ 3) := by
      gcongr
      exact hAPow.trans (mul_le_mul_of_nonneg_left hXpowS
        (Real.rpow_nonneg (by norm_num) η))
    _ = (2 ^ η * (8 / ε) * CL * CA) *
        (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
        (S ^ η) ^ 7 := by ring
    _ ≤ (2 ^ η * (8 / ε) * CL * CA) *
        (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
        S ^ ε := by gcongr
    _ = _ := by dsimp [η, S]

/-- The retained `x`-dual part of equation (29), summed over all delta
moduli, already has DFI Theorem 1 strength in the nonempty source range.
This theorem consumes the actual profile-derived retained estimate; its
constant is selected before `a`, `b`, and the shift. -/
theorem exists_sum_dfiEquation29_xSingleRetained_le_theorem1ErrorScale
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q ε : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε2 : ε < 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b h : ℕ), 0 < a → 0 < b → 0 < h →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 8) q) ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  let η : ℝ := ε / 8
  let CL : ℝ := 8 * Real.log 2 + 6 * η⁻¹ +
    2 * |Real.eulerMascheroniConstant|
  let CA : ℝ := divisorEpsilonConstant η * 3 ^ η *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) *
        ((1 + η⁻¹) * 3 ^ η)) *
      Real.sqrt ((divisorEpsilonConstant η * 2 ^ η) *
        ((1 + η⁻¹) * 3 ^ η))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηquarter : η < 1 / 4 := by dsimp [η]; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have hXY0 : 0 < X * Y := mul_pos hX0 hY0
  have hXY1 : 1 ≤ X * Y := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ X * Y := mul_le_mul hf.one_le_X hf.one_le_Y
        zero_le_one (zero_le_one.trans hf.one_le_X)
  have hQsqLeX :=
    (dfiEquation30_optimized_Q_sq_le_lengths hf.one_le_P hX0 hY0 hQsq).1
  have hQXY : Q ≤ X * Y := by
    have hQQ : Q ≤ Q ^ 2 := by nlinarith
    have hXXY : X ≤ X * Y := by
      calc
        X = X * 1 := by ring
        _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
    exact hQQ.trans (hQsqLeX.trans hXXY)
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hCA : 0 ≤ CA := by
    dsimp [CA]
    have hD : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    have hK : 0 ≤ 1 + η⁻¹ := by positivity
    have hThree : 0 ≤ (3 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hFour : 0 ≤ (4 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hTwo : 0 ≤ (2 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    positivity
  obtain ⟨C₀, hC₀, hRetained⟩ :=
    exists_sum_dfiEquation29_xSingleRetained_optimized_le
      hf hfC hbox hφ hφC hscale w hwC hQ hU hf.one_le_P hQsq
        η hη hηquarter η hη
  let B : ℝ := 2 ^ η * (8 / ε) * CL * CA
  let Ccore : ℝ := 2 * C₀ * 2 ^ (3 / 4 + η) * B
  let Cfinal : ℝ := 1 + Ccore * Real.sqrt 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro a b h ha hb hh haX hbY hhX
  have hhXY : (h : ℝ) ≤ 4 * (X * Y) := by
    calc
      (h : ℝ) ≤ 2 * X := hhX
      _ ≤ 4 * (X * Y) := by
        have hXXY : X ≤ X * Y := by
          calc
            X = X * 1 := by ring
            _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
        nlinarith
  have haXY : (a : ℝ) ≤ 2 * (X * Y) := by
    calc
      (a : ℝ) ≤ 2 * X := haX
      _ ≤ 2 * (X * Y) := by
        have hXXY : X ≤ X * Y := by
          calc
            X = X * 1 := by ring
            _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
        exact mul_le_mul_of_nonneg_left hXXY (by norm_num)
  have hLog : dfiEquation29XSingleLogMajorant Q Y b ≤
      CL * (X * Y) ^ η := by
    simpa only [CL] using dfiEquation29XSingleLogMajorant_le_rpow
      hf.one_le_X hf.one_le_Y (by linarith) hQXY hb hbY hη
  have hAverage : dfiEquation29TwoGcdAverage h a Q η ≤
      CA * ((X * Y) ^ η) ^ 3 := by
    simpa only [dfiEquation29TwoGcdAverage, CA] using
      dfiEquation29_twoGcdAverageLoss_le_rpow
        hf.one_le_X hf.one_le_Y (by linarith) hQXY hh.ne' ha.ne'
          hhXY haXY hη
  have hLoss :
      dfiEquation29XSingleLogMajorant Q Y b *
          (X ^ (1 / 2 + η) * (a : ℝ) ^ η *
            Q ^ ((-2 + η) * (3 / 4 + η)) *
            (min X Y * Real.log Q)) *
          dfiEquation29TwoGcdAverage h a Q η ≤
        B * (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
          (X * Y) ^ ε := by
    simpa only [B, η] using dfiEquation29_xRetained_loss_bundle_le
      hf.one_le_X hf.one_le_Y (by linarith) hQXY ha haX hε0 hε2.le
        hCL hCA hLog hAverage
  have hRaw := hRetained a b ha hb (h : ℤ) (by exact_mod_cast hh.ne')
  have hRaw' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h η q) ≤
        Ccore *
          (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
          (X * Y) ^ ε := by
    calc
      _ ≤ ((2 * C₀ * dfiEquation29XSingleLogMajorant Q Y b) *
          (2 ^ (3 / 4 + η) * X ^ (1 / 2 + η) * (a : ℝ) ^ η *
            Q ^ ((-2 + η) * (3 / 4 + η)) *
            (min X Y * Real.log Q))) *
          dfiEquation29TwoGcdAverage h a Q η := by
          simpa only [dfiEquation29TwoGcdAverage] using hRaw
      _ = (2 * C₀ * 2 ^ (3 / 4 + η)) *
          (dfiEquation29XSingleLogMajorant Q Y b *
            (X ^ (1 / 2 + η) * (a : ℝ) ^ η *
              Q ^ ((-2 + η) * (3 / 4 + η)) *
              (min X Y * Real.log Q)) *
            dfiEquation29TwoGcdAverage h a Q η) := by ring
      _ ≤ (2 * C₀ * 2 ^ (3 / 4 + η)) *
          (B * (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
            (X * Y) ^ ε) := by gcongr
      _ = _ := by dsimp [Ccore]; ring
  have hCore := dfiEquation29_xRetained_zeroEpsilon_le_secondError
    hf.one_le_P hf.one_le_X hf.one_le_Y hQ0 hQsq
  have hSecondNonneg : 0 ≤
      (X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)) := by
    positivity
  calc
    _ ≤ Ccore *
        (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
        (X * Y) ^ ε := hRaw'
    _ ≤ Ccore * (Real.sqrt 2 *
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)))) *
        (X * Y) ^ ε := by gcongr
    _ = (Ccore * Real.sqrt 2) * dfiTheorem1ErrorScale P X Y ε := by
      rw [← dfiEquation30_second_with_epsilon_eq_theorem1ErrorScale
        (zero_lt_one.trans_le hf.one_le_P) hX0 hY0 hQ0 hQsq]
      ring
    _ ≤ Cfinal * dfiTheorem1ErrorScale P X Y ε := by
      have hTarget : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
        unfold dfiTheorem1ErrorScale
        exact mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans hf.one_le_P) _)
            (Real.rpow_nonneg (add_nonneg hX0.le hY0.le) _))
          (Real.rpow_nonneg hXY0.le _)
      gcongr
      dsimp [Cfinal]
      linarith

set_option maxHeartbeats 800000 in
/-- The discarded `x`-dual modes in equation (29), summed over the
equation-(22) moduli, satisfy the same Theorem 1 error scale.  Taking one
Bessel recurrence is enough because the source-sharp `L¹` estimate supplies
the extra factor `Q^(-ε/8)`. -/
theorem exists_sum_dfiEquation29_xSingleTail_le_theorem1ErrorScale
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q ε : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε2 : ε < 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b h : ℕ), 0 < a → 0 < b → 0 < h →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 8) q) ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  let η : ℝ := ε / 8
  let CL : ℝ := 8 * Real.log 2 + 6 * η⁻¹ +
    2 * |Real.eulerMascheroniConstant|
  let CA : ℝ := divisorEpsilonConstant η * 3 ^ η *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) *
        ((1 + η⁻¹) * 3 ^ η)) *
      Real.sqrt ((divisorEpsilonConstant η * 2 ^ η) *
        ((1 + η⁻¹) * 3 ^ η))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηquarter : η < 1 / 4 := by dsimp [η]; linarith
  have hk : η + 3 / 4 < ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have hXY0 : 0 < X * Y := mul_pos hX0 hY0
  have hXY1 : 1 ≤ X * Y := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ X * Y := mul_le_mul hf.one_le_X hf.one_le_Y
        zero_le_one (zero_le_one.trans hf.one_le_X)
  have hQsqLeX :=
    (dfiEquation30_optimized_Q_sq_le_lengths hf.one_le_P hX0 hY0 hQsq).1
  have hQXY : Q ≤ X * Y := by
    have hQQ : Q ≤ Q ^ 2 := by nlinarith
    have hXXY : X ≤ X * Y := by
      calc
        X = X * 1 := by ring
        _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
    exact hQQ.trans (hQsqLeX.trans hXXY)
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hCA : 0 ≤ CA := by
    dsimp [CA]
    have hD : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    have hK : 0 ≤ 1 + η⁻¹ := by positivity
    have hThree : 0 ≤ (3 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hFour : 0 ≤ (4 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hTwo : 0 ≤ (2 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    positivity
  obtain ⟨C₀, D₀, hC₀, hD₀, hTail⟩ :=
    exists_sum_dfiEquation29_xSingleTail_l1_optimized_le
      hf hfC hbox hφ hφC hscale w hwC hU hf.one_le_P hQ hQsq
        η hη 1 hk η hη
  let B : ℝ := 2 ^ η * (8 / ε) * CL * CA
  let R : ℝ :=
    2 * (C₀ * D₀ * (14 * Real.pi + 8) / ((1 : ℝ) - η - 3 / 4)) *
      (5 / Real.pi ^ 2) * 2 ^ (3 / 4 + η)
  let Ccore : ℝ := R * B
  let Cfinal : ℝ := 1 + Ccore * Real.sqrt 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hden : 0 < (1 : ℝ) - η - 3 / 4 := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro a b h ha hb hh haX hbY hhX
  have hhXY : (h : ℝ) ≤ 4 * (X * Y) := by
    calc
      (h : ℝ) ≤ 2 * X := hhX
      _ ≤ 4 * (X * Y) := by
        have hXXY : X ≤ X * Y := by
          calc
            X = X * 1 := by ring
            _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
        nlinarith
  have haXY : (a : ℝ) ≤ 2 * (X * Y) := by
    calc
      (a : ℝ) ≤ 2 * X := haX
      _ ≤ 2 * (X * Y) := by
        have hXXY : X ≤ X * Y := by
          calc
            X = X * 1 := by ring
            _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
        exact mul_le_mul_of_nonneg_left hXXY (by norm_num)
  have hLog : dfiEquation29XSingleLogMajorant Q Y b ≤
      CL * (X * Y) ^ η := by
    simpa only [CL] using dfiEquation29XSingleLogMajorant_le_rpow
      hf.one_le_X hf.one_le_Y (by linarith) hQXY hb hbY hη
  have hAverage : dfiEquation29TwoGcdAverage h a Q η ≤
      CA * ((X * Y) ^ η) ^ 3 := by
    simpa only [dfiEquation29TwoGcdAverage, CA] using
      dfiEquation29_twoGcdAverageLoss_le_rpow
        hf.one_le_X hf.one_le_Y (by linarith) hQXY hh.ne' ha.ne'
          hhXY haXY hη
  have hLoss :
      dfiEquation29XSingleLogMajorant Q Y b *
          (X ^ (1 / 2 + η) * (a : ℝ) ^ η *
            Q ^ ((-2 + η) * (3 / 4 + η)) *
            (min X Y * Real.log Q)) *
          dfiEquation29TwoGcdAverage h a Q η ≤
        B * (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
          (X * Y) ^ ε := by
    simpa only [B, η] using dfiEquation29_xRetained_loss_bundle_le
      hf.one_le_X hf.one_le_Y (by linarith) hQXY ha haX hε0 hε2.le
        hCL hCA hLog hAverage
  have hQneg : Q ^ (-η) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hLoss0 : 0 ≤
      dfiEquation29XSingleLogMajorant Q Y b *
          (X ^ (1 / 2 + η) * (a : ℝ) ^ η *
            Q ^ ((-2 + η) * (3 / 4 + η)) *
            (min X Y * Real.log Q)) *
          dfiEquation29TwoGcdAverage h a Q η := by
    have hMaj0 : 0 ≤ dfiEquation29XSingleLogMajorant Q Y b := by
      unfold dfiEquation29XSingleLogMajorant
      have hlog2Q : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
      nlinarith [abs_nonneg (Real.log (Y / b)),
        abs_nonneg (Real.log (2 * Y / b)),
        abs_nonneg Real.eulerMascheroniConstant]
    have hAvg0 : 0 ≤ dfiEquation29TwoGcdAverage h a Q η := by
      unfold dfiEquation29TwoGcdAverage
      exact mul_nonneg
        (mul_nonneg (divisorEpsilonConstant_pos η).le
          (zero_le_one.trans (le_max_left _ _)))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hlog2Q : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hRaw := hTail a b ha hb (h : ℤ) (by exact_mod_cast hh.ne')
  have hRaw' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h η q) ≤
        Ccore *
          (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
          (X * Y) ^ ε := by
    calc
      _ ≤ R * Q ^ (-η) *
          (dfiEquation29XSingleLogMajorant Q Y b *
            (X ^ (1 / 2 + η) * (a : ℝ) ^ η *
              Q ^ ((-2 + η) * (3 / 4 + η)) *
              (min X Y * Real.log Q)) *
            dfiEquation29TwoGcdAverage h a Q η) := by
          convert hRaw using 1
          all_goals simp [dfiEquation29TwoGcdAverage, R, η]
          all_goals ring
      _ ≤ R * 1 *
          (dfiEquation29XSingleLogMajorant Q Y b *
            (X ^ (1 / 2 + η) * (a : ℝ) ^ η *
              Q ^ ((-2 + η) * (3 / 4 + η)) *
              (min X Y * Real.log Q)) *
            dfiEquation29TwoGcdAverage h a Q η) := by gcongr
      _ = R *
          (dfiEquation29XSingleLogMajorant Q Y b *
            (X ^ (1 / 2 + η) * (a : ℝ) ^ η *
              Q ^ ((-2 + η) * (3 / 4 + η)) *
              (min X Y * Real.log Q)) *
            dfiEquation29TwoGcdAverage h a Q η) := by ring
      _ ≤ R *
          (B * (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
            (X * Y) ^ ε) := mul_le_mul_of_nonneg_left hLoss hR
      _ = _ := by dsimp [Ccore]; ring
  have hCore := dfiEquation29_xRetained_zeroEpsilon_le_secondError
    hf.one_le_P hf.one_le_X hf.one_le_Y hQ0 hQsq
  calc
    _ ≤ Ccore *
        (X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
        (X * Y) ^ ε := hRaw'
    _ ≤ Ccore * (Real.sqrt 2 *
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)))) *
        (X * Y) ^ ε := by gcongr
    _ = (Ccore * Real.sqrt 2) * dfiTheorem1ErrorScale P X Y ε := by
      rw [← dfiEquation30_second_with_epsilon_eq_theorem1ErrorScale
        (zero_lt_one.trans_le hf.one_le_P) hX0 hY0 hQ0 hQsq]
      ring
    _ ≤ Cfinal * dfiTheorem1ErrorScale P X Y ε := by
      have hTarget : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
        unfold dfiTheorem1ErrorScale
        exact mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans hf.one_le_P) _)
            (Real.rpow_nonneg (add_nonneg hX0.le hY0.le) _))
          (Real.rpow_nonneg hXY0.le _)
      gcongr
      dsimp [Cfinal]
      linarith

/-- The retained `y`-dual part of equation (29), summed over all delta
moduli, has DFI Theorem 1 strength in the nonempty source range.  This is
proved from the actual `y`-retained source estimate, with a constant chosen
before the arithmetic parameters. -/
theorem exists_sum_dfiEquation29_ySingleRetained_le_theorem1ErrorScale
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q ε : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε2 : ε < 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b h : ℕ), 0 < a → 0 < b → 0 < h →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 8) q) ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  let η : ℝ := ε / 8
  let CL : ℝ := 8 * Real.log 2 + 6 * η⁻¹ +
    2 * |Real.eulerMascheroniConstant|
  let CA : ℝ := divisorEpsilonConstant η * 3 ^ η *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) *
        ((1 + η⁻¹) * 3 ^ η)) *
      Real.sqrt ((divisorEpsilonConstant η * 2 ^ η) *
        ((1 + η⁻¹) * 3 ^ η))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηquarter : η < 1 / 4 := by dsimp [η]; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have hXY0 : 0 < X * Y := mul_pos hX0 hY0
  have hQsqLeX :=
    (dfiEquation30_optimized_Q_sq_le_lengths hf.one_le_P hX0 hY0 hQsq).1
  have hQXY : Q ≤ X * Y := by
    have hQQ : Q ≤ Q ^ 2 := by nlinarith
    have hXXY : X ≤ X * Y := by
      calc
        X = X * 1 := by ring
        _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
    exact hQQ.trans (hQsqLeX.trans hXXY)
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hCA : 0 ≤ CA := by
    dsimp [CA]
    have hD : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    have hK : 0 ≤ 1 + η⁻¹ := by positivity
    have hThree : 0 ≤ (3 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hFour : 0 ≤ (4 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hTwo : 0 ≤ (2 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    positivity
  obtain ⟨C₀, hC₀, hRetained⟩ :=
    exists_sum_dfiEquation29_ySingleRetained_optimized_le
      hf hfC hbox hφ hφC hscale w hwC hQ hU hf.one_le_P hQsq
        η hη hηquarter η hη
  let B : ℝ := 2 ^ η * (8 / ε) * CL * CA
  let Ccore : ℝ := 2 * C₀ * 2 ^ (3 / 4 + η) * B
  let Cfinal : ℝ := 1 + Ccore * Real.sqrt 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro a b h ha hb hh haX hbY hhX
  have hhXY : (h : ℝ) ≤ 4 * (X * Y) := by
    calc
      (h : ℝ) ≤ 2 * X := hhX
      _ ≤ 4 * (X * Y) := by
        have hXXY : X ≤ X * Y := by
          calc
            X = X * 1 := by ring
            _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
        nlinarith
  have hbXY : (b : ℝ) ≤ 2 * (X * Y) := by
    calc
      (b : ℝ) ≤ 2 * Y := hbY
      _ ≤ 2 * (X * Y) := by
        have hYXY : Y ≤ X * Y := by
          calc
            Y = 1 * Y := by ring
            _ ≤ X * Y := mul_le_mul_of_nonneg_right hf.one_le_X hY0.le
        exact mul_le_mul_of_nonneg_left hYXY (by norm_num)
  have hLog : dfiEquation29YSingleLogMajorant Q X a ≤
      CL * (X * Y) ^ η := by
    simpa only [CL] using dfiEquation29YSingleLogMajorant_le_rpow
      hf.one_le_X hf.one_le_Y (by linarith) hQXY ha haX hη
  have hAverage : dfiEquation29TwoGcdAverage h b Q η ≤
      CA * ((X * Y) ^ η) ^ 3 := by
    simpa only [dfiEquation29TwoGcdAverage, CA] using
      dfiEquation29_twoGcdAverageLoss_le_rpow
        hf.one_le_X hf.one_le_Y (by linarith) hQXY hh.ne' hb.ne'
          hhXY hbXY hη
  have hQYX : Q ≤ Y * X := by simpa [mul_comm] using hQXY
  have hLogX : dfiEquation29XSingleLogMajorant Q X a ≤
      CL * (Y * X) ^ η := by
    simpa [dfiEquation29XSingleLogMajorant,
      dfiEquation29YSingleLogMajorant, mul_comm] using hLog
  have hAverageSwap : dfiEquation29TwoGcdAverage h b Q η ≤
      CA * ((Y * X) ^ η) ^ 3 := by
    simpa [mul_comm] using hAverage
  have hLoss :
      dfiEquation29YSingleLogMajorant Q X a *
          (Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
            Q ^ ((-2 + η) * (3 / 4 + η)) *
            (min X Y * Real.log Q)) *
          dfiEquation29TwoGcdAverage h b Q η ≤
        B * (Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
          (X * Y) ^ ε := by
    have hSwap := dfiEquation29_xRetained_loss_bundle_le
      hf.one_le_Y hf.one_le_X (by linarith) hQYX hb hbY hε0 hε2.le
        hCL hCA hLogX hAverageSwap
    simpa only [B, η, min_comm, mul_comm Y X] using hSwap
  have hRaw := hRetained a b ha hb (h : ℤ) (by exact_mod_cast hh.ne')
  have hRaw' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h η q) ≤
        Ccore *
          (Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
          (X * Y) ^ ε := by
    calc
      _ ≤ ((2 * C₀ * dfiEquation29YSingleLogMajorant Q X a) *
          (2 ^ (3 / 4 + η) * Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
            Q ^ ((-2 + η) * (3 / 4 + η)) *
            (min X Y * Real.log Q))) *
          dfiEquation29TwoGcdAverage h b Q η := by
          simpa only [dfiEquation29TwoGcdAverage] using hRaw
      _ = (2 * C₀ * 2 ^ (3 / 4 + η)) *
          (dfiEquation29YSingleLogMajorant Q X a *
            (Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
              Q ^ ((-2 + η) * (3 / 4 + η)) *
              (min X Y * Real.log Q)) *
            dfiEquation29TwoGcdAverage h b Q η) := by ring
      _ ≤ (2 * C₀ * 2 ^ (3 / 4 + η)) *
          (B * (Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
            (X * Y) ^ ε) := by gcongr
      _ = _ := by dsimp [Ccore]; ring
  have hCore := dfiEquation29_yRetained_zeroEpsilon_le_secondError
    hf.one_le_P hf.one_le_X hf.one_le_Y hQ0 hQsq
  calc
    _ ≤ Ccore *
        (Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
        (X * Y) ^ ε := hRaw'
    _ ≤ Ccore * (Real.sqrt 2 *
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)))) *
        (X * Y) ^ ε := by gcongr
    _ = (Ccore * Real.sqrt 2) * dfiTheorem1ErrorScale P X Y ε := by
      rw [← dfiEquation30_second_with_epsilon_eq_theorem1ErrorScale
        (zero_lt_one.trans_le hf.one_le_P) hX0 hY0 hQ0 hQsq]
      ring
    _ ≤ Cfinal * dfiTheorem1ErrorScale P X Y ε := by
      have hTarget : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
        unfold dfiTheorem1ErrorScale
        exact mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans hf.one_le_P) _)
            (Real.rpow_nonneg (add_nonneg hX0.le hY0.le) _))
          (Real.rpow_nonneg hXY0.le _)
      gcongr
      dsimp [Cfinal]
      linarith

set_option maxHeartbeats 800000 in
/-- The discarded `y`-dual modes in equation (29), summed over the
equation-(22) moduli, satisfy the DFI Theorem 1 error scale. -/
theorem exists_sum_dfiEquation29_ySingleTail_le_theorem1ErrorScale
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q ε : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε2 : ε < 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b h : ℕ), 0 < a → 0 < b → 0 < h →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 8) q) ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  let η : ℝ := ε / 8
  let CL : ℝ := 8 * Real.log 2 + 6 * η⁻¹ +
    2 * |Real.eulerMascheroniConstant|
  let CA : ℝ := divisorEpsilonConstant η * 3 ^ η *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) *
        ((1 + η⁻¹) * 3 ^ η)) *
      Real.sqrt ((divisorEpsilonConstant η * 2 ^ η) *
        ((1 + η⁻¹) * 3 ^ η))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηquarter : η < 1 / 4 := by dsimp [η]; linarith
  have hk : η + 3 / 4 < ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have hXY0 : 0 < X * Y := mul_pos hX0 hY0
  have hQsqLeX :=
    (dfiEquation30_optimized_Q_sq_le_lengths hf.one_le_P hX0 hY0 hQsq).1
  have hQXY : Q ≤ X * Y := by
    have hQQ : Q ≤ Q ^ 2 := by nlinarith
    have hXXY : X ≤ X * Y := by
      calc
        X = X * 1 := by ring
        _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
    exact hQQ.trans (hQsqLeX.trans hXXY)
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hCA : 0 ≤ CA := by
    dsimp [CA]
    have hD : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    have hK : 0 ≤ 1 + η⁻¹ := by positivity
    have hThree : 0 ≤ (3 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hFour : 0 ≤ (4 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hTwo : 0 ≤ (2 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    positivity
  obtain ⟨C₀, D₀, hC₀, hD₀, hTail⟩ :=
    exists_sum_dfiEquation29_ySingleTail_l1_optimized_le
      hf hfC hbox hφ hφC hscale w hwC hU hf.one_le_P hQ hQsq
        η hη 1 hk η hη
  let B : ℝ := 2 ^ η * (8 / ε) * CL * CA
  let R : ℝ :=
    2 * (C₀ * D₀ * (14 * Real.pi + 8) / ((1 : ℝ) - η - 3 / 4)) *
      (5 / Real.pi ^ 2) * 2 ^ (3 / 4 + η)
  let Ccore : ℝ := R * B
  let Cfinal : ℝ := 1 + Ccore * Real.sqrt 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hden : 0 < (1 : ℝ) - η - 3 / 4 := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro a b h ha hb hh haX hbY hhX
  have hhXY : (h : ℝ) ≤ 4 * (X * Y) := by
    calc
      (h : ℝ) ≤ 2 * X := hhX
      _ ≤ 4 * (X * Y) := by
        have hXXY : X ≤ X * Y := by
          calc
            X = X * 1 := by ring
            _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
        nlinarith
  have hbXY : (b : ℝ) ≤ 2 * (X * Y) := by
    calc
      (b : ℝ) ≤ 2 * Y := hbY
      _ ≤ 2 * (X * Y) := by
        have hYXY : Y ≤ X * Y := by
          calc
            Y = 1 * Y := by ring
            _ ≤ X * Y := mul_le_mul_of_nonneg_right hf.one_le_X hY0.le
        exact mul_le_mul_of_nonneg_left hYXY (by norm_num)
  have hLog : dfiEquation29YSingleLogMajorant Q X a ≤
      CL * (X * Y) ^ η := by
    simpa only [CL] using dfiEquation29YSingleLogMajorant_le_rpow
      hf.one_le_X hf.one_le_Y (by linarith) hQXY ha haX hη
  have hAverage : dfiEquation29TwoGcdAverage h b Q η ≤
      CA * ((X * Y) ^ η) ^ 3 := by
    simpa only [dfiEquation29TwoGcdAverage, CA] using
      dfiEquation29_twoGcdAverageLoss_le_rpow
        hf.one_le_X hf.one_le_Y (by linarith) hQXY hh.ne' hb.ne'
          hhXY hbXY hη
  have hQYX : Q ≤ Y * X := by simpa [mul_comm] using hQXY
  have hLogX : dfiEquation29XSingleLogMajorant Q X a ≤
      CL * (Y * X) ^ η := by
    simpa [dfiEquation29XSingleLogMajorant,
      dfiEquation29YSingleLogMajorant, mul_comm] using hLog
  have hAverageSwap : dfiEquation29TwoGcdAverage h b Q η ≤
      CA * ((Y * X) ^ η) ^ 3 := by
    simpa [mul_comm] using hAverage
  have hLoss :
      dfiEquation29YSingleLogMajorant Q X a *
          (Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
            Q ^ ((-2 + η) * (3 / 4 + η)) *
            (min X Y * Real.log Q)) *
          dfiEquation29TwoGcdAverage h b Q η ≤
        B * (Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
          (X * Y) ^ ε := by
    have hSwap := dfiEquation29_xRetained_loss_bundle_le
      hf.one_le_Y hf.one_le_X (by linarith) hQYX hb hbY hε0 hε2.le
        hCL hCA hLogX hAverageSwap
    simpa only [B, η, min_comm, mul_comm Y X] using hSwap
  have hQneg : Q ^ (-η) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hLoss0 : 0 ≤
      dfiEquation29YSingleLogMajorant Q X a *
          (Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
            Q ^ ((-2 + η) * (3 / 4 + η)) *
            (min X Y * Real.log Q)) *
          dfiEquation29TwoGcdAverage h b Q η := by
    have hMaj0 : 0 ≤ dfiEquation29YSingleLogMajorant Q X a := by
      unfold dfiEquation29YSingleLogMajorant
      have hlog2Q : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
      nlinarith [abs_nonneg (Real.log (X / a)),
        abs_nonneg (Real.log (2 * X / a)),
        abs_nonneg Real.eulerMascheroniConstant]
    have hAvg0 : 0 ≤ dfiEquation29TwoGcdAverage h b Q η := by
      unfold dfiEquation29TwoGcdAverage
      exact mul_nonneg
        (mul_nonneg (divisorEpsilonConstant_pos η).le
          (zero_le_one.trans (le_max_left _ _)))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hRaw := hTail a b ha hb (h : ℤ) (by exact_mod_cast hh.ne')
  have hRaw' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h η q) ≤
        Ccore *
          (Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
          (X * Y) ^ ε := by
    calc
      _ ≤ R * Q ^ (-η) *
          (dfiEquation29YSingleLogMajorant Q X a *
            (Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
              Q ^ ((-2 + η) * (3 / 4 + η)) *
              (min X Y * Real.log Q)) *
            dfiEquation29TwoGcdAverage h b Q η) := by
          convert hRaw using 1
          all_goals simp [dfiEquation29TwoGcdAverage, R, η]
          all_goals ring
      _ ≤ R * 1 *
          (dfiEquation29YSingleLogMajorant Q X a *
            (Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
              Q ^ ((-2 + η) * (3 / 4 + η)) *
              (min X Y * Real.log Q)) *
            dfiEquation29TwoGcdAverage h b Q η) := by gcongr
      _ = R *
          (dfiEquation29YSingleLogMajorant Q X a *
            (Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
              Q ^ ((-2 + η) * (3 / 4 + η)) *
              (min X Y * Real.log Q)) *
            dfiEquation29TwoGcdAverage h b Q η) := by ring
      _ ≤ R *
          (B * (Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
            (X * Y) ^ ε) := mul_le_mul_of_nonneg_left hLoss hR
      _ = _ := by dsimp [Ccore]; ring
  have hCore := dfiEquation29_yRetained_zeroEpsilon_le_secondError
    hf.one_le_P hf.one_le_X hf.one_le_Y hQ0 hQsq
  calc
    _ ≤ Ccore *
        (Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y) *
        (X * Y) ^ ε := hRaw'
    _ ≤ Ccore * (Real.sqrt 2 *
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)))) *
        (X * Y) ^ ε := by gcongr
    _ = (Ccore * Real.sqrt 2) * dfiTheorem1ErrorScale P X Y ε := by
      rw [← dfiEquation30_second_with_epsilon_eq_theorem1ErrorScale
        (zero_lt_one.trans_le hf.one_le_P) hX0 hY0 hQ0 hQsq]
      ring
    _ ≤ Cfinal * dfiTheorem1ErrorScale P X Y ε := by
      have hTarget : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
        unfold dfiTheorem1ErrorScale
        exact mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans hf.one_le_P) _)
            (Real.rpow_nonneg (add_nonneg hX0.le hY0.le) _))
          (Real.rpow_nonneg hXY0.le _)
      gcongr
      dsimp [Cfinal]
      linarith

/-- The complete retained double-dual rectangle in DFI equation (29) has
the published Theorem 1 strength throughout the nonempty source range. -/
theorem exists_sum_dfiEquation29_doubleRetained_le_theorem1ErrorScale
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q ε : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b h : ℕ), 0 < a → 0 < b → a.Coprime b → 0 < h →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 8) q) ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  let η : ℝ := ε / 8
  let CA : ℝ := divisorEpsilonConstant η * 3 ^ η *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) *
        ((1 + η⁻¹) * 3 ^ η)) *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) * 3)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηhalf : η < 1 / 2 := by dsimp [η]; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have hXY0 : 0 < X * Y := mul_pos hX0 hY0
  have hQsqLeX :=
    (dfiEquation30_optimized_Q_sq_le_lengths hf.one_le_P hX0 hY0 hQsq).1
  have hQXY : Q ≤ X * Y := by
    have hQQ : Q ≤ Q ^ 2 := by nlinarith
    have hXXY : X ≤ X * Y := by
      calc
        X = X * 1 := by ring
        _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
    exact hQQ.trans (hQsqLeX.trans hXXY)
  have hCA : 0 ≤ CA := by
    dsimp [CA]
    have hD : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    have hK : 0 ≤ 1 + η⁻¹ := by positivity
    have hThree : 0 ≤ (3 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hFour : 0 ≤ (4 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    positivity
  obtain ⟨C₀, hC₀, hRetained⟩ :=
    exists_sum_dfiEquation29_doubleRetained_optimized_le
      hf hfC hbox hφ hφC hscale w hwC hQ hU hf.one_le_P hQsq
        η hη hηhalf η hη
  let B : ℝ :=
    (2 ^ (3 / 4 + η / 2) * 2 ^ (3 / 4 + η / 2)) *
      2 ^ η * (8 / ε) * CA
  let Ccore : ℝ := 4 * C₀ * B
  let Cfinal : ℝ := 1 + Ccore * 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro a b h ha hb hab hh haX hbY hhX
  have hhXY : (h : ℝ) ≤ 4 * (X * Y) := by
    calc
      (h : ℝ) ≤ 2 * X := hhX
      _ ≤ 4 * (X * Y) := by
        have hXXY : X ≤ X * Y := by
          calc
            X = X * 1 := by ring
            _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
        nlinarith
  have hAverage : dfiEquation29ThreeGcdAverage h a b Q η ≤
      CA * Q ^ (1 / 2 : ℝ) * ((X * Y) ^ η) ^ 3 := by
    simpa only [dfiEquation29ThreeGcdAverage, CA] using
      dfiEquation29_threeGcdAverageLoss_le_rpow_sqrtQ
        hf.one_le_X hf.one_le_Y (by linarith) hQXY hh ha hb
          hhXY haX hbY hη
  have hLoss := dfiEquation29_doubleRetained_loss_bundle_le
    hf.one_le_X hf.one_le_Y (by linarith) hQXY ha hb haX hbY
      hε0 hε4.le hCA hAverage
  have hRaw := hRetained a b ha hb hab (h : ℤ)
    (by exact_mod_cast hh.ne')
  have hRaw' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h η q) ≤
        Ccore *
          (((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
            Q ^ (1 / 2 : ℝ)) * (X * Y) ^ ε := by
    calc
      _ ≤ ((4 * C₀) *
          ((2 ^ (3 / 4 + η / 2) * 2 ^ (3 / 4 + η / 2)) *
            X ^ (1 / 2 + η / 2) * Y ^ (1 / 2 + η / 2) *
            (a : ℝ) ^ (η / 2) * (b : ℝ) ^ (η / 2) *
            (Q ^ ((-2 + η) * (3 / 4 + η / 2)) *
              Q ^ ((-2 + η) * (3 / 4 + η / 2))) *
            (min X Y * Real.log Q))) *
          dfiEquation29ThreeGcdAverage h a b Q η := by
          simpa only [dfiEquation29ThreeGcdAverage] using hRaw
      _ = (4 * C₀) *
          (((2 ^ (3 / 4 + η / 2) * 2 ^ (3 / 4 + η / 2)) *
            X ^ (1 / 2 + η / 2) * Y ^ (1 / 2 + η / 2) *
            (a : ℝ) ^ (η / 2) * (b : ℝ) ^ (η / 2) *
            (Q ^ ((-2 + η) * (3 / 4 + η / 2)) *
              Q ^ ((-2 + η) * (3 / 4 + η / 2))) *
            (min X Y * Real.log Q)) *
            dfiEquation29ThreeGcdAverage h a b Q η) := by ring
      _ ≤ (4 * C₀) * (B *
          (((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
            Q ^ (1 / 2 : ℝ)) * (X * Y) ^ ε) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [B, η] using hLoss)
            (mul_nonneg (by norm_num) hC₀)
      _ = _ := by dsimp [Ccore]; ring
  have hCore := dfiEquation29_doubleRetained_zeroEpsilon_le_secondError
    hf.one_le_X hf.one_le_Y hQ0
  calc
    _ ≤ Ccore *
        (((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
          Q ^ (1 / 2 : ℝ)) * (X * Y) ^ ε := hRaw'
    _ ≤ Ccore * (2 *
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)))) *
        (X * Y) ^ ε := by gcongr
    _ = (Ccore * 2) * dfiTheorem1ErrorScale P X Y ε := by
      rw [← dfiEquation30_second_with_epsilon_eq_theorem1ErrorScale
        (zero_lt_one.trans_le hf.one_le_P) hX0 hY0 hQ0 hQsq]
      ring
    _ ≤ Cfinal * dfiTheorem1ErrorScale P X Y ε := by
      have hTarget : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
        unfold dfiTheorem1ErrorScale
        exact mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans hf.one_le_P) _)
            (Real.rpow_nonneg (add_nonneg hX0.le hY0.le) _))
          (Real.rpow_nonneg hXY0.le _)
      gcongr
      dsimp [Cfinal]
      linarith

end RiemannZeta.GuthMaynard
