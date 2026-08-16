import RiemannZeta.GuthMaynard.DFIErrorOptimization
import RiemannZeta.GuthMaynard.DFISourceCutoffs

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff Topology
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

/-- Uniform source-scale absorption of the logarithmic factors in DFI
equations (27) and (30).  The arithmetic variable and modulus cutoff are
bounded by their literal source ranges, and every logarithm is paid for by
one `S^δ`, where `S = X*Y`. -/
theorem dfiEquation27_sourceLogFactor_le_rpow
    {X Y Q δ : ℝ} {a K : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y) (ha : 0 < a)
    (haX : (a : ℝ) ≤ 2 * X)
    (hK : 1 ≤ K) (hKQ : (K : ℝ) ≤ 3 * Q)
    (hδ : 0 < δ) :
    1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log K ≤
      (1 + 2 * |Real.eulerMascheroniConstant| +
          4 * (3 ^ δ / δ)) * (X * Y) ^ δ := by
  let S : ℝ := X * Y
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hS0 : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith
  have hXleS : X ≤ S := by
    dsimp [S]
    calc X = X * 1 := by ring
      _ ≤ X * Y := mul_le_mul_of_nonneg_left hY hX0.le
  have hTwoX : 2 * X ≤ 3 * S := by
    have := hXleS
    nlinarith [hS0]
  have haS : (a : ℝ) ≤ 3 * S := haX.trans hTwoX
  have hKS : (K : ℝ) ≤ 3 * S := by
    exact hKQ.trans (by gcongr)
  have hThreeS0 : 0 ≤ 3 * S := by positivity
  have hlogThreeS := Real.log_le_rpow_div hThreeS0 hδ
  have hpowThreeS : (3 * S) ^ δ = 3 ^ δ * S ^ δ := by
    rw [Real.mul_rpow (by norm_num) hS0.le]
  have hA : Real.log (3 * S) ≤ (3 ^ δ / δ) * S ^ δ := by
    calc
      Real.log (3 * S) ≤ (3 * S) ^ δ / δ := hlogThreeS
      _ = (3 ^ δ / δ) * S ^ δ := by rw [hpowThreeS]; ring
  have hlogX : Real.log (2 * X) ≤ (3 ^ δ / δ) * S ^ δ := by
    exact (Real.log_le_log (by positivity) hTwoX).trans hA
  have hloga0 : 0 ≤ Real.log (a : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ha.ne'))
  have hloga : |Real.log (a : ℝ)| ≤
      (3 ^ δ / δ) * S ^ δ := by
    rw [abs_of_nonneg hloga0]
    exact (Real.log_le_log (by exact_mod_cast ha) haS).trans hA
  have hlogK0 : 0 ≤ Real.log (K : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hK)
  have hlogK : Real.log (K : ℝ) ≤
      (3 ^ δ / δ) * S ^ δ :=
    (Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK))
      hKS).trans hA
  have hSδone : 1 ≤ S ^ δ := Real.one_le_rpow hS1 hδ.le
  have hcoef0 : 0 ≤ 3 ^ δ / δ := by positivity
  have hgamma0 : 0 ≤ |Real.eulerMascheroniConstant| := abs_nonneg _
  calc
    1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log K ≤
      1 + (3 ^ δ / δ) * S ^ δ +
        (3 ^ δ / δ) * S ^ δ +
        2 * |Real.eulerMascheroniConstant| +
        2 * ((3 ^ δ / δ) * S ^ δ) := by linarith
    _ ≤ (1 + 2 * |Real.eulerMascheroniConstant|) * S ^ δ +
        4 * (3 ^ δ / δ) * S ^ δ := by
      nlinarith
    _ = (1 + 2 * |Real.eulerMascheroniConstant| +
          4 * (3 ^ δ / δ)) * S ^ δ := by ring
    _ = _ := by rfl

/-- The source restriction `H ≤ 2X` turns the divisor count appearing in
equation (27) into one `S^δ` loss, uniformly in the shift. -/
theorem dfiEquation27_sourceDivisorCount_le_rpow
    {X Y δ : ℝ} {H : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hH : 0 < H)
    (hHX : (H : ℝ) ≤ 2 * X) (hδ : 0 < δ) :
    (H.divisors.card : ℝ) ≤
      (divisorEpsilonConstant δ * 2 ^ δ) * (X * Y) ^ δ := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hS0 : 0 < X * Y := mul_pos hX0 hY0
  have hD0 : 0 ≤ divisorEpsilonConstant δ :=
    (divisorEpsilonConstant_pos δ).le
  have hXleS : X ≤ X * Y := by
    calc X = X * 1 := by ring
      _ ≤ X * Y := mul_le_mul_of_nonneg_left hY hX0.le
  have hHS : (H : ℝ) ≤ 2 * (X * Y) := hHX.trans (by gcongr)
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg H) hHS hδ.le
  calc
    (H.divisors.card : ℝ) ≤
        divisorEpsilonConstant δ * (H : ℝ) ^ δ :=
      card_divisors_le_const_mul_rpow hδ hH.ne'
    _ ≤ divisorEpsilonConstant δ * (2 * (X * Y)) ^ δ :=
      mul_le_mul_of_nonneg_left hpow hD0
    _ = (divisorEpsilonConstant δ * 2 ^ δ) *
        (X * Y) ^ δ := by
      rw [Real.mul_rpow (by norm_num) hS0.le]
      ring

/-- A harmonic number whose endpoint is at most `3Q` costs one `S^δ`
in the DFI source range `Q ≤ S = XY`. -/
theorem dfiEquation27_sourceHarmonic_le_rpow
    {X Y Q δ : ℝ} {L : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hQXY : Q ≤ X * Y) (hL : 1 ≤ L)
    (hLQ : (L : ℝ) ≤ 3 * Q) (hδ : 0 < δ) :
    (((harmonic L : ℚ) : ℝ)) ≤
      ((1 + δ⁻¹) * 3 ^ δ) * (X * Y) ^ δ := by
  have hS0 : 0 < X * Y := by positivity
  have hLS : (L : ℝ) ≤ 3 * (X * Y) := hLQ.trans (by gcongr)
  have hLpow : (L : ℝ) ^ δ ≤
      3 ^ δ * (X * Y) ^ δ := by
    calc
      (L : ℝ) ^ δ ≤ (3 * (X * Y)) ^ δ :=
        Real.rpow_le_rpow (Nat.cast_nonneg L) hLS hδ.le
      _ = 3 ^ δ * (X * Y) ^ δ := by
        rw [Real.mul_rpow (by norm_num) hS0.le]
  have hMax : max 1 ((L : ℝ) ^ δ) = (L : ℝ) ^ δ := by
    rw [max_eq_right]
    exact Real.one_le_rpow (by exact_mod_cast hL) hδ.le
  calc
    (((harmonic L : ℚ) : ℝ)) ≤
        (1 + δ⁻¹) * max 1 ((L : ℝ) ^ δ) :=
      harmonic_le_epsilon_rpow hδ L
    _ = (1 + δ⁻¹) * (L : ℝ) ^ δ := by rw [hMax]
    _ ≤ (1 + δ⁻¹) *
        (3 ^ δ * (X * Y) ^ δ) := by gcongr
    _ = ((1 + δ⁻¹) * 3 ^ δ) * (X * Y) ^ δ := by ring

/-- The exact integer cutoff used in equation (27) remains below its
source real cutoff `Q^(1-η)`. -/
theorem dfiEquation27SourceSplitCutoff_cast_le
    {Q η : ℝ} (hQ : 2 ≤ Q) (hη0 : 0 < η) (hη1 : η < 1) :
    (dfiEquation27SourceSplitCutoff Q η : ℝ) ≤ Q ^ (1 - η) := by
  have hspec := dfiEquation27SourceSplitCutoff_spec hQ hη0 hη1
  have hlt : dfiEquation27SourceSplitCutoff Q η < ⌈Q ^ (1 - η)⌉₊ := by
    rw [← hspec.2.2]
    omega
  exact (Nat.lt_ceil.mp hlt).le

/-- The logarithm of the delta-modulus scale costs one source epsilon
power. -/
theorem dfiEquation27_sourceLogQ_le_rpow
    {X Y Q δ : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hQ : 1 ≤ Q) (hQXY : Q ≤ X * Y) (hδ : 0 < δ) :
    Real.log Q ≤ δ⁻¹ * (X * Y) ^ δ := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hS0 : 0 ≤ X * Y := mul_nonneg
    (zero_le_one.trans hX) (zero_le_one.trans hY)
  calc
    Real.log Q ≤ Q ^ δ / δ := Real.log_le_rpow_div hQ0 hδ
    _ ≤ (X * Y) ^ δ / δ := by
      gcongr
    _ = δ⁻¹ * (X * Y) ^ δ := by field_simp

/-- The logarithmic factor in the infinite central tail of equation (27)
also costs one source epsilon power. -/
theorem dfiEquation27_sourceCentralLogFactor_le_rpow
    {X Y Q δ β : ℝ} {a : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y) (ha : 0 < a)
    (haX : (a : ℝ) ≤ 2 * X) (hδ : 0 < δ) (hβ : 0 < β) :
    1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 4 * β⁻¹ ≤
      (1 + 2 * |Real.eulerMascheroniConstant| +
          4 * (3 ^ δ / δ) + 4 * β⁻¹) * (X * Y) ^ δ := by
  have hbase := dfiEquation27_sourceLogFactor_le_rpow
    hX hY hQ hQXY ha haX (K := 1) (by norm_num) (by
      have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
      norm_num
      linarith) hδ
  have hbase' :
      1 + Real.log (2 * X) + |Real.log a| +
          2 * |Real.eulerMascheroniConstant| + 2 * Real.log (1 : ℝ) ≤
        (1 + 2 * |Real.eulerMascheroniConstant| +
          4 * (3 ^ δ / δ)) * (X * Y) ^ δ := by
    simpa using hbase
  have hS1 : 1 ≤ (X * Y) ^ δ := by
    apply Real.one_le_rpow
    · nlinarith [mul_nonneg (zero_le_one.trans hX) (zero_le_one.trans hY)]
    · exact hδ.le
  have hβ0 : 0 ≤ 4 * β⁻¹ := by positivity
  calc
    1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 4 * β⁻¹ =
      (1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (1 : ℝ)) +
          4 * β⁻¹ := by norm_num
    _ ≤ (1 + 2 * |Real.eulerMascheroniConstant| +
          4 * (3 ^ δ / δ)) * (X * Y) ^ δ +
        (4 * β⁻¹) * (X * Y) ^ δ := by
      exact add_le_add hbase' (le_mul_of_one_le_right hβ0 hS1)
    _ = (1 + 2 * |Real.eulerMascheroniConstant| +
          4 * (3 ^ δ / δ) + 4 * β⁻¹) * (X * Y) ^ δ := by ring

/-- The physical logarithmic factor in equation (30), whose last term is
`log(2Q)`, is controlled by the same source logarithmic majorant. -/
theorem dfiEquation27_sourcePhysicalLogFactor_le_rpow
    {X Y Q δ : ℝ} {a : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y) (ha : 0 < a)
    (haX : (a : ℝ) ≤ 2 * X) (hδ : 0 < δ) :
    Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q) ≤
      (1 + 2 * |Real.eulerMascheroniConstant| +
          4 * (3 ^ δ / δ)) * (X * Y) ^ δ := by
  have hCeil1 : 1 ≤ ⌈2 * Q⌉₊ := by
    have htwo : (1 : ℝ) ≤ 2 * Q := by linarith
    exact_mod_cast htwo.trans (Nat.le_ceil (2 * Q))
  have hCeilQ := natCeil_two_mul_le_three_mul hQ
  have hbase := dfiEquation27_sourceLogFactor_le_rpow
    hX hY hQ hQXY ha haX hCeil1 hCeilQ hδ
  have hlog : Real.log (2 * Q) ≤ Real.log (⌈2 * Q⌉₊ : ℝ) :=
    Real.log_le_log (by positivity) (Nat.le_ceil (2 * Q))
  linarith

/-- The first integrated delta-kernel factor acquires the required
`Q⁻¹` saving once the source cutoff and derivative order are coupled. -/
theorem dfiEquation27_sourceCutoff_first_power_le
    {Q η : ℝ} {K j : ℕ} (hQ : 1 ≤ Q)
    (hK : (K : ℝ) ≤ Q ^ (1 - η))
    (hj : 2 ≤ η * (j : ℝ)) :
    (K : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * Q ^ 2 ≤
      Q ^ (-(1 : ℝ)) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hK0 : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hpowK : (K : ℝ) ^ j ≤ (Q ^ (1 - η)) ^ j :=
    pow_le_pow_left₀ hK0 hK j
  have hCut : (Q ^ (1 - η)) ^ j =
      Q ^ ((1 - η) * (j : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
  have hInv : (Q ^ (j + 1))⁻¹ = Q ^ (-(j + 1 : ℕ) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hQ0.le]
  have hTwo : Q ^ (2 : ℕ) = Q ^ (2 : ℝ) :=
    (Real.rpow_natCast Q 2).symm
  have hCombine :
      (Q ^ (1 - η)) ^ j * (Q ^ (j + 1))⁻¹ * Q ^ (2 : ℕ) =
        Q ^ (1 - η * (j : ℝ)) := by
    rw [hCut, hInv, hTwo, ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    congr 1
    push_cast
    ring
  have hexp : 1 - η * (j : ℝ) ≤ -(1 : ℝ) := by linarith
  calc
    (K : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * Q ^ 2 ≤
        (Q ^ (1 - η)) ^ j * (Q ^ (j + 1))⁻¹ * Q ^ 2 := by
      gcongr
    _ = Q ^ (1 - η * (j : ℝ)) := hCombine
    _ ≤ Q ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hQ hexp

/-- The second integrated delta-kernel factor has the same `Q⁻¹` saving.
Here the factor `U⁻ʲ` is evaluated after the source choice `U=Q²`. -/
theorem dfiEquation27_sourceCutoff_second_power_le
    {Q η : ℝ} {K j : ℕ} (hQ : 1 ≤ Q) (hjNat : 2 ≤ j)
    (hK : (K : ℝ) ≤ Q ^ (1 - η))
    (hj : 2 ≤ η * (j : ℝ)) :
    (K : ℝ) ^ j * Q ^ (j - 1) *
        (Q ^ 2 * ((Q ^ 2)⁻¹ ^ j)) ≤ Q ^ (-(1 : ℝ)) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hK0 : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hpowK : (K : ℝ) ^ j ≤ (Q ^ (1 - η)) ^ j :=
    pow_le_pow_left₀ hK0 hK j
  have hCut : (Q ^ (1 - η)) ^ j =
      Q ^ ((1 - η) * (j : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
  have hSub : Q ^ (j - 1) = Q ^ ((j : ℝ) - 1) := by
    rw [← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ j)]
    norm_num
  have hTwo : Q ^ (2 : ℕ) = Q ^ (2 : ℝ) :=
    (Real.rpow_natCast Q 2).symm
  have hInvPow : ((Q ^ (2 : ℕ))⁻¹) ^ j =
      Q ^ (-(2 : ℝ) * (j : ℝ)) := by
    rw [hTwo, ← Real.rpow_neg hQ0.le, ← Real.rpow_natCast]
    exact (Real.rpow_mul hQ0.le (-(2 : ℝ)) (j : ℝ)).symm
  have hCombine :
      (Q ^ (1 - η)) ^ j * Q ^ (j - 1) *
          (Q ^ (2 : ℕ) * ((Q ^ (2 : ℕ))⁻¹ ^ j)) =
        Q ^ (1 - η * (j : ℝ)) := by
    rw [hCut, hSub, hInvPow, hTwo,
      ← Real.rpow_add hQ0, ← Real.rpow_add hQ0,
      ← Real.rpow_add hQ0]
    congr 1
    ring
  have hexp : 1 - η * (j : ℝ) ≤ -(1 : ℝ) := by linarith
  calc
    (K : ℝ) ^ j * Q ^ (j - 1) *
        (Q ^ 2 * ((Q ^ 2)⁻¹ ^ j)) ≤
      (Q ^ (1 - η)) ^ j * Q ^ (j - 1) *
        (Q ^ 2 * ((Q ^ 2)⁻¹ ^ j)) := by
        gcongr
    _ = Q ^ (1 - η * (j : ℝ)) := hCombine
    _ ≤ Q ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hQ hexp

/-- After the source choice `U=Q²`, both integrated delta-kernel errors
are bounded by the same `Q⁻¹` term, with exactly two logarithmic epsilon
losses. -/
theorem dfiEquation27IntegratedErrorEnvelope_source_le
    {X Y Q η : ℝ} {a b K j : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y) (hη : 0 < η)
    (ha : 0 < a) (hb : 0 < b)
    (haX : (a : ℝ) ≤ 2 * X) (hbY : (b : ℝ) ≤ 2 * Y)
    (hK1 : 1 ≤ K) (hKQ : (K : ℝ) ≤ 3 * Q)
    (hKcut : (K : ℝ) ≤ Q ^ (1 - η))
    (hjNat : 2 ≤ j) (hj : 2 ≤ η * (j : ℝ)) :
    dfiEquation27IntegratedErrorEnvelope Q X Y (Q ^ 2) a b K j ≤
      12 * (1 + 2 * |Real.eulerMascheroniConstant| +
          4 * (3 ^ η / η)) ^ 2 * min X Y * Q ^ (-(1 : ℝ)) *
        (X * Y) ^ (2 * η) := by
  let B : ℝ := 1 + 2 * |Real.eulerMascheroniConstant| +
    4 * (3 ^ η / η)
  let LX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log K
  let LY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log K
  have hLX := dfiEquation27_sourceLogFactor_le_rpow
    hX hY hQ hQXY ha haX hK1 hKQ hη
  have hLY := dfiEquation27_sourceLogFactor_le_rpow
    hY hX hQ (by simpa [mul_comm] using hQXY) hb hbY hK1 hKQ hη
  have hlogK : 0 ≤ Real.log (K : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hK1)
  have hLX0 : 0 ≤ LX := by
    dsimp [LX]
    have : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by nlinarith)
    positivity
  have hLY0 : 0 ≤ LY := by
    dsimp [LY]
    have : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by nlinarith)
    positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hS0 : 0 < X * Y := by positivity
  have hSη0 : 0 ≤ (X * Y) ^ η := Real.rpow_nonneg hS0.le η
  have hLogs : LX * LY ≤ B ^ 2 * (X * Y) ^ (2 * η) := by
    calc
      LX * LY ≤ (B * (X * Y) ^ η) * (B * (X * Y) ^ η) := by
        exact mul_le_mul (by simpa [LX, B] using hLX)
          (by simpa [LY, B, mul_comm] using hLY) hLY0
          (mul_nonneg hB0 hSη0)
      _ = B ^ 2 * (X * Y) ^ (2 * η) := by
        rw [show (2 * η : ℝ) = η + η by ring, Real.rpow_add hS0]
        ring
  have hA₁ := dfiEquation27_sourceCutoff_first_power_le hQ hKcut hj
  have hA₂ := dfiEquation27_sourceCutoff_second_power_le hQ hjNat hKcut hj
  have hA₁0 : 0 ≤
      (K : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * Q ^ 2 := by positivity
  have hA₂0 : 0 ≤
      (K : ℝ) ^ j * Q ^ (j - 1) *
        (Q ^ 2 * ((Q ^ 2)⁻¹ ^ j)) := by positivity
  have hQinv0 : 0 ≤ Q ^ (-(1 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hC0 : 0 ≤ 6 * min X Y := by
    exact mul_nonneg (by norm_num)
      (le_min (zero_le_one.trans hX) (zero_le_one.trans hY))
  unfold dfiEquation27IntegratedErrorEnvelope
  change
    ((K : ℝ) ^ j * (Q ^ (j + 1))⁻¹) *
          (6 * min X Y * Q ^ 2 * (LX * LY)) +
        ((K : ℝ) ^ j * Q ^ (j - 1)) *
          (6 * min X Y * Q ^ 2 *
            (LX * LY * (Q ^ 2)⁻¹ ^ j)) ≤ _
  calc
    _ = (6 * min X Y) *
          (((K : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * Q ^ 2) * (LX * LY)) +
        (6 * min X Y) *
          (((K : ℝ) ^ j * Q ^ (j - 1) *
            (Q ^ 2 * ((Q ^ 2)⁻¹ ^ j))) * (LX * LY)) := by ring
    _ ≤ (6 * min X Y) *
          (Q ^ (-(1 : ℝ)) * (B ^ 2 * (X * Y) ^ (2 * η))) +
        (6 * min X Y) *
          (Q ^ (-(1 : ℝ)) * (B ^ 2 * (X * Y) ^ (2 * η))) := by
      gcongr
    _ = 12 * B ^ 2 * min X Y * Q ^ (-(1 : ℝ)) *
          (X * Y) ^ (2 * η) := by ring
    _ = _ := by rfl

/-- The small-modulus term in the source-uniform equation-(27) split has
the published first-error shape, with four explicitly accounted epsilon
losses. -/
theorem dfiEquation27InterpolatedSmallError_source_le
    {X Y Q η Cs : ℝ} {a b h K j : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y) (hη : 0 < η) (hCs : 0 ≤ Cs)
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (haX : (a : ℝ) ≤ 2 * X) (hbY : (b : ℝ) ≤ 2 * Y)
    (hhX : (h : ℝ) ≤ 2 * X)
    (hK1 : 1 ≤ K) (hKlt : K < ⌈2 * Q⌉₊)
    (hKcut : (K : ℝ) ≤ Q ^ (1 - η))
    (hjNat : 2 ≤ j) (hj : 2 ≤ η * (j : ℝ)) :
    dfiEquation27InterpolatedSmallError
        Cs Q X Y (Q ^ 2) 1 a b h K j ≤
      (Cs * (divisorEpsilonConstant η * 2 ^ η) *
          ((1 + η⁻¹) * 3 ^ η) *
          (12 * (1 + 2 * |Real.eulerMascheroniConstant| +
            4 * (3 ^ η / η)) ^ 2)) *
        min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (4 * η) := by
  have hKQ : (K : ℝ) ≤ 3 * Q := by
    have hceil := natCeil_two_mul_le_three_mul hQ
    have hcast : (K : ℝ) ≤ (⌈2 * Q⌉₊ : ℝ) := by
      exact_mod_cast hKlt.le
    exact hcast.trans hceil
  have hKsuccQ : ((K + 1 : ℕ) : ℝ) ≤ 3 * Q := by
    have hsucc : K + 1 ≤ ⌈2 * Q⌉₊ := by omega
    have hcast : ((K + 1 : ℕ) : ℝ) ≤ (⌈2 * Q⌉₊ : ℝ) := by
      exact_mod_cast hsucc
    exact hcast.trans (natCeil_two_mul_le_three_mul hQ)
  have hD := dfiEquation27_sourceDivisorCount_le_rpow
    hX hY hh hhX hη
  have hH := dfiEquation27_sourceHarmonic_le_rpow
    hX hY hQXY (L := K + 1) (by omega) hKsuccQ hη
  have hE := dfiEquation27IntegratedErrorEnvelope_source_le
    hX hY hQ hQXY hη ha hb haX hbY hK1 hKQ hKcut hjNat hj
  have hD0 : 0 ≤ (h.divisors.card : ℝ) := Nat.cast_nonneg _
  have hH0 : 0 ≤ (((harmonic (K + 1) : ℚ) : ℝ)) := by
    exact_mod_cast (harmonic_pos (by omega : K + 1 ≠ 0)).le
  have hE0 : 0 ≤ dfiEquation27IntegratedErrorEnvelope
      Q X Y (Q ^ 2) a b K j :=
    dfiEquation27IntegratedErrorEnvelope_nonneg
      (zero_lt_one.trans_le hQ) hX hY (by positivity) a b K j hK1
  have hS0 : 0 < X * Y := by positivity
  have hDBound0 : 0 ≤
      (divisorEpsilonConstant η * 2 ^ η) * (X * Y) ^ η := by
    have : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    positivity
  have hHBound0 : 0 ≤
      ((1 + η⁻¹) * 3 ^ η) * (X * Y) ^ η := by positivity
  unfold dfiEquation27InterpolatedSmallError
  rw [show (-1 + (1 : ℝ)) = 0 by norm_num, Real.rpow_zero]
  simp only [one_mul]
  calc
    Cs * ((h.divisors.card : ℝ) *
          (((harmonic (K + 1) : ℚ) : ℝ))) *
        dfiEquation27IntegratedErrorEnvelope Q X Y (Q ^ 2) a b K j ≤
      Cs * (((divisorEpsilonConstant η * 2 ^ η) * (X * Y) ^ η) *
          (((1 + η⁻¹) * 3 ^ η) * (X * Y) ^ η)) *
        ((12 * (1 + 2 * |Real.eulerMascheroniConstant| +
            4 * (3 ^ η / η)) ^ 2) * min X Y *
          Q ^ (-(1 : ℝ)) * (X * Y) ^ (2 * η)) := by
      have hDH := mul_le_mul hD hH hH0 hDBound0
      have hCDH := mul_le_mul_of_nonneg_left hDH hCs
      exact mul_le_mul hCDH hE hE0
        (mul_nonneg hCs (mul_nonneg hDBound0 hHBound0))
    _ = (Cs * (divisorEpsilonConstant η * 2 ^ η) *
          ((1 + η⁻¹) * 3 ^ η) *
          (12 * (1 + 2 * |Real.eulerMascheroniConstant| +
            4 * (3 ^ η / η)) ^ 2)) *
        min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (4 * η) := by
      rw [show (4 * η : ℝ) = η + η + 2 * η by ring,
        Real.rpow_add hS0, Real.rpow_add hS0]
      ring

/-- The large-modulus physical part of equation (27) has the same
`Q⁻¹` source shape.  Its six epsilon losses are respectively the shift
divisor count, harmonic sum, two logarithmic factors, `log Q`, and the
integer-cutoff displacement `Q^η`. -/
theorem dfiEquation27InterpolatedPhysicalError_source_le
    {X Y Q η Cp : ℝ} {a b h : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 2 ≤ Q)
    (hQXY : Q ≤ X * Y) (hη : 0 < η) (hη1 : η < 1)
    (hCp : 0 ≤ Cp) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (haX : (a : ℝ) ≤ 2 * X) (hbY : (b : ℝ) ≤ 2 * Y)
    (hhX : (h : ℝ) ≤ 2 * X) :
    dfiEquation27InterpolatedPhysicalError Cp Q X Y 1 a b h
        (dfiEquation27SourceSplitCutoff Q η) ≤
      ((divisorEpsilonConstant η * 2 ^ η) *
          ((1 + η⁻¹) * 3 ^ η) * Cp *
          (1 + 2 * |Real.eulerMascheroniConstant| +
            4 * (3 ^ η / η)) ^ 2 * η⁻¹) *
        min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) := by
  let K : ℕ := dfiEquation27SourceSplitCutoff Q η
  let D : ℝ := divisorEpsilonConstant η * 2 ^ η
  let H : ℝ := (1 + η⁻¹) * 3 ^ η
  let B : ℝ := 1 + 2 * |Real.eulerMascheroniConstant| +
    4 * (3 ^ η / η)
  let LX : ℝ := Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)
  let LY : ℝ := Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)
  have hQ1 : 1 ≤ Q := hQ.trans' (by norm_num)
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  have hS0 : 0 < X * Y := by positivity
  have hD := dfiEquation27_sourceDivisorCount_le_rpow
    hX hY hh hhX hη
  have hH := dfiEquation27_sourceHarmonic_le_rpow
    hX hY hQXY (L := ⌈2 * Q⌉₊) (by
      have : (1 : ℝ) ≤ 2 * Q := by linarith
      exact_mod_cast this.trans (Nat.le_ceil (2 * Q)))
      (natCeil_two_mul_le_three_mul hQ1) hη
  have hLX := dfiEquation27_sourcePhysicalLogFactor_le_rpow
    hX hY hQ1 hQXY ha haX hη
  have hLY := dfiEquation27_sourcePhysicalLogFactor_le_rpow
    hY hX hQ1 (by simpa [mul_comm] using hQXY) hb hbY hη
  have hLogQ := dfiEquation27_sourceLogQ_le_rpow
    hX hY hQ1 hQXY hη
  have hInv0 := dfiEquation27SourceSplitCutoff_inv_le hQ hη hη1
  have hInv : (((K + 1 : ℕ) : ℝ) ^ (-(1 : ℝ))) ≤
      Q ^ (-(1 : ℝ)) * (X * Y) ^ η := by
    calc
      (((K + 1 : ℕ) : ℝ) ^ (-(1 : ℝ))) =
          1 / (((K + 1 : ℕ) : ℝ)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_one, one_div]
      _ ≤ Q ^ (-(1 - η)) := by simpa [K] using hInv0
      _ = Q ^ (-(1 : ℝ)) * Q ^ η := by
        rw [show (-(1 - η) : ℝ) = -(1 : ℝ) + η by ring,
          Real.rpow_add hQ0]
      _ ≤ Q ^ (-(1 : ℝ)) * (X * Y) ^ η := by
        gcongr
  have hDiv0 : 0 ≤ (h.divisors.card : ℝ) := Nat.cast_nonneg _
  have hHarm0 : 0 ≤ (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ)) := by
    have hceil : ⌈2 * Q⌉₊ ≠ 0 := by
      have : 0 < ⌈2 * Q⌉₊ := by
        have : (0 : ℝ) < 2 * Q := by positivity
        exact_mod_cast this.trans_le (Nat.le_ceil (2 * Q))
      omega
    exact_mod_cast (harmonic_pos hceil).le
  have hLX0 : 0 ≤ LX := by
    dsimp [LX]
    have hx : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by nlinarith)
    have hq : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by nlinarith)
    positivity
  have hLY0 : 0 ≤ LY := by
    dsimp [LY]
    have hy : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by nlinarith)
    have hq : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by nlinarith)
    positivity
  have hLY' : LY ≤ B * (X * Y) ^ η := by
    simpa [LY, B, mul_comm] using hLY
  have hLogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hInvTerm0 : 0 ≤ (((K + 1 : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
    Real.rpow_nonneg (by positivity) _
  have hD0 : 0 ≤ D := by
    dsimp [D]
    have : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    positivity
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  unfold dfiEquation27InterpolatedPhysicalError
  change
    ((((a * b : ℕ) : ℝ) ^ (-1 + (1 : ℝ))) *
      (h.divisors.card : ℝ) *
      ((((K + 1 : ℕ) : ℝ) ^ (-(1 : ℝ))) *
        (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
      (Cp * LX * LY * min X Y * Real.log Q)) ≤ _
  rw [show (-1 + (1 : ℝ)) = 0 by norm_num, Real.rpow_zero, one_mul]
  calc
    (h.divisors.card : ℝ) *
        ((((K + 1 : ℕ) : ℝ) ^ (-(1 : ℝ))) *
          (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
        (Cp * LX * LY * min X Y * Real.log Q) ≤
      (D * (X * Y) ^ η) *
        ((Q ^ (-(1 : ℝ)) * (X * Y) ^ η) *
          (H * (X * Y) ^ η)) *
        (Cp * (B * (X * Y) ^ η) * (B * (X * Y) ^ η) *
          min X Y * (η⁻¹ * (X * Y) ^ η)) := by
      gcongr
    _ = (D * H * Cp * B ^ 2 * η⁻¹) * min X Y *
          Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) := by
      rw [show (6 * η : ℝ) = η + η + η + η + η + η by ring,
        Real.rpow_add hS0, Real.rpow_add hS0, Real.rpow_add hS0,
        Real.rpow_add hS0, Real.rpow_add hS0]
      ring
    _ = _ := by rfl

/-- The infinite central tail in equation (27) has the same source shape.
The exponent identity
`-(1-η)(1-2η) ≤ -1+3η` supplies the cutoff saving, and the other three
epsilon powers come from the shift divisor count and two central logarithms. -/
theorem dfiEquation27InterpolatedCentralTail_source_le
    {X Y Q η Ct : ℝ} {a b h : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 2 ≤ Q)
    (hQXY : Q ≤ X * Y) (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hCt : 0 ≤ Ct) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (haX : (a : ℝ) ≤ 2 * X) (hbY : (b : ℝ) ≤ 2 * Y)
    (hhX : (h : ℝ) ≤ 2 * X) :
    dfiEquation27InterpolatedCentralTail Ct X Y 1
        (1 - 2 * η) η η a b h
        (dfiEquation27SourceSplitCutoff Q η) ≤
      (Ct * (divisorEpsilonConstant η * 2 ^ η) *
          (1 + 2 * |Real.eulerMascheroniConstant| +
            4 * (3 ^ η / η) + 4 * η⁻¹) ^ 2 * (1 + η⁻¹)) *
        min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) := by
  let K : ℕ := dfiEquation27SourceSplitCutoff Q η
  let D : ℝ := divisorEpsilonConstant η * 2 ^ η
  let B : ℝ := 1 + 2 * |Real.eulerMascheroniConstant| +
    4 * (3 ^ η / η) + 4 * η⁻¹
  let LX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant| + 4 * η⁻¹
  let LY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant| + 4 * η⁻¹
  have hQ1 : 1 ≤ Q := hQ.trans' (by norm_num)
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  have hη1 : η < 1 := hηhalf.trans (by norm_num)
  have hAlpha : 0 < 1 - 2 * η := by linarith
  have hS0 : 0 < X * Y := by positivity
  have hSpec := dfiEquation27SourceSplitCutoff_spec hQ hη hη1
  have hScale := dfiEquation27SourceSplitCutoff_scale hQ hη hη1
  have hD := dfiEquation27_sourceDivisorCount_le_rpow
    hX hY hh hhX hη
  have hLX := dfiEquation27_sourceCentralLogFactor_le_rpow
    hX hY hQ1 hQXY ha haX hη hη
  have hLY := dfiEquation27_sourceCentralLogFactor_le_rpow
    hY hX hQ1 (by simpa [mul_comm] using hQXY) hb hbY hη hη
  have hCutRaw : (((K + 1 : ℕ) : ℝ) ^ (-(1 - 2 * η))) ≤
      (Q ^ (1 - η)) ^ (-(1 - 2 * η)) := by
    exact Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hQ0 (1 - η))
      (by simpa [K] using hScale.1) (by linarith)
  have hCut : (((K + 1 : ℕ) : ℝ) ^ (-(1 - 2 * η))) ≤
      Q ^ (-(1 : ℝ)) * (X * Y) ^ (3 * η) := by
    calc
      (((K + 1 : ℕ) : ℝ) ^ (-(1 - 2 * η))) ≤
          (Q ^ (1 - η)) ^ (-(1 - 2 * η)) := hCutRaw
      _ = Q ^ ((1 - η) * (-(1 - 2 * η))) := by
        rw [← Real.rpow_mul hQ0.le]
      _ ≤ Q ^ (-(1 : ℝ) + 3 * η) := by
        apply Real.rpow_le_rpow_of_exponent_le hQ1
        nlinarith [sq_nonneg η]
      _ = Q ^ (-(1 : ℝ)) * Q ^ (3 * η) := by
        rw [Real.rpow_add hQ0]
      _ ≤ Q ^ (-(1 : ℝ)) * (X * Y) ^ (3 * η) := by
        gcongr
  have hDiv0 : 0 ≤ (h.divisors.card : ℝ) := Nat.cast_nonneg _
  have hLX0 : 0 ≤ LX := by
    dsimp [LX]
    have hx : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by nlinarith)
    positivity
  have hLY0 : 0 ≤ LY := by
    dsimp [LY]
    have hy : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by nlinarith)
    positivity
  have hCut0 : 0 ≤ (((K + 1 : ℕ) : ℝ) ^ (-(1 - 2 * η))) :=
    Real.rpow_nonneg (by positivity) _
  have hD0 : 0 ≤ D := by
    dsimp [D]
    have : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hLY' : LY ≤ B * (X * Y) ^ η := by
    simpa [LY, B, mul_comm] using hLY
  unfold dfiEquation27InterpolatedCentralTail
  change
    Ct * (((a * b : ℕ) : ℝ) ^ (-1 + (1 : ℝ))) *
      (h.divisors.card : ℝ) * LX * LY * min X Y *
      (((K : ℝ) + 1) ^ (-(1 - 2 * η))) * (1 + η⁻¹) ≤ _
  rw [show (-1 + (1 : ℝ)) = 0 by norm_num, Real.rpow_zero]
  have hKcast : (K : ℝ) + 1 = ((K + 1 : ℕ) : ℝ) := by norm_num
  rw [mul_one, hKcast]
  calc
    Ct * (h.divisors.card : ℝ) * LX * LY * min X Y *
        (((K + 1 : ℕ) : ℝ) ^ (-(1 - 2 * η))) * (1 + η⁻¹) ≤
      Ct * (D * (X * Y) ^ η) * (B * (X * Y) ^ η) *
        (B * (X * Y) ^ η) * min X Y *
        (Q ^ (-(1 : ℝ)) * (X * Y) ^ (3 * η)) * (1 + η⁻¹) := by
      gcongr
    _ = (Ct * D * B ^ 2 * (1 + η⁻¹)) * min X Y *
          Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) := by
      rw [show (6 * η : ℝ) = η + η + η + 3 * η by ring,
        Real.rpow_add hS0, Real.rpow_add hS0,
        Real.rpow_add hS0]
      ring
    _ = _ := by rfl

/-- The symmetric physical mass in equation (27), after the optimized
choice of `Q`, is already at the first DFI error scale.  This is the
source-facing version needed below: the support contributes `min X Y`,
not an asymmetric factor `X`. -/
theorem dfiEquation27_min_mul_Q_inv_mul_rpow_le_theorem1ErrorScale
    {P X Y Q ε : ℝ}
    (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε ≤
      2 * dfiTheorem1ErrorScale P X Y ε := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hXY0 : 0 < X * Y := mul_pos hX0 hY0
  have hMin : min X Y ≤ 2 * (X * Y) / (X + Y) := by
    rcases le_total X Y with hXY | hYX
    · rw [min_eq_left hXY]
      apply (le_div_iff₀ (add_pos hX0 hY0)).2
      nlinarith [mul_nonneg hX0.le hY0.le]
    · rw [min_eq_right hYX]
      apply (le_div_iff₀ (add_pos hX0 hY0)).2
      nlinarith [mul_nonneg hX0.le hY0.le]
  have hFirst := dfiEquation30_first_optimized_le
    (a := 1) (b := 1) (by norm_num) (by norm_num) hP hX hY hQ hQsq
  have hFirst' :
      (X * Y) / (X + Y) * Q ^ (-(1 : ℝ)) ≤
        P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ) := by
    simpa using hFirst
  have hTargetFactor :
      (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ ε =
        dfiTheorem1ErrorScale P X Y ε := by
    unfold dfiTheorem1ErrorScale
    rw [show
        P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
            (X * Y) ^ (1 / 4 : ℝ) * (X * Y) ^ ε =
          P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
            ((X * Y) ^ (1 / 4 : ℝ) * (X * Y) ^ ε) by ring,
      ← Real.rpow_add hXY0]
  calc
    min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε ≤
        (2 * (X * Y) / (X + Y)) * Q ^ (-(1 : ℝ)) *
          (X * Y) ^ ε := by gcongr
    _ = 2 * (((X * Y) / (X + Y) * Q ^ (-(1 : ℝ))) *
          (X * Y) ^ ε) := by ring
    _ ≤ 2 * ((P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ ε) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hFirst'
          (Real.rpow_nonneg hXY0.le ε)) (by norm_num)
    _ = 2 * dfiTheorem1ErrorScale P X Y ε := by rw [hTargetFactor]

set_option maxHeartbeats 2000000 in
/-- DFI equations (27) and (30), at the paper's optimized cutoff: the
complete main-branch discrepancy is bounded by the published Theorem 1
scale.  The constant is chosen before the coprime coefficients and shift. -/
theorem exists_norm_sum_dfiEquation24Main_sub_centralSeries_le_theorem1ErrorScale
    {P X Y U Q ε : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b h : ℕ), 0 < a → 0 < b → 0 < h → a.Coprime b →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  subst U
  let η : ℝ := ε / 16
  have hη : 0 < η := by dsimp [η]; positivity
  have hηhalf : η < 1 / 2 := by dsimp [η]; linarith
  have hη1 : η < 1 := hηhalf.trans (by norm_num)
  have hAlpha : 0 < 1 - 2 * η := by linarith
  obtain ⟨j, hjLarge⟩ := exists_nat_gt (2 / η)
  have hTwoDiv : (2 : ℝ) < 2 / η := by
    apply (lt_div_iff₀ hη).2
    nlinarith
  have hjNat : 2 ≤ j := by
    have : (2 : ℝ) < (j : ℝ) := hTwoDiv.trans hjLarge
    exact_mod_cast this.le
  have hj : 2 ≤ η * (j : ℝ) := by
    have hmul : 2 < (j : ℝ) * η := (div_lt_iff₀ hη).1 hjLarge
    nlinarith
  obtain ⟨Cs, Cp, Ct, hCs, hCp, hCt, hMain⟩ :=
    exists_norm_sum_dfiEquation24Main_sub_centralSeries_le_source_split_interpolated
      w hf hfC hbox hφ hφC hscale hwC hQ rfl j hjNat
        1 (1 - 2 * η) η η (by norm_num) (by norm_num)
        hAlpha hη hη (by ring)
  let K : ℕ := dfiEquation27SourceSplitCutoff Q η
  have hSpec := dfiEquation27SourceSplitCutoff_spec hQ hη hη1
  have hKcut : (K : ℝ) ≤ Q ^ (1 - η) := by
    simpa [K] using dfiEquation27SourceSplitCutoff_cast_le hQ hη hη1
  have hQ0 : 0 < Q := by linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hS0 : 0 < X * Y := mul_pos hX0 hY0
  have hS1 : 1 ≤ X * Y := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ X * Y := mul_le_mul hf.one_le_X hf.one_le_Y
        zero_le_one (zero_le_one.trans hf.one_le_X)
  have hQsqLeX :=
    (dfiEquation30_optimized_Q_sq_le_lengths hf.one_le_P hX0 hY0 hQsq).1
  have hQXY : Q ≤ X * Y := by
    have hQQ : Q ≤ Q ^ 2 := by nlinarith
    have hXXY : X ≤ X * Y := by
      calc X = X * 1 := by ring
        _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
    exact hQQ.trans (hQsqLeX.trans hXXY)
  let As : ℝ := Cs * (divisorEpsilonConstant η * 2 ^ η) *
      ((1 + η⁻¹) * 3 ^ η) *
      (12 * (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η)) ^ 2)
  let Ap : ℝ := (divisorEpsilonConstant η * 2 ^ η) *
      ((1 + η⁻¹) * 3 ^ η) * Cp *
      (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η)) ^ 2 * η⁻¹
  let At : ℝ := Ct * (divisorEpsilonConstant η * 2 ^ η) *
      (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η) + 4 * η⁻¹) ^ 2 * (1 + η⁻¹)
  let C : ℝ := 1 + 2 * (As + Ap + At)
  have hDiv0 : 0 ≤ divisorEpsilonConstant η :=
    (divisorEpsilonConstant_pos η).le
  have hAs : 0 ≤ As := by
    change 0 ≤ Cs * (divisorEpsilonConstant η * 2 ^ η) *
      ((1 + η⁻¹) * 3 ^ η) *
      (12 * (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η)) ^ 2)
    positivity
  have hAp : 0 ≤ Ap := by
    change 0 ≤ (divisorEpsilonConstant η * 2 ^ η) *
      ((1 + η⁻¹) * 3 ^ η) * Cp *
      (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η)) ^ 2 * η⁻¹
    positivity
  have hAt : 0 ≤ At := by
    change 0 ≤ Ct * (divisorEpsilonConstant η * 2 ^ η) *
      (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η) + 4 * η⁻¹) ^ 2 * (1 + η⁻¹)
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a b h ha hb hh hab haX hbY hhX
  have hRaw := hMain a b h K ha hb hh hab hSpec.1 hSpec.2.1
  have hSmall := dfiEquation27InterpolatedSmallError_source_le
    hf.one_le_X hf.one_le_Y (by linarith : 1 ≤ Q) hQXY hη hCs.le
      ha hb hh haX hbY hhX hSpec.1 hSpec.2.1 hKcut hjNat hj
  have hPhysical := dfiEquation27InterpolatedPhysicalError_source_le
    hf.one_le_X hf.one_le_Y hQ hQXY hη hη1 hCp.le
      ha hb hh haX hbY hhX
  have hCentral := dfiEquation27InterpolatedCentralTail_source_le
    hf.one_le_X hf.one_le_Y hQ hQXY hη hηhalf hCt.le
      ha hb hh haX hbY hhX
  have hPow4 : (X * Y) ^ (4 * η) ≤ (X * Y) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hS1 (by dsimp [η]; linarith)
  have hPow6 : (X * Y) ^ (6 * η) ≤ (X * Y) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hS1 (by dsimp [η]; linarith)
  have hBase := dfiEquation27_min_mul_Q_inv_mul_rpow_le_theorem1ErrorScale
    (ε := ε) hf.one_le_P hf.one_le_X hf.one_le_Y hQ0 hQsq
  have hSmall' :
      dfiEquation27InterpolatedSmallError Cs Q X Y (Q ^ 2) 1
          a b h K j ≤ 2 * As * dfiTheorem1ErrorScale P X Y ε := by
    calc
      _ ≤ As * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (4 * η) := by
        simpa only [As] using hSmall
      _ ≤ As * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) := by
        rw [show As * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (4 * η) =
            (As * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ (4 * η) by ring,
          show As * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) =
            (As * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ ε by ring]
        exact mul_le_mul_of_nonneg_left hPow4
          (mul_nonneg (mul_nonneg hAs (le_min hX0.le hY0.le))
            (Real.rpow_nonneg hQ0.le _))
      _ ≤ As * (2 * dfiTheorem1ErrorScale P X Y ε) := by
        exact mul_le_mul_of_nonneg_left hBase hAs
      _ = 2 * As * dfiTheorem1ErrorScale P X Y ε := by ring
  have hPhysical' :
      dfiEquation27InterpolatedPhysicalError Cp Q X Y 1 a b h K ≤
        2 * Ap * dfiTheorem1ErrorScale P X Y ε := by
    calc
      _ ≤ Ap * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) := by
        simpa only [K, Ap] using hPhysical
      _ ≤ Ap * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) := by
        rw [show Ap * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) =
            (Ap * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ (6 * η) by ring,
          show Ap * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) =
            (Ap * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ ε by ring]
        exact mul_le_mul_of_nonneg_left hPow6
          (mul_nonneg (mul_nonneg hAp (le_min hX0.le hY0.le))
            (Real.rpow_nonneg hQ0.le _))
      _ ≤ Ap * (2 * dfiTheorem1ErrorScale P X Y ε) := by
        exact mul_le_mul_of_nonneg_left hBase hAp
      _ = 2 * Ap * dfiTheorem1ErrorScale P X Y ε := by ring
  have hCentral' :
      dfiEquation27InterpolatedCentralTail Ct X Y 1
          (1 - 2 * η) η η a b h K ≤
        2 * At * dfiTheorem1ErrorScale P X Y ε := by
    calc
      _ ≤ At * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) := by
        simpa only [K, At] using hCentral
      _ ≤ At * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) := by
        rw [show At * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) =
            (At * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ (6 * η) by ring,
          show At * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) =
            (At * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ ε by ring]
        exact mul_le_mul_of_nonneg_left hPow6
          (mul_nonneg (mul_nonneg hAt (le_min hX0.le hY0.le))
            (Real.rpow_nonneg hQ0.le _))
      _ ≤ At * (2 * dfiTheorem1ErrorScale P X Y ε) := by
        exact mul_le_mul_of_nonneg_left hBase hAt
      _ = 2 * At * dfiTheorem1ErrorScale P X Y ε := by ring
  calc
    _ ≤ dfiEquation27InterpolatedSmallError Cs Q X Y (Q ^ 2) 1
          a b h K j +
        dfiEquation27InterpolatedPhysicalError Cp Q X Y 1 a b h K +
        dfiEquation27InterpolatedCentralTail Ct X Y 1
          (1 - 2 * η) η η a b h K := hRaw
    _ ≤ (2 * As + 2 * Ap + 2 * At) *
          dfiTheorem1ErrorScale P X Y ε := by
      calc
        _ ≤ 2 * As * dfiTheorem1ErrorScale P X Y ε +
            2 * Ap * dfiTheorem1ErrorScale P X Y ε +
            2 * At * dfiTheorem1ErrorScale P X Y ε :=
          add_le_add (add_le_add hSmall' hPhysical') hCentral'
        _ = _ := by ring
    _ ≤ C * dfiTheorem1ErrorScale P X Y ε := by
      have hTarget : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
        unfold dfiTheorem1ErrorScale
        exact mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans hf.one_le_P) _)
            (Real.rpow_nonneg (add_nonneg hX0.le hY0.le) _))
          (Real.rpow_nonneg hS0.le _)
      apply mul_le_mul_of_nonneg_right _ hTarget
      dsimp [C]
      linarith

set_option maxHeartbeats 2000000 in
/-- Scale-uniform equation-(27) main-branch estimate.  The constant is
selected before `P,X,Y,U,Q`, the source function, and every arithmetic
variable; its only data are the fixed derivative profiles and `ε`. -/
theorem exists_uniform_norm_sum_dfiEquation24Main_sub_centralSeries_le_theorem1ErrorScale
    (D E : ℕ → ℝ) (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P X Y U Q : ℝ} {w : DFIDeltaWeight Q}
        {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ},
      DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
      DFILocalizedBox f X Y →
      ∀ (hφ : DFIRedundantCutoff φ U), DFIRedundantCutoffProfile hφ Cφ →
      U ≤ P⁻¹ * min X Y →
      DFIDeltaWeightProfile w Cw → DFIDeltaWeightProfile w D →
      DFIWeightQuotientProfile w E →
      2 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b h : ℕ), 0 < a → 0 < b → 0 < h → a.Coprime b →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  let η : ℝ := ε / 16
  have hη : 0 < η := by dsimp [η]; positivity
  have hηhalf : η < 1 / 2 := by dsimp [η]; linarith
  have hη1 : η < 1 := hηhalf.trans (by norm_num)
  have hAlpha : 0 < 1 - 2 * η := by linarith
  obtain ⟨j, hjLarge⟩ := exists_nat_gt (2 / η)
  have hTwoDiv : (2 : ℝ) < 2 / η := by
    apply (lt_div_iff₀ hη).2
    nlinarith
  have hjNat : 2 ≤ j := by
    have : (2 : ℝ) < (j : ℝ) := hTwoDiv.trans hjLarge
    exact_mod_cast this.le
  have hj : 2 ≤ η * (j : ℝ) := by
    have hmul : 2 < (j : ℝ) * η := (div_lt_iff₀ hη).1 hjLarge
    nlinarith
  obtain ⟨Cpsi, hCpsi, hpsi⟩ := exists_bound_dfiPsi j
  obtain ⟨CpsiSucc, hCpsiSucc, hpsiSucc⟩ := exists_bound_dfiPsi (j + 1)
  let Cs : ℝ := dfiEquation27SmallProfileConstant
    D E j Cpsi CpsiSucc Cf Cφ
  let Cp : ℝ := dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw
  let Ct : ℝ := dfiEquation27CentralProfileConstant Cf Cφ
  let As : ℝ := Cs * (divisorEpsilonConstant η * 2 ^ η) *
      ((1 + η⁻¹) * 3 ^ η) *
      (12 * (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η)) ^ 2)
  let Ap : ℝ := (divisorEpsilonConstant η * 2 ^ η) *
      ((1 + η⁻¹) * 3 ^ η) * Cp *
      (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η)) ^ 2 * η⁻¹
  let At : ℝ := Ct * (divisorEpsilonConstant η * 2 ^ η) *
      (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η) + 4 * η⁻¹) ^ 2 * (1 + η⁻¹)
  let C : ℝ := 1 + 2 * (|As| + |Ap| + |At|)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro P X Y U Q w f φ hf hfC hbox hφ hφC hscale hwC hD hE hQ hU hQsq
  have hCs : 0 < Cs := by
    simpa only [Cs] using dfiEquation27SmallProfileConstant_pos
      hD hE hfC hφC j hCpsi hCpsiSucc
  have hCp : 0 < Cp := by
    simpa only [Cp] using dfiEquation27PhysicalMainProfileConstant_pos
      hfC hφC hwC
  have hCt : 0 < Ct := by
    simpa only [Ct] using dfiEquation27CentralProfileConstant_pos hfC hφC
  have hMain :=
    norm_sum_dfiEquation24Main_sub_centralSeries_le_source_split_interpolated_of_profiles
      hD hE hf hfC hbox hφ hφC hscale hwC hQ hU j hjNat
        hCpsi hpsi hCpsiSucc hpsiSucc
        1 (1 - 2 * η) η η (by norm_num) (by norm_num)
        hAlpha hη hη (by ring)
  let K : ℕ := dfiEquation27SourceSplitCutoff Q η
  have hSpec := dfiEquation27SourceSplitCutoff_spec hQ hη hη1
  have hKcut : (K : ℝ) ≤ Q ^ (1 - η) := by
    simpa [K] using dfiEquation27SourceSplitCutoff_cast_le hQ hη hη1
  have hQ0 : 0 < Q := by linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hS0 : 0 < X * Y := mul_pos hX0 hY0
  have hS1 : 1 ≤ X * Y := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ X * Y := mul_le_mul hf.one_le_X hf.one_le_Y
        zero_le_one (zero_le_one.trans hf.one_le_X)
  have hQsqLeX :=
    (dfiEquation30_optimized_Q_sq_le_lengths hf.one_le_P hX0 hY0 hQsq).1
  have hQXY : Q ≤ X * Y := by
    have hQQ : Q ≤ Q ^ 2 := by nlinarith
    have hXXY : X ≤ X * Y := by
      calc X = X * 1 := by ring
        _ ≤ X * Y := mul_le_mul_of_nonneg_left hf.one_le_Y hX0.le
    exact hQQ.trans (hQsqLeX.trans hXXY)
  have hDiv0 : 0 ≤ divisorEpsilonConstant η :=
    (divisorEpsilonConstant_pos η).le
  have hTwoPow : 0 ≤ (2 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
  have hThreePow : 0 ≤ (3 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
  have hEtaInv : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hOneEtaInv : 0 ≤ 1 + η⁻¹ := by linarith
  have hAs : 0 ≤ As := by
    change 0 ≤ Cs * (divisorEpsilonConstant η * 2 ^ η) *
      ((1 + η⁻¹) * 3 ^ η) *
      (12 * (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η)) ^ 2)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hCs.le (mul_nonneg hDiv0 hTwoPow))
        (mul_nonneg hOneEtaInv hThreePow))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hAp : 0 ≤ Ap := by
    change 0 ≤ (divisorEpsilonConstant η * 2 ^ η) *
      ((1 + η⁻¹) * 3 ^ η) * Cp *
      (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η)) ^ 2 * η⁻¹
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hDiv0 hTwoPow)
            (mul_nonneg hOneEtaInv hThreePow))
          hCp.le)
        (sq_nonneg _))
      hEtaInv
  have hAt : 0 ≤ At := by
    change 0 ≤ Ct * (divisorEpsilonConstant η * 2 ^ η) *
      (1 + 2 * |Real.eulerMascheroniConstant| +
        4 * (3 ^ η / η) + 4 * η⁻¹) ^ 2 * (1 + η⁻¹)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hCt.le (mul_nonneg hDiv0 hTwoPow))
        (sq_nonneg _))
      hOneEtaInv
  intro a b h ha hb hh hab haX hbY hhX
  have hRaw := hMain a b h K ha hb hh hab hSpec.1 hSpec.2.1
  have hSmall := dfiEquation27InterpolatedSmallError_source_le
    hf.one_le_X hf.one_le_Y (by linarith : 1 ≤ Q) hQXY hη hCs.le
      ha hb hh haX hbY hhX hSpec.1 hSpec.2.1 hKcut hjNat hj
  have hPhysical := dfiEquation27InterpolatedPhysicalError_source_le
    hf.one_le_X hf.one_le_Y hQ hQXY hη hη1 hCp.le
      ha hb hh haX hbY hhX
  have hCentral := dfiEquation27InterpolatedCentralTail_source_le
    hf.one_le_X hf.one_le_Y hQ hQXY hη hηhalf hCt.le
      ha hb hh haX hbY hhX
  have hPow4 : (X * Y) ^ (4 * η) ≤ (X * Y) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hS1 (by dsimp [η]; linarith)
  have hPow6 : (X * Y) ^ (6 * η) ≤ (X * Y) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hS1 (by dsimp [η]; linarith)
  have hBase := dfiEquation27_min_mul_Q_inv_mul_rpow_le_theorem1ErrorScale
    (ε := ε) hf.one_le_P hf.one_le_X hf.one_le_Y hQ0 hQsq
  have hSmall' :
      dfiEquation27InterpolatedSmallError Cs Q X Y (Q ^ 2) 1
          a b h K j ≤ 2 * As * dfiTheorem1ErrorScale P X Y ε := by
    calc
      _ ≤ As * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (4 * η) := by
        simpa only [As] using hSmall
      _ ≤ As * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) := by
        rw [show As * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (4 * η) =
            (As * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ (4 * η) by ring,
          show As * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) =
            (As * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ ε by ring]
        exact mul_le_mul_of_nonneg_left hPow4
          (mul_nonneg (mul_nonneg hAs (le_min hX0.le hY0.le))
            (Real.rpow_nonneg hQ0.le _))
      _ ≤ As * (2 * dfiTheorem1ErrorScale P X Y ε) := by
        exact mul_le_mul_of_nonneg_left hBase hAs
      _ = 2 * As * dfiTheorem1ErrorScale P X Y ε := by ring
  have hPhysical' :
      dfiEquation27InterpolatedPhysicalError Cp Q X Y 1 a b h K ≤
        2 * Ap * dfiTheorem1ErrorScale P X Y ε := by
    calc
      _ ≤ Ap * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) := by
        simpa only [K, Ap] using hPhysical
      _ ≤ Ap * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) := by
        rw [show Ap * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) =
            (Ap * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ (6 * η) by ring,
          show Ap * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) =
            (Ap * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ ε by ring]
        exact mul_le_mul_of_nonneg_left hPow6
          (mul_nonneg (mul_nonneg hAp (le_min hX0.le hY0.le))
            (Real.rpow_nonneg hQ0.le _))
      _ ≤ Ap * (2 * dfiTheorem1ErrorScale P X Y ε) := by
        exact mul_le_mul_of_nonneg_left hBase hAp
      _ = 2 * Ap * dfiTheorem1ErrorScale P X Y ε := by ring
  have hCentral' :
      dfiEquation27InterpolatedCentralTail Ct X Y 1
          (1 - 2 * η) η η a b h K ≤
        2 * At * dfiTheorem1ErrorScale P X Y ε := by
    calc
      _ ≤ At * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) := by
        simpa only [K, At] using hCentral
      _ ≤ At * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) := by
        rw [show At * min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ (6 * η) =
            (At * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ (6 * η) by ring,
          show At * (min X Y * Q ^ (-(1 : ℝ)) * (X * Y) ^ ε) =
            (At * min X Y * Q ^ (-(1 : ℝ))) * (X * Y) ^ ε by ring]
        exact mul_le_mul_of_nonneg_left hPow6
          (mul_nonneg (mul_nonneg hAt (le_min hX0.le hY0.le))
            (Real.rpow_nonneg hQ0.le _))
      _ ≤ At * (2 * dfiTheorem1ErrorScale P X Y ε) := by
        exact mul_le_mul_of_nonneg_left hBase hAt
      _ = 2 * At * dfiTheorem1ErrorScale P X Y ε := by ring
  calc
    _ ≤ dfiEquation27InterpolatedSmallError Cs Q X Y (Q ^ 2) 1
          a b h K j +
        dfiEquation27InterpolatedPhysicalError Cp Q X Y 1 a b h K +
        dfiEquation27InterpolatedCentralTail Ct X Y 1
          (1 - 2 * η) η η a b h K := by
      simpa only [Cs, Cp, Ct, hU] using hRaw
    _ ≤ (2 * As + 2 * Ap + 2 * At) *
          dfiTheorem1ErrorScale P X Y ε := by
      calc
        _ ≤ 2 * As * dfiTheorem1ErrorScale P X Y ε +
            2 * Ap * dfiTheorem1ErrorScale P X Y ε +
            2 * At * dfiTheorem1ErrorScale P X Y ε :=
          add_le_add (add_le_add hSmall' hPhysical') hCentral'
        _ = _ := by ring
    _ ≤ C * dfiTheorem1ErrorScale P X Y ε := by
      have hTarget : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
        unfold dfiTheorem1ErrorScale
        exact mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans hf.one_le_P) _)
            (Real.rpow_nonneg (add_nonneg hX0.le hY0.le) _))
          (Real.rpow_nonneg hS0.le _)
      apply mul_le_mul_of_nonneg_right _ hTarget
      dsimp [C]
      rw [abs_of_nonneg hAs, abs_of_nonneg hAp, abs_of_nonneg hAt]
      linarith

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

/-- Complete epsilon-loss absorption for the source-sharp double-tail
complement.  The internal displacement is `ε/16`; the two physical length
powers and the three arithmetic-average powers spend only `5ε/16`.  The
fourth-order tail contributes a nonpositive extra power of `Q`. -/
theorem dfiEquation29_doubleTail_loss_bundle_le
    {X Y Q ε CA : ℝ} {A B H : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hA : 0 < A) (hB : 0 < B)
    (hAX : (A : ℝ) ≤ 2 * X) (hBY : (B : ℝ) ≤ 2 * Y)
    (hε0 : 0 < ε) (hε4 : ε ≤ 4)
    (hCA : 0 ≤ CA)
    (hAverage : dfiEquation29ThreeGcdAverage H A B Q (ε / 16) ≤
      CA * Q ^ (1 / 2 : ℝ) * ((X * Y) ^ (ε / 16)) ^ 3) :
    let η : ℝ := ε / 16
    let α : ℝ := 3 / 4 + η
    let R : ℝ := (11 : ℝ) / Real.pi ^ 2
    (R ^ 4 * Q ^ (-η * (4 : ℝ))) *
        ((2 ^ α * 2 ^ α) * X ^ (α - 1 / 4) * Y ^ (α - 1 / 4) *
          (A : ℝ) ^ (α - 3 / 4) * (B : ℝ) ^ (α - 3 / 4) *
          (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) *
          (X * Y / Q)) *
        dfiEquation29ThreeGcdAverage H A B Q η ≤
      (R ^ 4 * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) * CA) *
        (((X * Y) ^ (3 / 2 : ℝ) * Q ^ (-(7 / 2 : ℝ))) *
          (X * Y) ^ ε) := by
  dsimp only
  let η : ℝ := ε / 16
  let α : ℝ := 3 / 4 + η
  let R : ℝ := (11 : ℝ) / Real.pi ^ 2
  let S : ℝ := X * Y
  let e : ℝ := (-2 + η) * α
  have hη : 0 < η := by dsimp [η]; positivity
  have hη4 : η ≤ 1 / 4 := by dsimp [η]; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hS0 : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith
  have hAB : (A : ℝ) * B ≤ 4 * S := by dsimp [S]; nlinarith
  have hABpow : (A : ℝ) ^ η * (B : ℝ) ^ η ≤
      2 ^ (2 * η) * S ^ η := by
    rw [← Real.mul_rpow hA0.le hB0.le]
    have hp := Real.rpow_le_rpow (mul_nonneg hA0.le hB0.le) hAB hη.le
    calc
      ((A : ℝ) * B) ^ η ≤ (4 * S) ^ η := hp
      _ = 2 ^ (2 * η) * S ^ η := by
        rw [Real.mul_rpow (by norm_num) hS0.le]
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
          show (2 : ℝ) ^ (2 : ℕ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hXYpow : X ^ (1 / 2 + η) * Y ^ (1 / 2 + η) =
      S ^ (1 / 2 : ℝ) * S ^ η := by
    rw [Real.rpow_add hX0, Real.rpow_add hY0,
      show X ^ (1 / 2 : ℝ) * X ^ η *
          (Y ^ (1 / 2 : ℝ) * Y ^ η) =
        (X ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) *
          (X ^ η * Y ^ η) by ring,
      ← Real.mul_rpow hX0.le hY0.le,
      ← Real.mul_rpow hX0.le hY0.le]
  have hQexp : -η * 4 + e + e - 1 + 1 / 2 ≤ -(7 / 2 : ℝ) := by
    dsimp [e, α]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hη.le
      (by linarith : η - 13 / 4 ≤ 0)]
  have hQpow : Q ^ (-η * (4 : ℝ)) * (Q ^ e * Q ^ e) * Q⁻¹ *
      Q ^ (1 / 2 : ℝ) ≤ Q ^ (-(7 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0,
      ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ
    linarith
  have hSsplit : S ^ (1 / 2 : ℝ) * S = S ^ (3 / 2 : ℝ) := by
    calc
      S ^ (1 / 2 : ℝ) * S = S ^ (1 / 2 : ℝ) * S ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = S ^ ((1 / 2 : ℝ) + 1) := by rw [Real.rpow_add hS0]
      _ = _ := by congr 1; ring
  have hLoss : S ^ η * S ^ η * (S ^ η) ^ 3 ≤ S ^ ε := by
    rw [show (S ^ η) ^ 3 = S ^ (3 * η) by
      rw [show (S ^ η) ^ 3 = (S ^ η) ^ (3 : ℝ) by norm_num,
        ← Real.rpow_mul hS0.le]
      congr 1
      ring,
      ← Real.rpow_add hS0, ← Real.rpow_add hS0]
    exact Real.rpow_le_rpow_of_exponent_le hS1 (by dsimp [η]; linarith)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hAvg0 : 0 ≤ dfiEquation29ThreeGcdAverage H A B Q η := by
    unfold dfiEquation29ThreeGcdAverage
    exact mul_nonneg
      (mul_nonneg (divisorEpsilonConstant_pos η).le
        (zero_le_one.trans (le_max_left _ _)))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [show (3 / 4 + ε / 16 : ℝ) - 1 / 4 = 1 / 2 + ε / 16 by ring,
    show (3 / 4 + ε / 16 : ℝ) - 3 / 4 = ε / 16 by ring]
  change (R ^ 4 * Q ^ (-η * (4 : ℝ))) *
      ((2 ^ α * 2 ^ α) * X ^ (1 / 2 + η) * Y ^ (1 / 2 + η) *
        (A : ℝ) ^ η * (B : ℝ) ^ η * (Q ^ e * Q ^ e) * (S / Q)) *
      dfiEquation29ThreeGcdAverage H A B Q η ≤ _
  calc
    _ = (R ^ 4 * Q ^ (-η * (4 : ℝ))) *
        ((2 ^ α * 2 ^ α) *
          (X ^ (1 / 2 + η) * Y ^ (1 / 2 + η)) *
          ((A : ℝ) ^ η * (B : ℝ) ^ η) *
          (Q ^ e * Q ^ e) * (S / Q)) *
        dfiEquation29ThreeGcdAverage H A B Q η := by ring
    _ ≤ (R ^ 4 * Q ^ (-η * (4 : ℝ))) *
        ((2 ^ α * 2 ^ α) * (S ^ (1 / 2 : ℝ) * S ^ η) *
          (2 ^ (2 * η) * S ^ η) * (Q ^ e * Q ^ e) * (S / Q)) *
        (CA * Q ^ (1 / 2 : ℝ) * (S ^ η) ^ 3) := by
      rw [hXYpow]
      gcongr
    _ = (R ^ 4 * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) * CA) *
        ((S ^ (1 / 2 : ℝ) * S) *
          (Q ^ (-η * (4 : ℝ)) * (Q ^ e * Q ^ e) * Q⁻¹ *
            Q ^ (1 / 2 : ℝ))) *
        (S ^ η * S ^ η * (S ^ η) ^ 3) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ (R ^ 4 * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) * CA) *
        (S ^ (3 / 2 : ℝ) * Q ^ (-(7 / 2 : ℝ))) * S ^ ε := by
      rw [hSsplit]
      gcongr
    _ = _ := by dsimp [η, α, R, S, e]; ring

/-- Epsilon-loss absorption for the genuinely two-variable recurrence in
the double-tail corner.  With internal displacement `ε/16`, the two
fourth-order integrations contribute `Q^(-8η)`.  After the Weil average
the resulting exponent is at most `Q^(-5/2)`, while the two physical
length powers, the source coefficients, the logarithm, and the arithmetic
average spend only `6η < ε`. -/
theorem dfiEquation29_doubleFullRecurrenceCorner_loss_bundle_le
    {X Y Q ε CA Krec : ℝ} {A B H : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y)
    (hA : 0 < A) (hB : 0 < B)
    (hAX : (A : ℝ) ≤ 2 * X) (hBY : (B : ℝ) ≤ 2 * Y)
    (hε0 : 0 < ε) (hε4 : ε ≤ 4)
    (hCA : 0 ≤ CA) (hKrec : 0 ≤ Krec)
    (hAverage : dfiEquation29ThreeGcdAverage H A B Q (ε / 16) ≤
      CA * Q ^ (1 / 2 : ℝ) * ((X * Y) ^ (ε / 16)) ^ 3) :
    let η : ℝ := ε / 16
    let α : ℝ := 3 / 4 + η
    let R : ℝ := 44
    ((R ^ 4 * Q ^ (-η * (4 : ℝ))) *
        (R ^ 4 * Q ^ (-η * (4 : ℝ)))) *
        ((2 ^ α * 2 ^ α) * X ^ (α - 1 / 4) * Y ^ (α - 1 / 4) *
          (A : ℝ) ^ (α - 3 / 4) * (B : ℝ) ^ (α - 3 / 4) *
          (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) *
          (Krec * min X Y * Real.log Q)) *
        dfiEquation29ThreeGcdAverage H A B Q η ≤
      ((R ^ 4 * R ^ 4) * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) *
          (16 / ε) * Krec * CA) *
        (((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
          Q ^ (1 / 2 : ℝ)) * (X * Y) ^ ε := by
  dsimp only
  let η : ℝ := ε / 16
  let α : ℝ := 3 / 4 + η
  let R : ℝ := 44
  let S : ℝ := X * Y
  let e : ℝ := (-2 + η) * α
  have hη : 0 < η := by dsimp [η]; positivity
  have hη4 : η ≤ 1 / 4 := by dsimp [η]; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hS0 : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith
  have hAB : (A : ℝ) * B ≤ 4 * S := by dsimp [S]; nlinarith
  have hABpow : (A : ℝ) ^ η * (B : ℝ) ^ η ≤
      2 ^ (2 * η) * S ^ η := by
    rw [← Real.mul_rpow hA0.le hB0.le]
    have hp := Real.rpow_le_rpow (mul_nonneg hA0.le hB0.le) hAB hη.le
    calc
      ((A : ℝ) * B) ^ η ≤ (4 * S) ^ η := hp
      _ = 2 ^ (2 * η) * S ^ η := by
        rw [Real.mul_rpow (by norm_num) hS0.le]
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
          show (2 : ℝ) ^ (2 : ℕ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hXYpow : X ^ (1 / 2 + η) * Y ^ (1 / 2 + η) =
      S ^ (1 / 2 : ℝ) * S ^ η := by
    rw [Real.rpow_add hX0, Real.rpow_add hY0,
      show X ^ (1 / 2 : ℝ) * X ^ η *
          (Y ^ (1 / 2 : ℝ) * Y ^ η) =
        (X ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) *
          (X ^ η * Y ^ η) by ring,
      ← Real.mul_rpow hX0.le hY0.le,
      ← Real.mul_rpow hX0.le hY0.le]
  have hlog : Real.log Q ≤ (16 / ε) * S ^ η := by
    have hlogQS : Real.log Q ≤ Real.log S :=
      Real.strictMonoOn_log.monotoneOn hQ0 hS0 hQXY
    have hlogS := Real.log_le_rpow_div hS0.le hη
    calc
      Real.log Q ≤ Real.log S := hlogQS
      _ ≤ S ^ η / η := hlogS
      _ = (16 / ε) * S ^ η := by
        dsimp [η]
        field_simp
  have hQexp : -η * 4 + -η * 4 + e + e + 1 / 2 ≤ -(5 / 2 : ℝ) := by
    dsimp [e, α]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hη.le
      (by linarith : 2 * η - 21 / 2 ≤ 0)]
  have hQpow :
      (Q ^ (-η * (4 : ℝ)) * Q ^ (-η * (4 : ℝ))) *
          (Q ^ e * Q ^ e) * Q ^ (1 / 2 : ℝ) ≤
        Q ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0,
      ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ
    linarith
  have hLoss : S ^ η * S ^ η * S ^ η * (S ^ η) ^ 3 ≤ S ^ ε := by
    rw [show (S ^ η) ^ 3 = S ^ (3 * η) by
      rw [show (S ^ η) ^ 3 = (S ^ η) ^ (3 : ℝ) by norm_num,
        ← Real.rpow_mul hS0.le]
      congr 1
      ring,
      ← Real.rpow_add hS0, ← Real.rpow_add hS0, ← Real.rpow_add hS0]
    exact Real.rpow_le_rpow_of_exponent_le hS1 (by dsimp [η]; linarith)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hAvg0 : 0 ≤ dfiEquation29ThreeGcdAverage H A B Q η := by
    unfold dfiEquation29ThreeGcdAverage
    exact mul_nonneg
      (mul_nonneg (divisorEpsilonConstant_pos η).le
        (zero_le_one.trans (le_max_left _ _)))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hlog0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  rw [show (3 / 4 + ε / 16 : ℝ) - 1 / 4 = 1 / 2 + ε / 16 by ring,
    show (3 / 4 + ε / 16 : ℝ) - 3 / 4 = ε / 16 by ring]
  change ((R ^ 4 * Q ^ (-η * (4 : ℝ))) *
      (R ^ 4 * Q ^ (-η * (4 : ℝ)))) *
      ((2 ^ α * 2 ^ α) * X ^ (1 / 2 + η) * Y ^ (1 / 2 + η) *
        (A : ℝ) ^ η * (B : ℝ) ^ η * (Q ^ e * Q ^ e) *
        (Krec * min X Y * Real.log Q)) *
      dfiEquation29ThreeGcdAverage H A B Q η ≤ _
  calc
    _ = (R ^ 4 * R ^ 4) * (2 ^ α * 2 ^ α) * Krec *
        (X ^ (1 / 2 + η) * Y ^ (1 / 2 + η)) *
        ((A : ℝ) ^ η * (B : ℝ) ^ η) * min X Y * Real.log Q *
        ((Q ^ (-η * (4 : ℝ)) * Q ^ (-η * (4 : ℝ))) *
          (Q ^ e * Q ^ e)) *
        dfiEquation29ThreeGcdAverage H A B Q η := by ring
    _ ≤ (R ^ 4 * R ^ 4) * (2 ^ α * 2 ^ α) * Krec *
        (S ^ (1 / 2 : ℝ) * S ^ η) *
        (2 ^ (2 * η) * S ^ η) * min X Y * ((16 / ε) * S ^ η) *
        ((Q ^ (-η * (4 : ℝ)) * Q ^ (-η * (4 : ℝ))) *
          (Q ^ e * Q ^ e)) *
        (CA * Q ^ (1 / 2 : ℝ) * (S ^ η) ^ 3) := by
      rw [hXYpow]
      gcongr
    _ = ((R ^ 4 * R ^ 4) * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) *
          (16 / ε) * Krec * CA) *
        ((S ^ (1 / 2 : ℝ) * min X Y) *
          ((Q ^ (-η * (4 : ℝ)) * Q ^ (-η * (4 : ℝ))) *
            (Q ^ e * Q ^ e) * Q ^ (1 / 2 : ℝ))) *
        (S ^ η * S ^ η * S ^ η * (S ^ η) ^ 3) := by ring
    _ ≤ ((R ^ 4 * R ^ 4) * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) *
          (16 / ε) * Krec * CA) *
        ((S ^ (1 / 2 : ℝ) * min X Y) * Q ^ (-(5 / 2 : ℝ))) *
        S ^ ε := by gcongr
    _ = _ := by
      have hQsplit : Q ^ (-(3 : ℝ)) * Q ^ (1 / 2 : ℝ) =
          Q ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_add hQ0]
        congr 1
        ring
      rw [← hQsplit]
      dsimp [η, α, R, S, e]
      ring

/-- Epsilon-loss absorption for either one-sided complement with the
physical equation-(30) mixed-`L¹` mass.  One fourth-order recurrence already
puts the modulus power at `Q⁻⁵ᐟ²`; logarithmic, coefficient, and gcd-average
losses consume only `6ε/16`. -/
theorem dfiEquation29_doubleMixedOneTail_loss_bundle_le
    {X Y Q ε CA : ℝ} {A B H : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y)
    (hA : 0 < A) (hB : 0 < B)
    (hAX : (A : ℝ) ≤ 2 * X) (hBY : (B : ℝ) ≤ 2 * Y)
    (hε0 : 0 < ε) (hε4 : ε ≤ 4)
    (hCA : 0 ≤ CA)
    (hAverage : dfiEquation29ThreeGcdAverage H A B Q (ε / 16) ≤
      CA * Q ^ (1 / 2 : ℝ) * ((X * Y) ^ (ε / 16)) ^ 3) :
    let η : ℝ := ε / 16
    let α : ℝ := 3 / 4 + η
    let R : ℝ := 44
    (R ^ 4 * Q ^ (-η * (4 : ℝ))) *
        ((2 ^ α * 2 ^ α) * X ^ (α - 1 / 4) * Y ^ (α - 1 / 4) *
          (A : ℝ) ^ (α - 3 / 4) * (B : ℝ) ^ (α - 3 / 4) *
          (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) *
          (min X Y * Real.log Q)) *
        dfiEquation29ThreeGcdAverage H A B Q η ≤
      (R ^ 4 * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) *
          (16 / ε) * CA) *
        (((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
          Q ^ (1 / 2 : ℝ)) * (X * Y) ^ ε := by
  dsimp only
  let η : ℝ := ε / 16
  let α : ℝ := 3 / 4 + η
  let R : ℝ := 44
  let S : ℝ := X * Y
  let e : ℝ := (-2 + η) * α
  have hη : 0 < η := by dsimp [η]; positivity
  have hη4 : η ≤ 1 / 4 := by dsimp [η]; linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hS0 : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith
  have hAB : (A : ℝ) * B ≤ 4 * S := by dsimp [S]; nlinarith
  have hABpow : (A : ℝ) ^ η * (B : ℝ) ^ η ≤
      2 ^ (2 * η) * S ^ η := by
    rw [← Real.mul_rpow hA0.le hB0.le]
    have hp := Real.rpow_le_rpow (mul_nonneg hA0.le hB0.le) hAB hη.le
    calc
      ((A : ℝ) * B) ^ η ≤ (4 * S) ^ η := hp
      _ = 2 ^ (2 * η) * S ^ η := by
        rw [Real.mul_rpow (by norm_num) hS0.le]
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
          show (2 : ℝ) ^ (2 : ℕ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hXYpow : X ^ (1 / 2 + η) * Y ^ (1 / 2 + η) =
      S ^ (1 / 2 : ℝ) * S ^ η := by
    rw [Real.rpow_add hX0, Real.rpow_add hY0,
      show X ^ (1 / 2 : ℝ) * X ^ η *
          (Y ^ (1 / 2 : ℝ) * Y ^ η) =
        (X ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) *
          (X ^ η * Y ^ η) by ring,
      ← Real.mul_rpow hX0.le hY0.le,
      ← Real.mul_rpow hX0.le hY0.le]
  have hlog : Real.log Q ≤ (16 / ε) * S ^ η := by
    have hlogQS : Real.log Q ≤ Real.log S :=
      Real.strictMonoOn_log.monotoneOn hQ0 hS0 hQXY
    have hlogS := Real.log_le_rpow_div hS0.le hη
    calc
      Real.log Q ≤ Real.log S := hlogQS
      _ ≤ S ^ η / η := hlogS
      _ = (16 / ε) * S ^ η := by
        dsimp [η]
        field_simp
  have hQexp : -η * 4 + e + e + 1 / 2 ≤ -(5 / 2 : ℝ) := by
    dsimp [e, α]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hη.le
      (by linarith : 2 * η - 13 / 2 ≤ 0)]
  have hQpow :
      Q ^ (-η * (4 : ℝ)) * (Q ^ e * Q ^ e) * Q ^ (1 / 2 : ℝ) ≤
        Q ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0,
      ← Real.rpow_add hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ
    linarith
  have hLoss : S ^ η * S ^ η * S ^ η * (S ^ η) ^ 3 ≤ S ^ ε := by
    rw [show (S ^ η) ^ 3 = S ^ (3 * η) by
      rw [show (S ^ η) ^ 3 = (S ^ η) ^ (3 : ℝ) by norm_num,
        ← Real.rpow_mul hS0.le]
      congr 1
      ring,
      ← Real.rpow_add hS0, ← Real.rpow_add hS0, ← Real.rpow_add hS0]
    exact Real.rpow_le_rpow_of_exponent_le hS1 (by dsimp [η]; linarith)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hAvg0 : 0 ≤ dfiEquation29ThreeGcdAverage H A B Q η := by
    unfold dfiEquation29ThreeGcdAverage
    exact mul_nonneg
      (mul_nonneg (divisorEpsilonConstant_pos η).le
        (zero_le_one.trans (le_max_left _ _)))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hlog0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  rw [show (3 / 4 + ε / 16 : ℝ) - 1 / 4 = 1 / 2 + ε / 16 by ring,
    show (3 / 4 + ε / 16 : ℝ) - 3 / 4 = ε / 16 by ring]
  change (R ^ 4 * Q ^ (-η * (4 : ℝ))) *
      ((2 ^ α * 2 ^ α) * X ^ (1 / 2 + η) * Y ^ (1 / 2 + η) *
        (A : ℝ) ^ η * (B : ℝ) ^ η * (Q ^ e * Q ^ e) *
        (min X Y * Real.log Q)) *
      dfiEquation29ThreeGcdAverage H A B Q η ≤ _
  calc
    _ = R ^ 4 * (2 ^ α * 2 ^ α) *
        (X ^ (1 / 2 + η) * Y ^ (1 / 2 + η)) *
        ((A : ℝ) ^ η * (B : ℝ) ^ η) * min X Y * Real.log Q *
        (Q ^ (-η * (4 : ℝ)) * (Q ^ e * Q ^ e)) *
        dfiEquation29ThreeGcdAverage H A B Q η := by ring
    _ ≤ R ^ 4 * (2 ^ α * 2 ^ α) *
        (S ^ (1 / 2 : ℝ) * S ^ η) *
        (2 ^ (2 * η) * S ^ η) * min X Y * ((16 / ε) * S ^ η) *
        (Q ^ (-η * (4 : ℝ)) * (Q ^ e * Q ^ e)) *
        (CA * Q ^ (1 / 2 : ℝ) * (S ^ η) ^ 3) := by
      rw [hXYpow]
      gcongr
    _ = (R ^ 4 * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) *
          (16 / ε) * CA) *
        ((S ^ (1 / 2 : ℝ) * min X Y) *
          (Q ^ (-η * (4 : ℝ)) * (Q ^ e * Q ^ e) * Q ^ (1 / 2 : ℝ))) *
        (S ^ η * S ^ η * S ^ η * (S ^ η) ^ 3) := by ring
    _ ≤ (R ^ 4 * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) *
          (16 / ε) * CA) *
        ((S ^ (1 / 2 : ℝ) * min X Y) * Q ^ (-(5 / 2 : ℝ))) *
        S ^ ε := by gcongr
    _ = _ := by
      have hQsplit : Q ^ (-(3 : ℝ)) * Q ^ (1 / 2 : ℝ) =
          Q ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_add hQ0]
        congr 1
        ring
      rw [← hQsplit]
      dsimp [η, α, R, S, e]
      ring

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

/-- Uniform-in-scale DFI Theorem 1 estimate for the retained `x`-dual
branch.  Once the three derivative profiles and `ε` are fixed, the witness
constant is independent of every dyadic scale and arithmetic parameter. -/
theorem exists_uniform_sum_dfiEquation29_xSingleRetained_le_theorem1ErrorScale
    (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε2 : ε < 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ},
      DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
      DFILocalizedBox f X Y →
      ∀ (hφ : DFIRedundantCutoff φ U),
      DFIRedundantCutoffProfile hφ Cφ →
      U ≤ P⁻¹ * min X Y →
      ∀ (w : DFIDeltaWeight Q), DFIDeltaWeightProfile w Cw →
      2 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
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
  obtain ⟨C₀, hC₀, hRetainedAll⟩ :=
    exists_uniform_sum_dfiEquation29_xSingleRetained_optimized_le
      Cf Cφ Cw η hη hηquarter η hη
  let B : ℝ := 2 ^ η * (8 / ε) * CL * CA
  let Ccore : ℝ := 2 * C₀ * 2 ^ (3 / 4 + η) * B
  let Cfinal : ℝ := 1 + Ccore * Real.sqrt 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro f φ P X Y U Q hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
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
  have hRetained := hRetainedAll hf hfC hbox hφ hφC hscale w hwC
    hQ hU hf.one_le_P hQsq
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

set_option maxHeartbeats 800000 in
/-- Uniform-in-scale DFI Theorem 1 estimate for the discarded
`x`-dual tail.  The witness depends only on `ε` and the three source
profiles. -/
theorem exists_uniform_sum_dfiEquation29_xSingleTail_le_theorem1ErrorScale
    (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε2 : ε < 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ},
      DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
      DFILocalizedBox f X Y →
      ∀ (hφ : DFIRedundantCutoff φ U),
      DFIRedundantCutoffProfile hφ Cφ →
      U ≤ P⁻¹ * min X Y →
      ∀ (w : DFIDeltaWeight Q), DFIDeltaWeightProfile w Cw →
      2 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
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
  obtain ⟨D₀, hD₀, hTail⟩ :=
    exists_uniform_sum_dfiEquation29_xSingleTail_l1_optimized_le
      η hη 1 hk η hη
  let C₀ := dfiEquation23PhysicalMixedDerivativeFiniteConstant Cf Cφ Cw 2
  let B : ℝ := 2 ^ η * (8 / ε) * CL * CA
  let R : ℝ :=
    2 * (C₀ * D₀ * (14 * Real.pi + 8) / ((1 : ℝ) - η - 3 / 4)) *
      (5 / Real.pi ^ 2) * 2 ^ (3 / 4 + η)
  let Ccore : ℝ := R * B
  let Cfinal : ℝ := 1 + |Ccore| * Real.sqrt 2
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro f φ P X Y U Q hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
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
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    exact dfiEquation23PhysicalMixedDerivativeFiniteConstant_pos
      hfC hφC hwC 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hden : 0 < (1 : ℝ) - η - 3 / 4 := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
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
  have hRaw := hTail hf hfC hbox hφ hφC hscale w hwC hU hf.one_le_P hQ hQsq
    a b ha hb (h : ℤ) (by exact_mod_cast hh.ne')
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
      apply mul_le_mul_of_nonneg_right _ hTarget
      have hmul : Ccore * Real.sqrt 2 ≤ |Ccore| * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self Ccore) (Real.sqrt_nonneg 2)
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

/-- Uniform-in-scale DFI Theorem 1 estimate for the retained `y`-dual
branch. -/
theorem exists_uniform_sum_dfiEquation29_ySingleRetained_le_theorem1ErrorScale
    (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε2 : ε < 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ},
      DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
      DFILocalizedBox f X Y →
      ∀ (hφ : DFIRedundantCutoff φ U),
      DFIRedundantCutoffProfile hφ Cφ → U ≤ P⁻¹ * min X Y →
      ∀ (w : DFIDeltaWeight Q), DFIDeltaWeightProfile w Cw →
      2 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
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
  obtain ⟨C₀, hC₀, hRetainedAll⟩ :=
    exists_uniform_sum_dfiEquation29_ySingleRetained_optimized_le
      Cf Cφ Cw η hη hηquarter η hη
  let B : ℝ := 2 ^ η * (8 / ε) * CL * CA
  let Ccore : ℝ := 2 * C₀ * 2 ^ (3 / 4 + η) * B
  let Cfinal : ℝ := 1 + Ccore * Real.sqrt 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro f φ P X Y U Q hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
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
  have hRetained := hRetainedAll hf hfC hbox hφ hφC hscale w hwC
    hQ hU hf.one_le_P hQsq
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

set_option maxHeartbeats 800000 in
/-- Uniform-in-scale DFI Theorem 1 estimate for the discarded
`y`-dual tail. -/
theorem exists_uniform_sum_dfiEquation29_ySingleTail_le_theorem1ErrorScale
    (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε2 : ε < 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ},
      DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
      DFILocalizedBox f X Y →
      ∀ (hφ : DFIRedundantCutoff φ U),
      DFIRedundantCutoffProfile hφ Cφ →
      U ≤ P⁻¹ * min X Y →
      ∀ (w : DFIDeltaWeight Q), DFIDeltaWeightProfile w Cw →
      2 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
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
  obtain ⟨D₀, hD₀, hTail⟩ :=
    exists_uniform_sum_dfiEquation29_ySingleTail_l1_optimized_le
      η hη 1 hk η hη
  let C₀ := dfiEquation23PhysicalMixedDerivativeFiniteConstant Cf Cφ Cw 2
  let B : ℝ := 2 ^ η * (8 / ε) * CL * CA
  let R : ℝ :=
    2 * (C₀ * D₀ * (14 * Real.pi + 8) / ((1 : ℝ) - η - 3 / 4)) *
      (5 / Real.pi ^ 2) * 2 ^ (3 / 4 + η)
  let Ccore : ℝ := R * B
  let Cfinal : ℝ := 1 + |Ccore| * Real.sqrt 2
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro f φ P X Y U Q hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
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
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    exact dfiEquation23PhysicalMixedDerivativeFiniteConstant_pos
      hfC hφC hwC 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hden : 0 < (1 : ℝ) - η - 3 / 4 := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
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
  have hRaw := hTail hf hfC hbox hφ hφC hscale w hwC hU hf.one_le_P hQ hQsq
    a b ha hb (h : ℤ) (by exact_mod_cast hh.ne')
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
      apply mul_le_mul_of_nonneg_right _ hTarget
      have hmul : Ccore * Real.sqrt 2 ≤ |Ccore| * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self Ccore) (Real.sqrt_nonneg 2)
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

/-- Uniform-in-scale DFI Theorem 1 estimate for the retained double-dual
rectangle. -/
theorem exists_uniform_sum_dfiEquation29_doubleRetained_le_theorem1ErrorScale
    (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ},
      DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
      DFILocalizedBox f X Y →
      ∀ (hφ : DFIRedundantCutoff φ U),
      DFIRedundantCutoffProfile hφ Cφ → U ≤ P⁻¹ * min X Y →
      ∀ (w : DFIDeltaWeight Q), DFIDeltaWeightProfile w Cw →
      2 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
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
  have hCA : 0 ≤ CA := by
    dsimp [CA]
    have hD : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    have hK : 0 ≤ 1 + η⁻¹ := by positivity
    have hThree : 0 ≤ (3 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hFour : 0 ≤ (4 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    positivity
  obtain ⟨C₀, hC₀, hRetainedAll⟩ :=
    exists_uniform_sum_dfiEquation29_doubleRetained_optimized_le
      Cf Cφ Cw η hη hηhalf η hη
  let B : ℝ :=
    (2 ^ (3 / 4 + η / 2) * 2 ^ (3 / 4 + η / 2)) *
      2 ^ η * (8 / ε) * CA
  let Ccore : ℝ := 4 * C₀ * B
  let Cfinal : ℝ := 1 + Ccore * 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro f φ P X Y U Q hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
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
  have hRetained := hRetainedAll hf hfC hbox hφ hφC hscale w hwC
    hQ hU hf.one_le_P hQsq
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

/-- Scale-independent constant produced by the optimized double-tail part
of DFI equation (30). -/
noncomputable def dfiEquation29DoubleTailTheorem1Constant
    (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ) (ε Cdiv : ℝ) : ℝ :=
  let η : ℝ := ε / 16
  let α : ℝ := 3 / 4 + η
  let R : ℝ := 44
  let CA : ℝ := divisorEpsilonConstant η * 3 ^ η *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) *
        ((1 + η⁻¹) * 3 ^ η)) *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) * 3)
  let K := dfiEquation23PhysicalMixedDerivativeFiniteConstant Cf Cφ Cw 8
  let B₁ : ℝ :=
    (K * Cdiv * Cdiv * (14 * Real.pi + 8) *
        (14 * Real.pi + 8) * 9 * α⁻¹ / ((4 : ℝ) - η - 3 / 4)) +
    (K * Cdiv * Cdiv * (14 * Real.pi + 8) *
        (14 * Real.pi + 8) * 9 * α⁻¹ / ((4 : ℝ) - η - 3 / 4))
  let B₂ : ℝ := Cdiv * Cdiv * (14 * Real.pi + 8) *
    (14 * Real.pi + 8) * 9 /
      (((4 : ℝ) - η - 3 / 4) * ((4 : ℝ) - η - 3 / 4))
  let Lone : ℝ := R ^ 4 * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) *
    (16 / ε) * CA
  let Lcorner : ℝ := (R ^ 4 * R ^ 4) * (2 ^ α * 2 ^ α) *
    2 ^ (2 * η) * (16 / ε) * K * CA
  let Ccore : ℝ := 4 * B₁ * Lone + 4 * B₂ * Lcorner
  1 + |Ccore| * 2

/-- The complete complement of the retained double-dual rectangle in DFI
equation (29), with the corrected physical mixed-`L¹` one-sided bounds, has
the published Theorem 1 error scale. -/
theorem sum_dfiEquation29_doubleTail_le_theorem1ErrorScale_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q ε : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε4 : ε < 4)
    (Cdiv : ℝ) (hCdiv : 0 < Cdiv)
    (hDiv : ∀ n : ℕ, 0 < n →
      ‖divisorWeight n‖ ≤ Cdiv * (n : ℝ) ^ (ε / 16)) :
    0 < dfiEquation29DoubleTailTheorem1Constant Cf Cφ Cw ε Cdiv ∧
      ∀ (a b h : ℕ), 0 < a → 0 < b → a.Coprime b → 0 < h →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        dfiEquation29DoubleTailTheorem1Constant Cf Cφ Cw ε Cdiv *
          dfiTheorem1ErrorScale P X Y ε := by
  let η : ℝ := ε / 16
  let α : ℝ := 3 / 4 + η
  let R : ℝ := 44
  let CA : ℝ := divisorEpsilonConstant η * 3 ^ η *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) *
        ((1 + η⁻¹) * 3 ^ η)) *
      Real.sqrt ((divisorEpsilonConstant η * 4 ^ η) * 3)
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
  have hCA : 0 ≤ CA := by
    dsimp [CA]
    have hD : 0 ≤ divisorEpsilonConstant η :=
      (divisorEpsilonConstant_pos η).le
    have hK : 0 ≤ 1 + η⁻¹ := by positivity
    have hThree : 0 ≤ (3 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    have hFour : 0 ≤ (4 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) _
    positivity
  let K := dfiEquation23PhysicalMixedDerivativeFiniteConstant Cf Cφ Cw 8
  have hK : 0 < K := by
    dsimp [K]
    exact dfiEquation23PhysicalMixedDerivativeFiniteConstant_pos hfC hφC hwC 8
  let Ky := K
  let Kx := K
  let Kxy := K
  let Cdivy := Cdiv
  let Cdivx := Cdiv
  let Cdivxy := Cdiv
  have hKy : 0 < Ky := by simpa only [Ky] using hK
  have hKx : 0 < Kx := by simpa only [Kx] using hK
  have hKxy : 0 < Kxy := by simpa only [Kxy] using hK
  have hCdivy : 0 < Cdivy := by simpa only [Cdivy] using hCdiv
  have hCdivx : 0 < Cdivx := by simpa only [Cdivx] using hCdiv
  have hCdivxy : 0 < Cdivxy := by simpa only [Cdivxy] using hCdiv
  have hTail :=
    sum_dfiEquation29_doubleTail_mixed_recurrence_optimized_le_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hU hf.one_le_P hQ hQsq
        η hη hηquarter η hη Cdiv hCdiv hDiv
  let B₁ : ℝ :=
    (Ky * Cdivy * Cdivy * (14 * Real.pi + 8) *
        (14 * Real.pi + 8) * 9 * α⁻¹ / ((4 : ℝ) - η - 3 / 4)) +
    (Kx * Cdivx * Cdivx * (14 * Real.pi + 8) *
        (14 * Real.pi + 8) * 9 * α⁻¹ / ((4 : ℝ) - η - 3 / 4))
  let B₂ : ℝ := Cdivxy * Cdivxy * (14 * Real.pi + 8) *
    (14 * Real.pi + 8) * 9 /
      (((4 : ℝ) - η - 3 / 4) * ((4 : ℝ) - η - 3 / 4))
  let Lone : ℝ := R ^ 4 * (2 ^ α * 2 ^ α) * 2 ^ (2 * η) *
    (16 / ε) * CA
  let Lcorner : ℝ := (R ^ 4 * R ^ 4) * (2 ^ α * 2 ^ α) *
    2 ^ (2 * η) * (16 / ε) * Kxy * CA
  let Ccore : ℝ := 4 * B₁ * Lone + 4 * B₂ * Lcorner
  let Cfinal : ℝ := 1 + |Ccore| * 2
  have hden : 0 < (4 : ℝ) - η - 3 / 4 := by
    dsimp [η]
    linarith
  have hB₁ : 0 ≤ B₁ := by
    dsimp [B₁]
    apply add_nonneg <;> apply div_nonneg
    · positivity
    · exact hden.le
    · positivity
    · exact hden.le
  have hB₂ : 0 ≤ B₂ := by
    dsimp [B₂]
    apply div_nonneg
    · positivity
    · exact mul_nonneg hden.le hden.le
  have hLone : 0 ≤ Lone := by dsimp [Lone, R, α]; positivity
  have hLcorner : 0 ≤ Lcorner := by dsimp [Lcorner, R, α]; positivity
  have hCcore : 0 ≤ Ccore := by dsimp [Ccore]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  have hCfinalEq : Cfinal =
      dfiEquation29DoubleTailTheorem1Constant Cf Cφ Cw ε Cdiv := by
    dsimp [Cfinal, Ccore, B₁, B₂, Lone, Lcorner,
      dfiEquation29DoubleTailTheorem1Constant, η, α, R, CA,
      Ky, Kx, Kxy, Cdivy, Cdivx, Cdivxy, K]
  refine ⟨hCfinalEq ▸ hCfinal, ?_⟩
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
  have hOneLoss := dfiEquation29_doubleMixedOneTail_loss_bundle_le
    hf.one_le_X hf.one_le_Y (by linarith) hQXY ha hb haX hbY
      hε0 hε4.le hCA hAverage
  have hCornerLoss := dfiEquation29_doubleFullRecurrenceCorner_loss_bundle_le
    hf.one_le_X hf.one_le_Y (by linarith) hQXY ha hb haX hbY
      hε0 hε4.le hCA hKxy.le hAverage
  have hRaw := hTail a b ha hb hab (h : ℤ)
    (by exact_mod_cast hh.ne')
  let Base : ℝ :=
    (2 ^ α * 2 ^ α) * X ^ (α - 1 / 4) * Y ^ (α - 1 / 4) *
      (a : ℝ) ^ (α - 3 / 4) * (b : ℝ) ^ (α - 3 / 4) *
      (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α))
  let Avg : ℝ := dfiEquation29ThreeGcdAverage h a b Q η
  let Core : ℝ :=
    ((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
      Q ^ (1 / 2 : ℝ) * (X * Y) ^ ε
  have hOne :
      (R ^ 4 * Q ^ (-η * (4 : ℝ))) *
          (Base * (min X Y * Real.log Q)) * Avg ≤ Lone * Core := by
    simpa only [η, α, R, CA, Base, Avg, Lone, Core, mul_assoc] using hOneLoss
  have hCorner :
      ((R ^ 4 * Q ^ (-η * (4 : ℝ))) *
          (R ^ 4 * Q ^ (-η * (4 : ℝ)))) *
          (Base * (Kxy * min X Y * Real.log Q)) * Avg ≤
        Lcorner * Core := by
    simpa only [η, α, R, CA, Base, Avg, Lcorner, Core, mul_assoc] using hCornerLoss
  have hRaw' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h η q) ≤ Ccore * Core := by
    calc
      _ ≤ (4 * B₁ * (R ^ 4 * Q ^ (-η * (4 : ℝ))) *
              (Base * (min X Y * Real.log Q)) +
            4 * B₂ *
              ((R ^ 4 * Q ^ (-η * (4 : ℝ))) *
                (R ^ 4 * Q ^ (-η * (4 : ℝ)))) *
              (Base * (Kxy * min X Y * Real.log Q))) * Avg := by
          simpa only [η, α, R, B₁, B₂, Base, Avg,
            dfiEquation29ThreeGcdAverage] using hRaw
      _ = 4 * B₁ *
            ((R ^ 4 * Q ^ (-η * (4 : ℝ))) *
              (Base * (min X Y * Real.log Q)) * Avg) +
          4 * B₂ *
            (((R ^ 4 * Q ^ (-η * (4 : ℝ))) *
              (R ^ 4 * Q ^ (-η * (4 : ℝ)))) *
              (Base * (Kxy * min X Y * Real.log Q)) * Avg) := by ring
      _ ≤ 4 * B₁ * (Lone * Core) + 4 * B₂ * (Lcorner * Core) := by gcongr
      _ = Ccore * Core := by dsimp [Ccore]; ring
  have hCore := dfiEquation29_doubleRetained_zeroEpsilon_le_secondError
    hf.one_le_X hf.one_le_Y hQ0
  calc
    _ ≤ Ccore * Core := hRaw'
    _ ≤ Ccore * (2 *
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)))) *
        (X * Y) ^ ε := by
      rw [show Ccore * Core = Ccore *
          ((((X * Y) ^ (1 / 2 : ℝ) * Q ^ (-(3 : ℝ)) * min X Y) *
            Q ^ (1 / 2 : ℝ)) * (X * Y) ^ ε) by rfl]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hCore
          (Real.rpow_nonneg hXY0.le ε)) hCcore
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
      linarith [le_abs_self Ccore]
    _ = dfiEquation29DoubleTailTheorem1Constant Cf Cφ Cw ε Cdiv *
          dfiTheorem1ErrorScale P X Y ε := by rw [hCfinalEq]

/-- Existential compatibility form of the profile-explicit Theorem 1
double-tail estimate. -/
theorem exists_sum_dfiEquation29_doubleTail_le_theorem1ErrorScale
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
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  have hη : 0 < ε / 16 := by positivity
  obtain ⟨Cdiv, hCdiv, hDiv⟩ := exists_norm_divisorWeight_le_rpow (ε / 16) hη
  have hBound := sum_dfiEquation29_doubleTail_le_theorem1ErrorScale_of_profiles
    hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq hε0 hε4
      Cdiv hCdiv hDiv
  refine ⟨dfiEquation29DoubleTailTheorem1Constant Cf Cφ Cw ε Cdiv,
    hBound.1, hBound.2⟩

/-- Uniform-in-scale DFI Theorem 1 estimate for the full discarded
double-dual complement.  Its constant is fixed before every source and
dyadic scale. -/
theorem exists_uniform_sum_dfiEquation29_doubleTail_le_theorem1ErrorScale
    (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ},
      DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
      DFILocalizedBox f X Y →
      ∀ (hφ : DFIRedundantCutoff φ U),
      DFIRedundantCutoffProfile hφ Cφ →
      U ≤ P⁻¹ * min X Y →
      ∀ (w : DFIDeltaWeight Q), DFIDeltaWeightProfile w Cw →
      2 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b h : ℕ), 0 < a → 0 < b → a.Coprime b → 0 < h →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  have hη : 0 < ε / 16 := by positivity
  obtain ⟨Cdiv, hCdiv, hDiv⟩ := exists_norm_divisorWeight_le_rpow (ε / 16) hη
  let C := dfiEquation29DoubleTailTheorem1Constant Cf Cφ Cw ε Cdiv
  have hC : 0 < C := by
    unfold C dfiEquation29DoubleTailTheorem1Constant
    positivity
  refine ⟨C, hC, ?_⟩
  intro f φ P X Y U Q hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
  have hBound := sum_dfiEquation29_doubleTail_le_theorem1ErrorScale_of_profiles
    hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq hε0 hε4
      Cdiv hCdiv hDiv
  simpa only [C] using hBound.2

/-! ## Equation (30): common-cutoff assembly -/

/-- The published DFI error scale is monotone in its epsilon loss once the
dyadic lengths are at least one. -/
theorem dfiTheorem1ErrorScale_mono_epsilon
    {P X Y ε₁ ε₂ : ℝ} (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hε : ε₁ ≤ ε₂) :
    dfiTheorem1ErrorScale P X Y ε₁ ≤
      dfiTheorem1ErrorScale P X Y ε₂ := by
  unfold dfiTheorem1ErrorScale
  have hXY : 1 ≤ X * Y := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ X * Y := mul_le_mul hX hY zero_le_one (zero_le_one.trans hX)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hXY (by linarith))
    (mul_nonneg
      (Real.rpow_nonneg (zero_le_one.trans hP) _)
      (Real.rpow_nonneg (add_nonneg (zero_le_one.trans hX)
        (zero_le_one.trans hY)) _))

set_option maxHeartbeats 4000000 in
/-- The dyadic positive-shift form of DFI Theorem 1.  This theorem assembles
the exact source identity, equations (27) and (29), at one common cutoff
`ε/16`; the six off-diagonal branches and the main branch are all bounded by
the error scale in equation (30). -/
theorem exists_norm_dfiDyadicShiftedDivisorSum_sub_centralSeries_le_theorem1ErrorScale
    {P X Y U Q ε : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b M N h : ℕ), 0 < a → 0 < b → 0 < h → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      ‖dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) -
          dfiEquation27CentralSeries a b h f‖ ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  obtain ⟨Cmain, hCmain, hMain⟩ :=
    exists_norm_sum_dfiEquation24Main_sub_centralSeries_le_theorem1ErrorScale
      w hf hfC hbox hφ hφC hscale hwC hQ hU hQsq hε0 hε4
  obtain ⟨Cxr, hCxr, hXr⟩ :=
    exists_sum_dfiEquation29_xSingleRetained_le_theorem1ErrorScale
      hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
        (show 0 < ε / 2 by positivity) (show ε / 2 < 2 by linarith)
  obtain ⟨Cxt, hCxt, hXt⟩ :=
    exists_sum_dfiEquation29_xSingleTail_le_theorem1ErrorScale
      hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
        (show 0 < ε / 2 by positivity) (show ε / 2 < 2 by linarith)
  obtain ⟨Cyr, hCyr, hYr⟩ :=
    exists_sum_dfiEquation29_ySingleRetained_le_theorem1ErrorScale
      hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
        (show 0 < ε / 2 by positivity) (show ε / 2 < 2 by linarith)
  obtain ⟨Cyt, hCyt, hYt⟩ :=
    exists_sum_dfiEquation29_ySingleTail_le_theorem1ErrorScale
      hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
        (show 0 < ε / 2 by positivity) (show ε / 2 < 2 by linarith)
  obtain ⟨Cdr, hCdr, hDr⟩ :=
    exists_sum_dfiEquation29_doubleRetained_le_theorem1ErrorScale
      hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
        (show 0 < ε / 2 by positivity) (show ε / 2 < 4 by linarith)
  obtain ⟨Cdt, hCdt, hDt⟩ :=
    exists_sum_dfiEquation29_doubleTail_le_theorem1ErrorScale
      hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq hε0 hε4
  let C : ℝ := Cmain + Cxr + Cxt + Cyr + Cyt + Cdr + Cdt
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a b M N h ha hb hh hab hM hN haX hbY hhX
  have hParts :=
    norm_dfiDyadicShiftedDivisorSum_sub_sourceCentralSeries_le_equation29_parts
      w hf hbox hφ hU.symm a b M N h ha hb hM hN (ε / 16)
  have hMain' := hMain a b h ha hb hh hab haX hbY hhX
  have hScaleHalf :
      dfiTheorem1ErrorScale P X Y (ε / 2) ≤
        dfiTheorem1ErrorScale P X Y ε :=
    dfiTheorem1ErrorScale_mono_epsilon hf.one_le_P hf.one_le_X hf.one_le_Y
      (by linarith)
  have hCut : (ε / 2) / 8 = ε / 16 := by ring
  have hXr' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cxr * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hXr a b h ha hb hh haX hbY hhX).trans
      (mul_le_mul_of_nonneg_left hScaleHalf hCxr.le)
  have hXt' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cxt * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hXt a b h ha hb hh haX hbY hhX).trans
      (mul_le_mul_of_nonneg_left hScaleHalf hCxt.le)
  have hYr' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cyr * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hYr a b h ha hb hh haX hbY hhX).trans
      (mul_le_mul_of_nonneg_left hScaleHalf hCyr.le)
  have hYt' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cyt * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hYt a b h ha hb hh haX hbY hhX).trans
      (mul_le_mul_of_nonneg_left hScaleHalf hCyt.le)
  have hDr' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cdr * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hDr a b h ha hb hab hh haX hbY hhX).trans
      (mul_le_mul_of_nonneg_left hScaleHalf hCdr.le)
  have hDt' := hDt a b h ha hb hab hh haX hbY hhX
  calc
    _ ≤ ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h)‖ +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) := hParts
    _ ≤ (Cmain + Cxr + Cxt + Cyr + Cyt + Cdr + Cdt) *
        dfiTheorem1ErrorScale P X Y ε := by
      linarith
    _ = C * dfiTheorem1ErrorScale P X Y ε := by rfl

set_option maxHeartbeats 4000000 in
/-- Scale-uniform dyadic positive-shift DFI Theorem 1.  The witness
constant is chosen from the fixed source and cutoff derivative profiles
before any dyadic scale, source function, delta weight, or arithmetic
parameter is introduced. -/
theorem exists_uniform_norm_dfiDyadicShiftedDivisorSum_sub_centralSeries_le_theorem1ErrorScale
    (D E : ℕ → ℝ) (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P X Y U Q : ℝ} {w : DFIDeltaWeight Q}
        {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ},
      DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
      DFILocalizedBox f X Y →
      ∀ (hφ : DFIRedundantCutoff φ U), DFIRedundantCutoffProfile hφ Cφ →
      U ≤ P⁻¹ * min X Y →
      DFIDeltaWeightProfile w Cw → DFIDeltaWeightProfile w D →
      DFIWeightQuotientProfile w E →
      2 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N h : ℕ), 0 < a → 0 < b → 0 < h → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      ‖dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) -
          dfiEquation27CentralSeries a b h f‖ ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  obtain ⟨Cmain, hCmain, hMain⟩ :=
    exists_uniform_norm_sum_dfiEquation24Main_sub_centralSeries_le_theorem1ErrorScale
      D E Cf Cφ Cw ε hε0 hε4
  obtain ⟨Cxr, hCxr, hXr⟩ :=
    exists_uniform_sum_dfiEquation29_xSingleRetained_le_theorem1ErrorScale
      Cf Cφ Cw (ε / 2) (by positivity) (by linarith)
  obtain ⟨Cxt, hCxt, hXt⟩ :=
    exists_uniform_sum_dfiEquation29_xSingleTail_le_theorem1ErrorScale
      Cf Cφ Cw (ε / 2) (by positivity) (by linarith)
  obtain ⟨Cyr, hCyr, hYr⟩ :=
    exists_uniform_sum_dfiEquation29_ySingleRetained_le_theorem1ErrorScale
      Cf Cφ Cw (ε / 2) (by positivity) (by linarith)
  obtain ⟨Cyt, hCyt, hYt⟩ :=
    exists_uniform_sum_dfiEquation29_ySingleTail_le_theorem1ErrorScale
      Cf Cφ Cw (ε / 2) (by positivity) (by linarith)
  obtain ⟨Cdr, hCdr, hDr⟩ :=
    exists_uniform_sum_dfiEquation29_doubleRetained_le_theorem1ErrorScale
      Cf Cφ Cw (ε / 2) (by positivity) (by linarith)
  obtain ⟨Cdt, hCdt, hDt⟩ :=
    exists_uniform_sum_dfiEquation29_doubleTail_le_theorem1ErrorScale
      Cf Cφ Cw ε hε0 hε4
  let C : ℝ := Cmain + Cxr + Cxt + Cyr + Cyt + Cdr + Cdt
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro P X Y U Q w f φ hf hfC hbox hφ hφC hscale hwC hD hE hQ hU hQsq
    a b M N h ha hb hh hab hM hN haX hbY hhX
  have hParts :=
    norm_dfiDyadicShiftedDivisorSum_sub_sourceCentralSeries_le_equation29_parts
      w hf hbox hφ hU.symm a b M N h ha hb hM hN (ε / 16)
  have hMain' :=
    hMain hf hfC hbox hφ hφC hscale hwC hD hE hQ hU hQsq
      a b h ha hb hh hab haX hbY hhX
  have hScaleHalf :
      dfiTheorem1ErrorScale P X Y (ε / 2) ≤
        dfiTheorem1ErrorScale P X Y ε :=
    dfiTheorem1ErrorScale_mono_epsilon hf.one_le_P hf.one_le_X hf.one_le_Y
      (by linarith)
  have hCut : (ε / 2) / 8 = ε / 16 := by ring
  have hXr' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cxr * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hXr hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
      a b h ha hb hh haX hbY hhX).trans
        (mul_le_mul_of_nonneg_left hScaleHalf hCxr.le)
  have hXt' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cxt * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hXt hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
      a b h ha hb hh haX hbY hhX).trans
        (mul_le_mul_of_nonneg_left hScaleHalf hCxt.le)
  have hYr' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cyr * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hYr hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
      a b h ha hb hh haX hbY hhX).trans
        (mul_le_mul_of_nonneg_left hScaleHalf hCyr.le)
  have hYt' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cyt * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hYt hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
      a b h ha hb hh haX hbY hhX).trans
        (mul_le_mul_of_nonneg_left hScaleHalf hCyt.le)
  have hDr' :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) ≤
        Cdr * dfiTheorem1ErrorScale P X Y ε := by
    rw [← hCut]
    exact (hDr hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
      a b h ha hb hab hh haX hbY hhX).trans
        (mul_le_mul_of_nonneg_left hScaleHalf hCdr.le)
  have hDt' := hDt hf hfC hbox hφ hφC hscale w hwC hQ hU hQsq
    a b h ha hb hab hh haX hbY hhX
  calc
    _ ≤ ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h)‖ +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h (ε / 16) q) := hParts
    _ ≤ (Cmain + Cxr + Cxt + Cyr + Cyt + Cdr + Cdt) *
        dfiTheorem1ErrorScale P X Y ε := by
      linarith
    _ = C * dfiTheorem1ErrorScale P X Y ε := by rfl

/-- The optimized DFI error scale is invariant under exchanging the two
physical variables. -/
theorem dfiTheorem1ErrorScale_swap (P X Y ε : ℝ) :
    dfiTheorem1ErrorScale P Y X ε = dfiTheorem1ErrorScale P X Y ε := by
  unfold dfiTheorem1ErrorScale
  rw [add_comm X Y, mul_comm Y X]

/-- Swapping the physical variables swaps the two orders in DFI's mixed
derivative.  This is the analytic identity needed to remove a redundant
coordinate-swapped equation-(2) assumption from the signed theorem. -/
theorem dfiMixedDeriv_swap
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (i j : ℕ) (x y : ℝ) :
    dfiMixedDeriv i j (dfiSwapWeight f) x y =
      dfiMixedDeriv j i f y x := by
  have hswap : ContDiff ℝ ∞ (Function.uncurry (dfiSwapWeight f)) := by
    change ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.2 p.1)
    exact hf.comp (contDiff_snd.prodMk contDiff_fst)
  have hleft :
      dfiMixedDeriv i j (dfiSwapWeight f) x y =
        dfiPartialY i (dfiPartialX j (Function.uncurry f)) (y, x) := by
    rw [dfiMixedDeriv_eq_partialXY hswap]
    rw [dfiPartialX_apply i (contDiff_dfiPartialY j hswap)]
    rw [dfiPartialY_apply i (contDiff_dfiPartialX j hf)]
    congr 2
    funext z
    rw [dfiPartialX_apply j hf]
    rw [dfiPartialY_apply j hswap]
    rfl
  rw [hleft, dfiPartialY_dfiPartialX_comm hf j i]
  exact (dfiMixedDeriv_eq_partialXY hf j i y x).symm

/-- Equation (2) is invariant under exchanging the two physical variables. -/
theorem DFIEquation2.swap
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} (hf : DFIEquation2 f P X Y) :
    DFIEquation2 (dfiSwapWeight f) P Y X := by
  have hswapSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiSwapWeight f)) := by
    change ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.2 p.1)
    exact hf.smooth.comp (contDiff_snd.prodMk contDiff_fst)
  refine
    { one_le_P := hf.one_le_P
      one_le_X := hf.one_le_Y
      one_le_Y := hf.one_le_X
      smooth := hswapSmooth
      compactSupport := ?_
      support_pos := ?_
      derivativeBound := ?_ }
  · change HasCompactSupport ((Function.uncurry f) ∘ Prod.swap)
    exact hf.compactSupport.comp_homeomorph
      (UniformEquiv.prodComm ℝ ℝ).toHomeomorph
  · intro p hp
    rcases p with ⟨x, y⟩
    have hp' : (y, x) ∈ Function.support (Function.uncurry f) := by
      simpa [dfiSwapWeight] using hp
    have hxy := hf.support_pos hp'
    exact ⟨hxy.2, hxy.1⟩
  · intro i j
    obtain ⟨C, hC, hBound⟩ := hf.derivativeBound j i
    refine ⟨C, hC, ?_⟩
    intro x y hx hy
    rw [dfiMixedDeriv_swap hf.smooth]
    have h := hBound y x hy hx
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h

/-- A chosen equation-(2) constant profile swaps by transposing its two
derivative indices. -/
theorem DFIEquation2Profile.swap
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} {C : ℕ → ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hC : DFIEquation2Profile f P X Y C) :
    DFIEquation2Profile (dfiSwapWeight f) P Y X (fun i j => C j i) := by
  refine ⟨fun i j => hC.positive j i, ?_⟩
  intro i j x y hx hy
  rw [dfiMixedDeriv_swap hf.smooth]
  have h := hC.bound j i y x hy hx
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h

/-- A localized source box is invariant under exchanging its coordinates. -/
theorem DFILocalizedBox.swap
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hf : DFILocalizedBox f X Y) :
    DFILocalizedBox (dfiSwapWeight f) Y X := by
  refine ⟨?_⟩
  intro p hp
  rcases p with ⟨x, y⟩
  have hp' : (y, x) ∈ Function.support (Function.uncurry f) := by
    simpa [dfiSwapWeight] using hp
  have hxy := hf.support_subset hp'
  exact ⟨hxy.2, hxy.1⟩

set_option maxHeartbeats 4000000 in
/-- Signed-shift dyadic DFI theorem.  The two visible equation-(2) profile
hypotheses are the source-order and coordinate-swapped analytic inputs; this
form is designed for the Hughes--Young source family, where both are proved
uniformly from the same explicit smooth weight. -/
theorem exists_uniform_norm_dfiDyadicShiftedDivisorSum_sub_signedCentralSeries_le_theorem1ErrorScale
    (D E : ℕ → ℝ) (Cf CfSwap : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P X Y U Q : ℝ} {w : DFIDeltaWeight Q}
        {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ},
      DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
      DFILocalizedBox f X Y →
      DFIEquation2 (dfiSwapWeight f) P Y X →
      DFIEquation2Profile (dfiSwapWeight f) P Y X CfSwap →
      DFILocalizedBox (dfiSwapWeight f) Y X →
      ∀ (hφ : DFIRedundantCutoff φ U), DFIRedundantCutoffProfile hφ Cφ →
      U ≤ P⁻¹ * min X Y →
      DFIDeltaWeightProfile w Cw → DFIDeltaWeightProfile w D →
      DFIWeightQuotientProfile w E →
      2 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ) (r : ℤ), 0 < a → 0 < b → r ≠ 0 → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) →
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) →
      ‖dfiDyadicShiftedDivisorSum f a b M N r -
          dfiSignedCentralSeries a b r f‖ ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  obtain ⟨Cpos, hCpos, hPos⟩ :=
    exists_uniform_norm_dfiDyadicShiftedDivisorSum_sub_centralSeries_le_theorem1ErrorScale
      D E Cf Cφ Cw ε hε0 hε4
  obtain ⟨Cneg, hCneg, hNeg⟩ :=
    exists_uniform_norm_dfiDyadicShiftedDivisorSum_sub_centralSeries_le_theorem1ErrorScale
      D E CfSwap Cφ Cw ε hε0 hε4
  let C : ℝ := Cpos + Cneg
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro P X Y U Q w f φ hf hfC hbox hfSwap hfSwapC hboxSwap
    hφ hφC hscale hwC hD hE hQ hU hQsq a b M N r ha hb hr hab
    hM hN haX hbY hrPos hrNeg
  have hErrNonneg : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
    unfold dfiTheorem1ErrorScale
    exact mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (zero_le_one.trans hf.one_le_P) _)
        (Real.rpow_nonneg
          (add_nonneg (zero_le_one.trans hf.one_le_X)
            (zero_le_one.trans hf.one_le_Y)) _))
      (Real.rpow_nonneg
        (mul_nonneg (zero_le_one.trans hf.one_le_X)
          (zero_le_one.trans hf.one_le_Y)) _)
  cases r with
  | ofNat h =>
      have hh : 0 < h := by
        by_contra hh
        have : h = 0 := Nat.eq_zero_of_not_pos hh
        exact hr (by simp [this])
      have hhX : (h : ℝ) ≤ 2 * X := by
        exact hrPos (by simp) |>.trans_eq (by simp)
      have hBound := hPos hf hfC hbox hφ hφC hscale hwC hD hE hQ hU hQsq
        a b M N h ha hb hh hab hM hN haX hbY hhX
      calc
        ‖dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) -
            dfiSignedCentralSeries a b (h : ℤ) f‖
            = ‖dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) -
                dfiEquation27CentralSeries a b h f‖ := by
                  rw [dfiSignedCentralSeries_ofNat]
        _ ≤ Cpos * dfiTheorem1ErrorScale P X Y ε := hBound
        _ ≤ C * dfiTheorem1ErrorScale P X Y ε := by
          apply mul_le_mul_of_nonneg_right _
          · exact hErrNonneg
          · dsimp [C]
            linarith
  | negSucc h =>
      let k : ℕ := h + 1
      have hk : 0 < k := by dsimp [k]; omega
      have hkY : (k : ℝ) ≤ 2 * Y := by
        simpa [k] using hrNeg (by simp)
      have hscaleSwap : U ≤ P⁻¹ * min Y X := by
        simpa [min_comm] using hscale
      have hQsqSwap : Q ^ 2 = P⁻¹ * (Y + X)⁻¹ * (Y * X) := by
        simpa [add_comm, mul_comm] using hQsq
      have hBound := hNeg hfSwap hfSwapC hboxSwap hφ hφC hscaleSwap
        hwC hD hE hQ hU hQsqSwap b a N M k hb ha hk hab.symm
        hN hM hbY haX hkY
      have hSource := dfiDyadicShiftedDivisorSum_swap f a b M N (Int.negSucc h)
      calc
        ‖dfiDyadicShiftedDivisorSum f a b M N (Int.negSucc h) -
            dfiSignedCentralSeries a b (Int.negSucc h) f‖
            = ‖dfiDyadicShiftedDivisorSum (dfiSwapWeight f) b a N M (k : ℤ) -
                dfiEquation27CentralSeries b a k (dfiSwapWeight f)‖ := by
                  rw [hSource]
                  simp [dfiSignedCentralSeries, k]
        _ ≤ Cneg * dfiTheorem1ErrorScale P Y X ε := hBound
        _ = Cneg * dfiTheorem1ErrorScale P X Y ε := by
          rw [dfiTheorem1ErrorScale_swap]
        _ ≤ C * dfiTheorem1ErrorScale P X Y ε := by
          apply mul_le_mul_of_nonneg_right _
          · exact hErrNonneg
          · dsimp [C]
            linarith

/-- The dyadic DFI estimate with the paper's auxiliary cutoffs constructed
internally.  Thus the caller supplies only the equation-(2) source weight and
the optimized physical scales, not a delta-symbol oracle. -/
theorem exists_norm_dfiDyadicShiftedDivisorSum_sub_centralSeries_le_theorem1ErrorScale_native
    {P X Y U Q ε : ℝ} {f : ℝ → ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 8 ≤ Q)
    (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b M N h : ℕ), 0 < a → 0 < b → 0 < h → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y → (h : ℝ) ≤ 2 * X →
      ‖dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) -
          dfiEquation27CentralSeries a b h f‖ ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  obtain ⟨Cf, hCf⟩ := hf.exists_profile
  obtain ⟨Cφ, hCφ⟩ := exists_dfiUniformRedundantCutoff_profile
  obtain ⟨Cw, hCw⟩ := exists_dfiUniformDeltaWeight_profile
  obtain ⟨E, hE⟩ := exists_dfiUniformDeltaWeight_quotient_profile
  have hQ0 : 0 < Q := by linarith
  have hU0 : 0 < U := by rw [hU]; positivity
  let φ : ℝ → ℂ := dfiUniformRedundantCutoff U
  let hφ : DFIRedundantCutoff φ U := dfiUniformRedundantCutoff_spec U hU0
  let w : DFIDeltaWeight Q := dfiUniformDeltaWeight Q hQ
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_dfiDyadicShiftedDivisorSum_sub_centralSeries_le_theorem1ErrorScale
      Cw E Cf Cφ Cw ε hε0 hε4
  exact ⟨C, hC, hBound hf hCf hbox hφ (hCφ U hU0) hscale
    (hCw Q hQ) (hCw Q hQ) (hE Q hQ) (by linarith) hU hQsq⟩

/-- Native signed form of DFI Theorem 1 on one localized dyadic box.  The
coordinate-swapped analytic data and every auxiliary cutoff are constructed
inside the proof; the only hypotheses left are DFI equation (2), the literal
box support, the optimized source scales, and the published nonzero-shift
range. -/
theorem exists_norm_dfiDyadicShiftedDivisorSum_sub_signedCentralSeries_le_theorem1ErrorScale_native
    {P X Y U Q ε : ℝ} {f : ℝ → ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 8 ≤ Q)
    (hU : U = Q ^ 2)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b M N : ℕ) (r : ℤ), 0 < a → 0 < b → r ≠ 0 → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) →
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) →
      ‖dfiDyadicShiftedDivisorSum f a b M N r -
          dfiSignedCentralSeries a b r f‖ ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  obtain ⟨Cf, hCf⟩ := hf.exists_profile
  obtain ⟨Cφ, hCφ⟩ := exists_dfiUniformRedundantCutoff_profile
  obtain ⟨Cw, hCw⟩ := exists_dfiUniformDeltaWeight_profile
  obtain ⟨E, hE⟩ := exists_dfiUniformDeltaWeight_quotient_profile
  have hU0 : 0 < U := by rw [hU]; positivity
  let φ : ℝ → ℂ := dfiUniformRedundantCutoff U
  let hφ : DFIRedundantCutoff φ U := dfiUniformRedundantCutoff_spec U hU0
  let w : DFIDeltaWeight Q := dfiUniformDeltaWeight Q hQ
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_dfiDyadicShiftedDivisorSum_sub_signedCentralSeries_le_theorem1ErrorScale
      Cw E Cf (fun i j => Cf j i) Cφ Cw ε hε0 hε4
  refine ⟨C, hC, ?_⟩
  exact hBound hf hCf hbox hf.swap (hCf.swap hf) hbox.swap hφ
    (hCφ U hU0) hscale (hCw Q hQ) (hCw Q hQ) (hE Q hQ)
    (by linarith) hU hQsq

end RiemannZeta.GuthMaynard
