import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_second_optimized {P X Y Q : ℝ} (hP : 0 < P) (hX : 0 < X) (hY : 0 < Y)
    (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    (X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)) =
      P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
        (X * Y) ^ (1 / 4 : ℝ) := by
  have hXY : 0 < X * Y := mul_pos hX hY
  have hSum : 0 < X + Y := add_pos hX hY
  have hQpow : Q ^ (-(5 / 2 : ℝ)) = (Q ^ 2) ^ (-(5 / 4 : ℝ)) := by
    rw [show Q ^ 2 = Q ^ (2 : ℝ) by norm_num, ← Real.rpow_mul hQ.le]
    congr 1
    ring
  rw [hQpow, hQsq]
  rw [Real.mul_rpow (by positivity : 0 ≤ P⁻¹ * (X + Y)⁻¹) hXY.le,
    Real.mul_rpow (inv_nonneg.mpr hP.le) (inv_nonneg.mpr hSum.le),
    Real.inv_rpow hP.le, Real.inv_rpow hSum.le]
  rw [← Real.rpow_neg hP.le, ← Real.rpow_neg hSum.le]
  field_simp
  rw [show (X * Y) ^ (3 / 2 : ℝ) * (X + Y) ^ (5 / 4 : ℝ) *
        (X * Y) ^ (-(5 / 4 : ℝ)) =
      ((X * Y) ^ (3 / 2 : ℝ) * (X * Y) ^ (-(5 / 4 : ℝ))) *
        (X + Y) ^ (5 / 4 : ℝ) by ring,
    ← Real.rpow_add hXY,
    show (3 / 2 : ℝ) + -(5 / 4 : ℝ) = 1 / 4 by norm_num,
    show (X + Y) * (X + Y) ^ (1 / 4 : ℝ) *
        (X * Y) ^ (1 / 4 : ℝ) =
      ((X + Y) ^ (1 : ℝ) * (X + Y) ^ (1 / 4 : ℝ)) *
        (X * Y) ^ (1 / 4 : ℝ) by rw [Real.rpow_one],
    ← Real.rpow_add hSum]
  norm_num
  ring

theorem probe_first_optimized {a b : ℕ} {P X Y Q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    (((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) * Q ^ (-(1 : ℝ))) ≤
      P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
        (X * Y) ^ (1 / 4 : ℝ) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hXY : 0 < X * Y := mul_pos hX0 hY0
  have hSum : 0 < X + Y := add_pos hX0 hY0
  have hQpow : Q ^ (-(1 : ℝ)) = (Q ^ 2) ^ (-(1 / 2 : ℝ)) := by
    rw [show Q ^ 2 = Q ^ (2 : ℝ) by norm_num, ← Real.rpow_mul hQ.le]
    congr 1
    ring
  have hQinv : Q ^ (-(1 : ℝ)) =
      P ^ (1 / 2 : ℝ) * (X + Y) ^ (1 / 2 : ℝ) *
        (X * Y) ^ (-(1 / 2 : ℝ)) := by
    rw [hQpow, hQsq]
    rw [Real.mul_rpow (by positivity : 0 ≤ P⁻¹ * (X + Y)⁻¹) hXY.le,
      Real.mul_rpow (inv_nonneg.mpr hP0.le) (inv_nonneg.mpr hSum.le),
      Real.inv_rpow hP0.le, Real.inv_rpow hSum.le]
    rw [← Real.rpow_neg hP0.le, ← Real.rpow_neg hSum.le]
    congr 1 <;> ring_nf
  have hsumOne : 1 ≤ X + Y := by linarith
  have hxsum : X ≤ X + Y := by linarith
  have hysum : Y ≤ X + Y := by linarith
  have hXYsumSq : X * Y ≤ (X + Y) * (X + Y) :=
    mul_le_mul hxsum hysum hY0.le (by linarith)
  have hXYsumCube : X * Y ≤ (X + Y) ^ 3 := by
    calc
      X * Y ≤ (X + Y) * (X + Y) := hXYsumSq
      _ ≤ (X + Y) ^ 3 := by nlinarith
  have hroot : (X * Y) ^ (1 / 4 : ℝ) ≤
      (X + Y) ^ (3 / 4 : ℝ) := by
    have hr := Real.rpow_le_rpow hXY.le hXYsumCube (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc
      _ ≤ ((X + Y) ^ 3) ^ (1 / 4 : ℝ) := hr
      _ = _ := by
        rw [show (X + Y) ^ 3 = (X + Y) ^ (3 : ℝ) by norm_num,
          ← Real.rpow_mul hSum.le]
        congr 1
        ring
  have hXYhalf : (X * Y) ^ (1 / 2 : ℝ) =
      (X * Y) ^ (1 / 4 : ℝ) * (X * Y) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hXY]
    congr 1
    ring
  have hXYhalfSq : ((X * Y) ^ (1 / 2 : ℝ)) ^ 2 = X * Y := by
    rw [show ((X * Y) ^ (1 / 2 : ℝ)) ^ 2 =
        ((X * Y) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul hXY.le]
    norm_num
  have hSumHalfSq : ((X + Y) ^ (1 / 2 : ℝ)) ^ 2 = X + Y := by
    rw [show ((X + Y) ^ (1 / 2 : ℝ)) ^ 2 =
        ((X + Y) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul hSum.le]
    norm_num
  have hscale : (X + Y) ^ (-(1 / 2 : ℝ)) *
      (X * Y) ^ (1 / 2 : ℝ) ≤
      (X + Y) ^ (1 / 4 : ℝ) * (X * Y) ^ (1 / 4 : ℝ) := by
    calc
      _ = ((X + Y) ^ (-(1 / 2 : ℝ)) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ (1 / 4 : ℝ) := by
        rw [hXYhalf]
        ring
      _ ≤ ((X + Y) ^ (-(1 / 2 : ℝ)) *
          (X + Y) ^ (3 / 4 : ℝ)) * (X * Y) ^ (1 / 4 : ℝ) := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_add hSum]
        congr 1 <;> ring_nf
  rw [hQinv]
  have habInv : (((a : ℝ) * b)⁻¹) ≤ 1 := by
    apply (inv_le_one₀ (by positivity : (0 : ℝ) < (a : ℝ) * b)).2
    have habOne : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (mul_ne_zero ha.ne' hb.ne')
    exact_mod_cast habOne
  have hPpow : P ^ (1 / 2 : ℝ) ≤ P ^ (5 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  calc
    _ = (((a : ℝ) * b)⁻¹) * P ^ (1 / 2 : ℝ) *
        ((X + Y) ^ (-(1 / 2 : ℝ)) * (X * Y) ^ (1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, Real.rpow_neg hSum.le,
        Real.rpow_neg hXY.le]
      field_simp
      rw [hSumHalfSq, hXYhalfSq]
      ring
    _ ≤ 1 * P ^ (5 / 4 : ℝ) *
        ((X + Y) ^ (1 / 4 : ℝ) * (X * Y) ^ (1 / 4 : ℝ)) := by
      gcongr
    _ = _ := by ring

example {a b : ℕ} {P X Y Q ε : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 0 < Q)
    (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    (((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) * Q ^ (-1 + ε) +
      (X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ) + ε)) ≤
      2 * (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
        (X * Y) ^ (1 / 4 + ε)) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hXY : 0 < X * Y := mul_pos hX0 hY0
  have hSum : 0 < X + Y := add_pos hX0 hY0
  have hXYOne : 1 ≤ X * Y := by
    nlinarith [mul_nonneg (show 0 ≤ X by linarith) (show 0 ≤ Y by linarith)]
  have hPinv : P⁻¹ ≤ 1 := (inv_le_one₀ hP0).2 hP
  have hSumInv : (X + Y)⁻¹ ≤ 1 :=
    (inv_le_one₀ hSum).2 (by linarith)
  have hQsqLe : Q ^ 2 ≤ X * Y := by
    rw [hQsq]
    calc
      P⁻¹ * (X + Y)⁻¹ * (X * Y) ≤ 1 * 1 * (X * Y) := by gcongr
      _ = X * Y := by ring
  have hQle : Q ≤ X * Y := by
    nlinarith [sq_nonneg (Q - X * Y)]
  have hQeps : Q ^ ε ≤ (X * Y) ^ ε :=
    Real.rpow_le_rpow hQ.le hQle hε
  have hFirst0 := show
      (((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) * Q ^ (-(1 : ℝ))) ≤
        P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ) by
    exact probe_first_optimized ha hb hP hX hY hQ hQsq
  have hSecond0 :
      (X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)) =
        P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ) := by
    exact probe_second_optimized hP0 hX0 hY0 hQ hQsq
  have hTargetFactor :
      (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ ε =
        P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 + ε) := by
    calc
      _ = P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          ((X * Y) ^ (1 / 4 : ℝ) * (X * Y) ^ ε) := by ring
      _ = _ := by rw [← Real.rpow_add hXY]
  have hFirst :
      ((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) * Q ^ (-1 + ε) ≤
        P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 + ε) := by
    rw [Real.rpow_add hQ]
    rw [show ((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) *
          (Q ^ (-(1 : ℝ)) * Q ^ ε) =
        (((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) * Q ^ (-(1 : ℝ))) *
          Q ^ ε by ring]
    calc
      _ ≤ (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ ε := by gcongr
      _ = _ := hTargetFactor
  have hSecond :
      (X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ) + ε) ≤
        P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 + ε) := by
    rw [Real.rpow_add hQ]
    rw [show (X * Y) ^ (3 / 2 : ℝ) / (X + Y) *
          (Q ^ (-(5 / 2 : ℝ)) * Q ^ ε) =
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ))) *
          Q ^ ε by ring,
      hSecond0]
    calc
      _ ≤ (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ ε := by gcongr
      _ = _ := hTargetFactor
  linarith

end RiemannZeta.GuthMaynard
