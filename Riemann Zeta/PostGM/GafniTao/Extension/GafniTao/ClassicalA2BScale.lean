import GafniTao.ClassicalA2BMajorants

/-!
# Integer scale selection for the classical `A²B` pair

For `9/4 ≤ tau ≤ 4` the continuous optimum is
`Y = N^((4-tau)/7)`.  The two A-process lengths are the literal natural
floors of `Y` and `Y²`.  Floors are essential at `tau = 4`: rounding upward
would destroy the curvature smallness hypothesis.
-/

namespace GafniTao

noncomputable section

noncomputable def classicalA2BExponent (tau : ℝ) : ℝ := (4 - tau) / 7

noncomputable def classicalA2BScale (N : ℕ) (tau : ℝ) : ℝ :=
  (N : ℝ) ^ classicalA2BExponent tau

noncomputable def classicalA2BFirstShift (N : ℕ) (tau : ℝ) : ℕ :=
  Nat.floor (classicalA2BScale N tau)

noncomputable def classicalA2BSecondShift (N : ℕ) (tau : ℝ) : ℕ :=
  Nat.floor (classicalA2BScale N tau ^ 2)

theorem classicalA2BExponent_nonneg {tau : ℝ} (htau : tau ≤ 4) :
    0 ≤ classicalA2BExponent tau := by
  unfold classicalA2BExponent
  linarith

theorem classicalA2BExponent_le_quarter {tau : ℝ} (htau : 9 / 4 ≤ tau) :
    classicalA2BExponent tau ≤ 1 / 4 := by
  unfold classicalA2BExponent
  norm_num at htau ⊢
  linarith

theorem classicalA2BScale_one_le
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 4) :
    1 ≤ classicalA2BScale N tau := by
  unfold classicalA2BScale
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  simpa using Real.one_le_rpow hNReal (classicalA2BExponent_nonneg htau)

theorem classicalA2BScale_pos
    {N : ℕ} {tau : ℝ} (hN : 0 < N) :
    0 < classicalA2BScale N tau := by
  unfold classicalA2BScale
  exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem base_sq_div_classicalA2BScale
    {N : ℕ} {tau : ℝ} (hN : 0 < N) :
    (N : ℝ) ^ 2 / classicalA2BScale N tau =
      (N : ℝ) ^ ((tau + 10) / 7) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold classicalA2BScale classicalA2BExponent
  rw [← Real.rpow_natCast, ← Real.rpow_sub hNReal]
  congr 1
  ring

theorem classicalA2B_height_scale_identity
    {N : ℕ} {tau : ℝ} (hN : 0 < N) :
    (N : ℝ) ^ tau * classicalA2BScale N tau ^ 3 /
        (N : ℝ) ^ 4 =
      1 / classicalA2BScale N tau ^ 4 := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold classicalA2BScale classicalA2BExponent
  have hcubed : ((N : ℝ) ^ ((4 - tau) / 7)) ^ 3 =
      (N : ℝ) ^ (((4 - tau) / 7) * 3) := by
    calc
      ((N : ℝ) ^ ((4 - tau) / 7)) ^ 3 =
          ((N : ℝ) ^ ((4 - tau) / 7)) ^ (3 : ℝ) :=
        (Real.rpow_natCast _ 3).symm
      _ = (N : ℝ) ^ (((4 - tau) / 7) * 3) :=
        (Real.rpow_mul hNReal.le _ _).symm
  have hfourth : ((N : ℝ) ^ ((4 - tau) / 7)) ^ 4 =
      (N : ℝ) ^ (((4 - tau) / 7) * 4) := by
    calc
      ((N : ℝ) ^ ((4 - tau) / 7)) ^ 4 =
          ((N : ℝ) ^ ((4 - tau) / 7)) ^ (4 : ℝ) :=
        (Real.rpow_natCast _ 4).symm
      _ = (N : ℝ) ^ (((4 - tau) / 7) * 4) :=
        (Real.rpow_mul hNReal.le _ _).symm
  rw [hcubed, hfourth, ← Real.rpow_natCast,
    ← Real.rpow_add hNReal, ← Real.rpow_sub hNReal,
    one_div, ← Real.rpow_neg hNReal.le]
  congr 1
  ring

theorem classicalA2BFirstShift_pos
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 4) :
    0 < classicalA2BFirstShift N tau := by
  unfold classicalA2BFirstShift
  exact Nat.floor_pos.mpr (classicalA2BScale_one_le hN htau)

theorem classicalA2BSecondShift_pos
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 4) :
    0 < classicalA2BSecondShift N tau := by
  unfold classicalA2BSecondShift
  apply Nat.floor_pos.mpr
  have hY := classicalA2BScale_one_le hN htau
  nlinarith

theorem half_le_natFloor {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hx0 : 0 ≤ x := hx.trans' zero_le_one
  have hfloorPos : 1 ≤ Nat.floor x := Nat.floor_pos.mpr hx
  by_cases hxTwo : x ≤ 2
  · have hfloorReal : (1 : ℝ) ≤ Nat.floor x := by exact_mod_cast hfloorPos
    linarith
  · have hlt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith

theorem classicalA2BScale_half_le_firstShift
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 4) :
    classicalA2BScale N tau / 2 ≤ classicalA2BFirstShift N tau := by
  unfold classicalA2BFirstShift
  exact half_le_natFloor (classicalA2BScale_one_le hN htau)

theorem classicalA2BScale_sq_half_le_secondShift
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 4) :
    classicalA2BScale N tau ^ 2 / 2 ≤
      classicalA2BSecondShift N tau := by
  unfold classicalA2BSecondShift
  apply half_le_natFloor
  have hY := classicalA2BScale_one_le hN htau
  nlinarith

theorem classicalA2BScale_le_sqrt
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : 9 / 4 ≤ tau) :
    classicalA2BScale N tau ≤ Real.sqrt (N : ℝ) := by
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hExp := classicalA2BExponent_le_quarter htau
  have hQuarterHalf : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  unfold classicalA2BScale
  rw [show Real.sqrt (N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) by
    exact Real.sqrt_eq_rpow (N : ℝ)]
  exact Real.rpow_le_rpow_of_exponent_le hNReal (hExp.trans hQuarterHalf)

theorem classicalA2BScale_sq_le_sqrt
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : 9 / 4 ≤ tau) :
    classicalA2BScale N tau ^ 2 ≤ Real.sqrt (N : ℝ) := by
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hTwoExp : 2 * classicalA2BExponent tau ≤ 1 / 2 := by
    have := classicalA2BExponent_le_quarter htau
    linarith
  unfold classicalA2BScale
  calc
    ((N : ℝ) ^ classicalA2BExponent tau) ^ 2 =
        ((N : ℝ) ^ classicalA2BExponent tau) ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = (N : ℝ) ^ (classicalA2BExponent tau * 2) :=
      (Real.rpow_mul (zero_le_one.trans hNReal) _ _).symm
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNReal (by simpa [mul_comm] using hTwoExp)
    _ = Real.sqrt (N : ℝ) := (Real.sqrt_eq_rpow (N : ℝ)).symm

theorem classicalA2BFirstShift_cast_le_sqrt
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : 9 / 4 ≤ tau) :
    (classicalA2BFirstShift N tau : ℝ) ≤ Real.sqrt (N : ℝ) := by
  exact (Nat.floor_le (by
    unfold classicalA2BScale
    positivity)).trans
      (classicalA2BScale_le_sqrt hN htau)

theorem classicalA2BSecondShift_cast_le_sqrt
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : 9 / 4 ≤ tau) :
    (classicalA2BSecondShift N tau : ℝ) ≤ Real.sqrt (N : ℝ) := by
  exact (Nat.floor_le (by positivity)).trans
    (classicalA2BScale_sq_le_sqrt hN htau)

theorem classicalA2B_shift_sum_le
    {N : ℕ} {tau : ℝ} (hN : 1024 ≤ N) (htau : 9 / 4 ≤ tau) :
    classicalA2BFirstShift N tau + classicalA2BSecondShift N tau ≤ N := by
  have hNOne : 1 ≤ N := by omega
  have hfirst := classicalA2BFirstShift_cast_le_sqrt hNOne htau
  have hsecond := classicalA2BSecondShift_cast_le_sqrt hNOne htau
  have hsqrtSq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)
  have hsqrtNonneg := Real.sqrt_nonneg (N : ℝ)
  have hNReal : (32 : ℝ) ≤ N := by exact_mod_cast (show 32 ≤ N by omega)
  have hsqrtLower : 4 ≤ Real.sqrt (N : ℝ) := by
    have hsixteenSq : Real.sqrt 16 ^ 2 = (16 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsixteenNonneg := Real.sqrt_nonneg 16
    have hsixteen : Real.sqrt 16 = 4 := by nlinarith
    rw [← hsixteen]
    exact Real.sqrt_le_sqrt (by linarith)
  have htwoSqrt : 2 * Real.sqrt (N : ℝ) ≤ N := by
    nlinarith
  exact_mod_cast (show
    (classicalA2BFirstShift N tau : ℝ) +
      classicalA2BSecondShift N tau ≤ N by linarith)

theorem classicalA2BFirstShift_le
    {N : ℕ} {tau : ℝ} (hN : 1024 ≤ N) (htau : 9 / 4 ≤ tau) :
    classicalA2BFirstShift N tau ≤ N := by
  exact (Nat.le_add_right _ _).trans
    (classicalA2B_shift_sum_le hN htau)

theorem classicalA2BSecondShift_admissible
    {N : ℕ} {tau : ℝ} (hN : 1024 ≤ N) (htau : 9 / 4 ≤ tau) :
    classicalA2BSecondShift N tau ≤
      N - (classicalA2BFirstShift N tau - 1) := by
  have hsum := classicalA2B_shift_sum_le hN htau
  omega

theorem classicalA2B_curvature_small
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htauUpper : tau ≤ 4) :
    (N : ℝ) ^ tau * (classicalA2BFirstShift N tau : ℝ) *
        (classicalA2BSecondShift N tau : ℝ) /
          ((N : ℝ) + 1) ^ 4 ≤ 1 := by
  let Y := classicalA2BScale N tau
  have hY0 : 0 ≤ Y := by dsimp only [Y, classicalA2BScale]; positivity
  have hfirst : (classicalA2BFirstShift N tau : ℝ) ≤ Y := by
    exact Nat.floor_le hY0
  have hsecond : (classicalA2BSecondShift N tau : ℝ) ≤ Y ^ 2 := by
    exact Nat.floor_le (sq_nonneg Y)
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hYcube : (N : ℝ) ^ tau * Y * Y ^ 2 = (N : ℝ) ^
      (tau + 3 * classicalA2BExponent tau) := by
    dsimp only [Y, classicalA2BScale]
    have hsquare : ((N : ℝ) ^ classicalA2BExponent tau) ^ 2 =
        (N : ℝ) ^ (classicalA2BExponent tau * 2) := by
      calc
        ((N : ℝ) ^ classicalA2BExponent tau) ^ 2 =
            ((N : ℝ) ^ classicalA2BExponent tau) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = (N : ℝ) ^ (classicalA2BExponent tau * 2) :=
          (Real.rpow_mul hNPos.le _ _).symm
    rw [hsquare, ← Real.rpow_add hNPos, ← Real.rpow_add hNPos]
    congr 1
    ring
  have hexp : tau + 3 * classicalA2BExponent tau ≤ 4 := by
    unfold classicalA2BExponent
    linarith
  have hpow : (N : ℝ) ^ (tau + 3 * classicalA2BExponent tau) ≤
      (N : ℝ) ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hexp
  have hnum : (N : ℝ) ^ tau * classicalA2BFirstShift N tau *
      classicalA2BSecondShift N tau ≤ (N : ℝ) ^ (4 : ℝ) := by
    calc
      (N : ℝ) ^ tau * classicalA2BFirstShift N tau *
          classicalA2BSecondShift N tau ≤ (N : ℝ) ^ tau * Y * Y ^ 2 := by
        gcongr
      _ = (N : ℝ) ^ (tau + 3 * classicalA2BExponent tau) := hYcube
      _ ≤ (N : ℝ) ^ (4 : ℝ) := hpow
  have hdenPos : 0 < ((N : ℝ) + 1) ^ 4 := by positivity
  rw [div_le_one hdenPos]
  exact hnum.trans (by
    calc
      (N : ℝ) ^ (4 : ℝ) = (N : ℝ) ^ (4 : ℕ) :=
        Real.rpow_natCast _ 4
      _ ≤ ((N : ℝ) + 1) ^ 4 :=
        pow_le_pow_left₀ (show (0 : ℝ) ≤ N by positivity)
          (show (N : ℝ) ≤ N + 1 by linarith) 4)

#print axioms half_le_natFloor
#print axioms base_sq_div_classicalA2BScale
#print axioms classicalA2B_height_scale_identity
#print axioms classicalA2B_shift_sum_le
#print axioms classicalA2B_curvature_small

end

end GafniTao
