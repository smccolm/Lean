import GafniTao.ClassicalA3BOuter

/-!
# Integer scale selection for the classical `A³B` construction

For `25/8 ≤ τ ≤ 5`, set `Y=N^((5-τ)/15)` and take the three literal
integer shifts `⌊Y⌋`, `⌊Y²⌋`, and `⌊Y⁴⌋`.  The floor choices preserve both
endpoint room and the small-curvature hypothesis.
-/

namespace GafniTao

noncomputable section

noncomputable def classicalA3BExponent (tau : ℝ) : ℝ := (5 - tau) / 15

noncomputable def classicalA3BScale (N : ℕ) (tau : ℝ) : ℝ :=
  (N : ℝ) ^ classicalA3BExponent tau

noncomputable def classicalA3BFirstShift (N : ℕ) (tau : ℝ) : ℕ :=
  Nat.floor (classicalA3BScale N tau)

noncomputable def classicalA3BSecondShift (N : ℕ) (tau : ℝ) : ℕ :=
  Nat.floor (classicalA3BScale N tau ^ 2)

noncomputable def classicalA3BThirdShift (N : ℕ) (tau : ℝ) : ℕ :=
  Nat.floor (classicalA3BScale N tau ^ 4)

theorem classicalA3BExponent_nonneg {tau : ℝ} (htau : tau ≤ 5) :
    0 ≤ classicalA3BExponent tau := by
  unfold classicalA3BExponent
  linarith

theorem classicalA3BExponent_le_eighth {tau : ℝ} (htau : 25 / 8 ≤ tau) :
    classicalA3BExponent tau ≤ 1 / 8 := by
  unfold classicalA3BExponent
  norm_num at htau ⊢
  linarith

theorem classicalA3BScale_pos {N : ℕ} {tau : ℝ} (hN : 0 < N) :
    0 < classicalA3BScale N tau := by
  unfold classicalA3BScale
  exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem classicalA3BScale_one_le
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    1 ≤ classicalA3BScale N tau := by
  unfold classicalA3BScale
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  simpa using Real.one_le_rpow hNR (classicalA3BExponent_nonneg htau)

theorem classicalA3BFirstShift_pos
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    0 < classicalA3BFirstShift N tau := by
  unfold classicalA3BFirstShift
  exact Nat.floor_pos.mpr (classicalA3BScale_one_le hN htau)

theorem classicalA3BSecondShift_pos
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    0 < classicalA3BSecondShift N tau := by
  unfold classicalA3BSecondShift
  apply Nat.floor_pos.mpr
  have hY := classicalA3BScale_one_le hN htau
  nlinarith

theorem classicalA3BThirdShift_pos
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    0 < classicalA3BThirdShift N tau := by
  unfold classicalA3BThirdShift
  apply Nat.floor_pos.mpr
  have hY := classicalA3BScale_one_le hN htau
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hY 4
  norm_num at hp
  exact hp

theorem half_le_natFloor_A3 {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hfloorPos : 1 ≤ Nat.floor x := Nat.floor_pos.mpr hx
  by_cases hxTwo : x ≤ 2
  · have hfloorReal : (1 : ℝ) ≤ Nat.floor x := by exact_mod_cast hfloorPos
    linarith
  · have hlt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith

theorem classicalA3BScale_half_le_firstShift
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    classicalA3BScale N tau / 2 ≤ classicalA3BFirstShift N tau := by
  unfold classicalA3BFirstShift
  exact half_le_natFloor_A3 (classicalA3BScale_one_le hN htau)

theorem classicalA3BScale_sq_half_le_secondShift
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    classicalA3BScale N tau ^ 2 / 2 ≤ classicalA3BSecondShift N tau := by
  unfold classicalA3BSecondShift
  apply half_le_natFloor_A3
  have hY := classicalA3BScale_one_le hN htau
  nlinarith

theorem classicalA3BScale_fourth_half_le_thirdShift
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    classicalA3BScale N tau ^ 4 / 2 ≤ classicalA3BThirdShift N tau := by
  unfold classicalA3BThirdShift
  apply half_le_natFloor_A3
  have hY := classicalA3BScale_one_le hN htau
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hY 4
  norm_num at hp
  exact hp

theorem classicalA3BScale_fourth_le_sqrt
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : 25 / 8 ≤ tau) :
    classicalA3BScale N tau ^ 4 ≤ Real.sqrt (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hExp := classicalA3BExponent_le_eighth htau
  have hfourExp : 4 * classicalA3BExponent tau ≤ 1 / 2 := by linarith
  unfold classicalA3BScale
  calc
    ((N : ℝ) ^ classicalA3BExponent tau) ^ 4 =
        (N : ℝ) ^ (classicalA3BExponent tau * 4) := by
      calc
        _ = ((N : ℝ) ^ classicalA3BExponent tau) ^ (4 : ℝ) :=
          (Real.rpow_natCast _ 4).symm
        _ = _ := (Real.rpow_mul (zero_le_one.trans hNR) _ _).symm
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNR (by simpa [mul_comm] using hfourExp)
    _ = Real.sqrt (N : ℝ) := (Real.sqrt_eq_rpow (N : ℝ)).symm

theorem classicalA3B_shift_sum_le
    {N : ℕ} {tau : ℝ} (hN : 1024 ≤ N) (htau : 25 / 8 ≤ tau)
    (htauHigh : tau ≤ 5) :
    classicalA3BFirstShift N tau + classicalA3BSecondShift N tau +
      classicalA3BThirdShift N tau ≤ N := by
  let Y := classicalA3BScale N tau
  have hNOne : 1 ≤ N := by omega
  have hYone : 1 ≤ Y := classicalA3BScale_one_le hNOne htauHigh
  have hYnonneg : 0 ≤ Y := zero_le_one.trans hYone
  have hY4 := classicalA3BScale_fourth_le_sqrt hNOne htau
  have hY_Y4 : Y ≤ Y ^ 4 := by nlinarith [sq_nonneg (Y - 1), sq_nonneg (Y ^ 2)]
  have hY2_Y4 : Y ^ 2 ≤ Y ^ 4 := by nlinarith [sq_nonneg (Y ^ 2 - 1)]
  have h1 : (classicalA3BFirstShift N tau : ℝ) ≤ Real.sqrt (N : ℝ) :=
    (Nat.floor_le hYnonneg).trans (hY_Y4.trans hY4)
  have h2 : (classicalA3BSecondShift N tau : ℝ) ≤ Real.sqrt (N : ℝ) :=
    (Nat.floor_le (sq_nonneg Y)).trans (hY2_Y4.trans hY4)
  have h3 : (classicalA3BThirdShift N tau : ℝ) ≤ Real.sqrt (N : ℝ) :=
    (Nat.floor_le (by positivity)).trans hY4
  have hNR : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrtSq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)
  have hsqrtLower : 3 ≤ Real.sqrt (N : ℝ) := by
    have : (9 : ℝ) ≤ N := by linarith
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hthree : 3 * Real.sqrt (N : ℝ) ≤ N := by
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  exact_mod_cast (show
    (classicalA3BFirstShift N tau : ℝ) +
      classicalA3BSecondShift N tau + classicalA3BThirdShift N tau ≤ N by
        linarith)

theorem classicalA3B_first_admissible
    {N : ℕ} {tau : ℝ} (hN : 1024 ≤ N) (htau : 25 / 8 ≤ tau)
    (htauHigh : tau ≤ 5) : classicalA3BFirstShift N tau ≤ N := by
  have := classicalA3B_shift_sum_le hN htau htauHigh
  omega

theorem classicalA3B_third_admissible
    {N : ℕ} {tau : ℝ} (hN : 1024 ≤ N) (htau : 25 / 8 ≤ tau)
    (htauHigh : tau ≤ 5) :
    classicalA3BThirdShift N tau ≤
      N - (classicalA3BFirstShift N tau - 1) -
        (classicalA3BSecondShift N tau - 1) := by
  have := classicalA3B_shift_sum_le hN htau htauHigh
  omega

theorem classicalA3B_height_scale_identity
    {N : ℕ} {tau : ℝ} (hN : 0 < N) :
    (N : ℝ) ^ tau * classicalA3BScale N tau ^ 7 / (N : ℝ) ^ 5 =
      1 / classicalA3BScale N tau ^ 8 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold classicalA3BScale classicalA3BExponent
  have h7 : ((N : ℝ) ^ ((5 - tau) / 15)) ^ 7 =
      (N : ℝ) ^ (((5 - tau) / 15) * 7) := by
    calc
      _ = ((N : ℝ) ^ ((5 - tau) / 15)) ^ (7 : ℝ) :=
        (Real.rpow_natCast _ 7).symm
      _ = _ := (Real.rpow_mul hNR.le _ _).symm
  have h8 : ((N : ℝ) ^ ((5 - tau) / 15)) ^ 8 =
      (N : ℝ) ^ (((5 - tau) / 15) * 8) := by
    calc
      _ = ((N : ℝ) ^ ((5 - tau) / 15)) ^ (8 : ℝ) :=
        (Real.rpow_natCast _ 8).symm
      _ = _ := (Real.rpow_mul hNR.le _ _).symm
  rw [h7, h8, ← Real.rpow_natCast, ← Real.rpow_add hNR,
    ← Real.rpow_sub hNR, one_div, ← Real.rpow_neg hNR.le]
  congr 1
  ring

theorem classicalA3B_curvature_small
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    (N : ℝ) ^ tau * (classicalA3BFirstShift N tau : ℝ) *
      (classicalA3BSecondShift N tau : ℝ) *
      (classicalA3BThirdShift N tau : ℝ) / ((N : ℝ) + 1) ^ 5 ≤ 1 := by
  let Y := classicalA3BScale N tau
  have hNPos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hYone : 1 ≤ Y := classicalA3BScale_one_le hN htau
  have h1 : (classicalA3BFirstShift N tau : ℝ) ≤ Y :=
    Nat.floor_le (zero_le_one.trans hYone)
  have h2 : (classicalA3BSecondShift N tau : ℝ) ≤ Y ^ 2 :=
    Nat.floor_le (sq_nonneg Y)
  have h3 : (classicalA3BThirdShift N tau : ℝ) ≤ Y ^ 4 :=
    Nat.floor_le (by positivity)
  have hid := classicalA3B_height_scale_identity (tau := tau) hNPos
  have hnum :
      (N : ℝ) ^ tau * (classicalA3BFirstShift N tau : ℝ) *
          (classicalA3BSecondShift N tau : ℝ) *
          (classicalA3BThirdShift N tau : ℝ) ≤ (N : ℝ) ^ 5 := by
    calc
      _ ≤ (N : ℝ) ^ tau * Y * Y ^ 2 * Y ^ 4 := by gcongr
      _ = (N : ℝ) ^ tau * Y ^ 7 := by ring
      _ ≤ (N : ℝ) ^ 5 := by
        rw [div_eq_iff (by positivity : (N : ℝ) ^ 5 ≠ 0)] at hid
        have hinv : 1 / Y ^ 8 ≤ 1 := by
          rw [div_le_one (by positivity)]
          have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hYone 8
          simpa using hp
        calc
          (N : ℝ) ^ tau * Y ^ 7 = 1 / Y ^ 8 * (N : ℝ) ^ 5 := by
            simpa only [Y] using hid
          _ ≤ 1 * (N : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_right hinv (by positivity)
          _ = (N : ℝ) ^ 5 := one_mul _
  rw [div_le_one (by positivity)]
  exact hnum.trans (pow_le_pow_left₀ (by positivity) (by linarith) 5)

theorem base_sq_div_classicalA3BScale
    {N : ℕ} {tau : ℝ} (hN : 0 < N) :
    (N : ℝ) ^ 2 / classicalA3BScale N tau =
      (N : ℝ) ^ ((tau + 25) / 15) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold classicalA3BScale classicalA3BExponent
  rw [← Real.rpow_natCast, ← Real.rpow_sub hNR]
  congr 1
  ring

#print axioms classicalA3B_shift_sum_le
#print axioms classicalA3B_height_scale_identity
#print axioms classicalA3B_curvature_small
#print axioms base_sq_div_classicalA3BScale

end

end GafniTao
