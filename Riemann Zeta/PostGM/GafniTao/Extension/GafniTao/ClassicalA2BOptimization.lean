import GafniTao.ClassicalA2BChosen

/-!
# Optimization of the selected `A²B` scales

The estimates here reduce the exact finite outer bound to the common square
power `N^((tau+10)/7)`.  No asymptotic notation is used in this layer.
-/

namespace GafniTao

noncomputable section

theorem classicalA2BSecondShift_sqrt_lower
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 4) :
    classicalA2BScale N tau / 2 ≤
      Real.sqrt (classicalA2BSecondShift N tau : ℝ) := by
  let Y := classicalA2BScale N tau
  have hY : 1 ≤ Y := classicalA2BScale_one_le hN htau
  have hlower : Y ^ 2 / 2 ≤ (classicalA2BSecondShift N tau : ℝ) :=
    classicalA2BScale_sq_half_le_secondShift hN htau
  apply Real.le_sqrt_of_sq_le
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  nlinarith [sq_nonneg Y]

theorem classicalA2B_inner_first_le
    {N L : ℕ} {tau : ℝ} (hN : 1 ≤ N) (hL : L ≤ N)
    (htau : tau ≤ 4) :
    (classicalA2BFirstShift N tau : ℝ) *
        (2 * (L : ℝ) /
          Real.sqrt (classicalA2BSecondShift N tau : ℝ)) ≤
      4 * (N : ℝ) := by
  let Y := classicalA2BScale N tau
  let H₁ := classicalA2BFirstShift N tau
  let H₂ := classicalA2BSecondShift N tau
  have hY : 1 ≤ Y := classicalA2BScale_one_le hN htau
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hH₁ : (H₁ : ℝ) ≤ Y := by
    dsimp only [H₁, classicalA2BFirstShift]
    exact Nat.floor_le (zero_le_one.trans hY)
  have hsH₂ : Y / 2 ≤ Real.sqrt (H₂ : ℝ) := by
    dsimp only [H₂]
    exact classicalA2BSecondShift_sqrt_lower hN htau
  have hsH₂pos : 0 < Real.sqrt (H₂ : ℝ) :=
    lt_of_lt_of_le (by positivity : 0 < Y / 2) hsH₂
  have hLReal : (L : ℝ) ≤ N := by exact_mod_cast hL
  calc
    (H₁ : ℝ) * (2 * (L : ℝ) / Real.sqrt (H₂ : ℝ)) ≤
        Y * (2 * (N : ℝ) / (Y / 2)) := by
      gcongr
    _ = 4 * (N : ℝ) := by field_simp [hYpos.ne']; ring

theorem nested_sqrt_inv_fourth_power {Y : ℝ} (hY : 0 < Y) :
    Real.sqrt (Real.sqrt (1 / Y ^ 4)) = 1 / Y := by
  have hY2 : 0 ≤ 1 / Y ^ 2 := by positivity
  have hY1 : 0 ≤ 1 / Y := by positivity
  have hinner : Real.sqrt (1 / Y ^ 4) = 1 / Y ^ 2 := by
    rw [show 1 / Y ^ 4 = (1 / Y ^ 2) ^ 2 by field_simp [hY.ne'],
      Real.sqrt_sq_eq_abs, abs_of_nonneg hY2]
  rw [hinner, show 1 / Y ^ 2 = (1 / Y) ^ 2 by field_simp [hY.ne'],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hY1]

theorem classicalA2B_nested_curvature_le
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) :
    Real.sqrt (Real.sqrt
        ((N : ℝ) ^ tau * classicalA2BFirstShift N tau *
          classicalA2BSecondShift N tau / ((N : ℝ) + 1) ^ 4)) ≤
      1 / classicalA2BScale N tau := by
  let Y := classicalA2BScale N tau
  let H₁ := classicalA2BFirstShift N tau
  let H₂ := classicalA2BSecondShift N tau
  have hNPos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hNPos
  have hYpos : 0 < Y := classicalA2BScale_pos hNPos
  have hH₁ : (H₁ : ℝ) ≤ Y := by
    dsimp only [H₁, classicalA2BFirstShift]
    exact Nat.floor_le hYpos.le
  have hH₂ : (H₂ : ℝ) ≤ Y ^ 2 := by
    dsimp only [H₂, classicalA2BSecondShift]
    exact Nat.floor_le (sq_nonneg Y)
  have hden : (N : ℝ) ^ 4 ≤ ((N : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ hNReal.le (by linarith) 4
  have hq :
      (N : ℝ) ^ tau * (H₁ : ℝ) * (H₂ : ℝ) /
          ((N : ℝ) + 1) ^ 4 ≤ 1 / Y ^ 4 := by
    calc
      (N : ℝ) ^ tau * (H₁ : ℝ) * (H₂ : ℝ) /
          ((N : ℝ) + 1) ^ 4 ≤
        (N : ℝ) ^ tau * Y * Y ^ 2 / ((N : ℝ) + 1) ^ 4 := by
          gcongr
      _ ≤ (N : ℝ) ^ tau * Y ^ 3 / (N : ℝ) ^ 4 := by
        have hnum : 0 ≤ (N : ℝ) ^ tau * Y ^ 3 := by positivity
        rw [show (N : ℝ) ^ tau * Y * Y ^ 2 =
          (N : ℝ) ^ tau * Y ^ 3 by ring]
        exact div_le_div_of_nonneg_left hnum (by positivity) hden
      _ = 1 / Y ^ 4 := by
        dsimp only [Y]
        exact classicalA2B_height_scale_identity hNPos
  calc
    Real.sqrt (Real.sqrt
        ((N : ℝ) ^ tau * classicalA2BFirstShift N tau *
          classicalA2BSecondShift N tau / ((N : ℝ) + 1) ^ 4)) ≤
      Real.sqrt (Real.sqrt (1 / Y ^ 4)) := by
        apply Real.sqrt_le_sqrt
        exact Real.sqrt_le_sqrt (by simpa only [H₁, H₂] using hq)
    _ = 1 / Y := nested_sqrt_inv_fourth_power hYpos
    _ = 1 / classicalA2BScale N tau := by rfl

theorem classicalA2B_inner_second_le
    {N L : ℕ} {tau : ℝ} (hN : 1 ≤ N) (hL : L ≤ N) :
    (classicalA2BFirstShift N tau : ℝ) *
        (44 * (L : ℝ) * Real.sqrt (Real.sqrt
          ((N : ℝ) ^ tau * classicalA2BFirstShift N tau *
            classicalA2BSecondShift N tau / ((N : ℝ) + 1) ^ 4))) ≤
      44 * (N : ℝ) := by
  let Y := classicalA2BScale N tau
  have hYpos : 0 < Y := classicalA2BScale_pos
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hH₁ : (classicalA2BFirstShift N tau : ℝ) ≤ Y := by
    unfold classicalA2BFirstShift
    exact Nat.floor_le hYpos.le
  have hcurv := classicalA2B_nested_curvature_le (tau := tau) hN
  have hLReal : (L : ℝ) ≤ N := by exact_mod_cast hL
  calc
    (classicalA2BFirstShift N tau : ℝ) *
        (44 * (L : ℝ) * Real.sqrt (Real.sqrt
          ((N : ℝ) ^ tau * classicalA2BFirstShift N tau *
            classicalA2BSecondShift N tau / ((N : ℝ) + 1) ^ 4))) ≤
      Y * (44 * (N : ℝ) * (1 / Y)) := by gcongr
    _ = 44 * (N : ℝ) := by field_simp [hYpos.ne']

theorem classicalA2B_base_curvature_identity
    {N : ℕ} {tau : ℝ} (hN : 0 < N) :
    (N : ℝ) ^ tau / (N : ℝ) ^ 4 =
      1 / classicalA2BScale N tau ^ 7 := by
  have hYpos := classicalA2BScale_pos (tau := tau) hN
  have hsource := classicalA2B_height_scale_identity (tau := tau) hN
  calc
    (N : ℝ) ^ tau / (N : ℝ) ^ 4 =
        ((N : ℝ) ^ tau * classicalA2BScale N tau ^ 3 /
          (N : ℝ) ^ 4) / classicalA2BScale N tau ^ 3 := by
      field_simp [hYpos.ne']
    _ = (1 / classicalA2BScale N tau ^ 4) /
        classicalA2BScale N tau ^ 3 := by rw [hsource]
    _ = 1 / classicalA2BScale N tau ^ 7 := by
      field_simp [hYpos.ne']

theorem classicalA2B_phase_curvature_sq_lower
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) :
    1 / (16 * classicalA2BScale N tau ^ 7) ≤
      Real.sqrt
        ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4) ^ 2 := by
  let Y := classicalA2BScale N tau
  have hNPos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hNPos
  have hYpos : 0 < Y := classicalA2BScale_pos hNPos
  have hden : ((N : ℝ) + 1) ^ 4 ≤ 16 * (N : ℝ) ^ 4 := by
    have htwo : (N : ℝ) + 1 ≤ 2 * N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    calc
      ((N : ℝ) + 1) ^ 4 ≤ (2 * (N : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) htwo 4
      _ = 16 * (N : ℝ) ^ 4 := by ring
  have hquot :
      (N : ℝ) ^ tau / (16 * (N : ℝ) ^ 4) ≤
        (N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4 := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hsqrt :
      Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4) ^ 2 =
        (N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4 :=
    Real.sq_sqrt (by positivity)
  rw [hsqrt]
  have hbase :
      (N : ℝ) ^ tau / (N : ℝ) ^ 4 = 1 / Y ^ 7 := by
    simpa only [Y] using classicalA2B_base_curvature_identity
      (tau := tau) hNPos
  calc
    1 / (16 * Y ^ 7) = (1 / Y ^ 7) / 16 := by ring
    _ = ((N : ℝ) ^ tau / (N : ℝ) ^ 4) / 16 := by rw [hbase]
    _ = (N : ℝ) ^ tau / (16 * (N : ℝ) ^ 4) := by ring
    _ ≤ (N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4 := hquot

/-- The inverse-curvature radical in the third `A²B` contribution.  The
proof squares twice and uses the literal floor inequalities; this is the
point at which the powers `Y²/2` and `Y⁻⁷/16` cancel. -/
theorem classicalA2B_inverse_curvature_factor_le
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 4) :
    Real.sqrt (1 /
        (Real.sqrt (classicalA2BSecondShift N tau : ℝ) *
          Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4))) *
      (Real.sqrt (classicalA2BFirstShift N tau : ℝ) *
        Real.sqrt (2 * Real.sqrt
          (classicalA2BFirstShift N tau : ℝ))) ≤
      4 * classicalA2BScale N tau ^ 2 := by
  let Y := classicalA2BScale N tau
  let H₁ := classicalA2BFirstShift N tau
  let H₂ := classicalA2BSecondShift N tau
  let s := Real.sqrt (H₂ : ℝ)
  let q := Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4)
  let a := Real.sqrt (H₁ : ℝ)
  let z := Real.sqrt (1 / (s * q))
  have hNPos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hYone : 1 ≤ Y := classicalA2BScale_one_le hN htau
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hYone
  have hH₁pos : 0 < H₁ := classicalA2BFirstShift_pos hN htau
  have hH₂pos : 0 < H₂ := classicalA2BSecondShift_pos hN htau
  have hspos : 0 < s := by
    dsimp only [s]
    exact Real.sqrt_pos.2 (by exact_mod_cast hH₂pos)
  have hqpos : 0 < q := by dsimp only [q]; positivity
  have hapos : 0 < a := by
    dsimp only [a]
    exact Real.sqrt_pos.2 (by exact_mod_cast hH₁pos)
  have hznonneg : 0 ≤ z := by dsimp only [z]; positivity
  have hH₁Y : (H₁ : ℝ) ≤ Y := by
    dsimp only [H₁, classicalA2BFirstShift]
    exact Nat.floor_le hYpos.le
  have hH₂Y : Y ^ 2 / 2 ≤ (H₂ : ℝ) := by
    dsimp only [H₂, Y]
    exact classicalA2BScale_sq_half_le_secondShift hN htau
  have hssq : s ^ 2 = (H₂ : ℝ) := by
    dsimp only [s]
    exact Real.sq_sqrt (by positivity)
  have hqsq : q ^ 2 =
      (N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4 := by
    dsimp only [q]
    exact Real.sq_sqrt (by positivity)
  have hqLower : 1 / (16 * Y ^ 7) ≤ q ^ 2 := by
    simpa only [q, Y] using classicalA2B_phase_curvature_sq_lower
      (tau := tau) hN
  have hasq : a ^ 2 = (H₁ : ℝ) := by
    dsimp only [a]
    exact Real.sq_sqrt (by positivity)
  have hzsq : z ^ 2 = 1 / (s * q) := by
    dsimp only [z]
    exact Real.sq_sqrt (by positivity)
  have hleftSq :
      (2 * (H₁ : ℝ) * a) ^ 2 ≤ 4 * Y ^ 3 := by
    rw [show (2 * (H₁ : ℝ) * a) ^ 2 =
      4 * (H₁ : ℝ) ^ 2 * a ^ 2 by ring, hasq]
    have hcube : (H₁ : ℝ) ^ 3 ≤ Y ^ 3 :=
      pow_le_pow_left₀ (by positivity) hH₁Y 3
    nlinarith
  have hrightSq :
      4 * Y ^ 3 ≤ (16 * Y ^ 4 * s * q) ^ 2 := by
    rw [show (16 * Y ^ 4 * s * q) ^ 2 =
      256 * Y ^ 8 * s ^ 2 * q ^ 2 by ring, hssq]
    calc
      4 * Y ^ 3 ≤
          256 * Y ^ 8 * (Y ^ 2 / 2) * (1 / (16 * Y ^ 7)) := by
        field_simp [hYpos.ne']
        nlinarith [sq_nonneg Y]
      _ ≤ 256 * Y ^ 8 * (H₂ : ℝ) * q ^ 2 := by gcongr
  have hlinear : 2 * (H₁ : ℝ) * a ≤ 16 * Y ^ 4 * s * q :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp (hleftSq.trans hrightSq)
  have hfactorSq :
      (z * (a * Real.sqrt (2 * a))) ^ 2 ≤ (4 * Y ^ 2) ^ 2 := by
    rw [show (z * (a * Real.sqrt (2 * a))) ^ 2 =
      z ^ 2 * a ^ 2 * Real.sqrt (2 * a) ^ 2 by ring,
      hzsq, hasq, Real.sq_sqrt (by positivity)]
    rw [show 1 / (s * q) * (H₁ : ℝ) * (2 * a) =
      (2 * (H₁ : ℝ) * a) / (s * q) by field_simp [hspos.ne', hqpos.ne']]
    rw [div_le_iff₀ (mul_pos hspos hqpos)]
    calc
      2 * (H₁ : ℝ) * a ≤ 16 * Y ^ 4 * s * q := hlinear
      _ = (4 * Y ^ 2) ^ 2 * (s * q) := by ring
  have hfactor : z * (a * Real.sqrt (2 * a)) ≤ 4 * Y ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hfactorSq
  simpa only [z, a, s, q, H₁, H₂, Y] using hfactor

theorem classicalA2B_inner_third_le
    {N L : ℕ} {tau : ℝ} (hN : 1 ≤ N) (hL : L ≤ N)
    (htauLow : 9 / 4 ≤ tau) (htauHigh : tau ≤ 4) :
    62 * Real.sqrt (L : ℝ) *
        Real.sqrt (1 /
          (Real.sqrt (classicalA2BSecondShift N tau : ℝ) *
            Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4))) *
        (Real.sqrt (classicalA2BFirstShift N tau : ℝ) *
          Real.sqrt (2 * Real.sqrt
            (classicalA2BFirstShift N tau : ℝ))) ≤
      248 * (N : ℝ) := by
  let Y := classicalA2BScale N tau
  have hfactor := classicalA2B_inverse_curvature_factor_le
    (tau := tau) hN htauHigh
  have hsqrtL : Real.sqrt (L : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hL)
  have hYsq : Y ^ 2 ≤ Real.sqrt (N : ℝ) := by
    simpa only [Y] using classicalA2BScale_sq_le_sqrt hN htauLow
  have hsqrtSq : Real.sqrt (N : ℝ) ^ 2 = N :=
    Real.sq_sqrt (by positivity)
  let F := Real.sqrt (1 /
      (Real.sqrt (classicalA2BSecondShift N tau : ℝ) *
        Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4))) *
    (Real.sqrt (classicalA2BFirstShift N tau : ℝ) *
      Real.sqrt (2 * Real.sqrt
        (classicalA2BFirstShift N tau : ℝ)))
  have hFnonneg : 0 ≤ F := by dsimp only [F]; positivity
  have hF : F ≤ 4 * Y ^ 2 := by simpa only [F, Y] using hfactor
  calc
    62 * Real.sqrt (L : ℝ) *
        Real.sqrt (1 /
          (Real.sqrt (classicalA2BSecondShift N tau : ℝ) *
            Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4))) *
        (Real.sqrt (classicalA2BFirstShift N tau : ℝ) *
          Real.sqrt (2 * Real.sqrt
            (classicalA2BFirstShift N tau : ℝ))) ≤
      62 * Real.sqrt (N : ℝ) * F := by
        rw [show 62 * Real.sqrt (L : ℝ) *
            Real.sqrt (1 /
              (Real.sqrt (classicalA2BSecondShift N tau : ℝ) *
                Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 4))) *
            (Real.sqrt (classicalA2BFirstShift N tau : ℝ) *
              Real.sqrt (2 * Real.sqrt
                (classicalA2BFirstShift N tau : ℝ))) =
              (62 * Real.sqrt (L : ℝ)) * F by
                dsimp only [F]
                ring]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrtL
            (show (0 : ℝ) ≤ 62 by norm_num)) hFnonneg
    _ ≤ 62 * Real.sqrt (N : ℝ) * (4 * Y ^ 2) := by
      exact mul_le_mul_of_nonneg_left hF (by positivity)
    _ ≤ 62 * Real.sqrt (N : ℝ) *
        (4 * Real.sqrt (N : ℝ)) := by
      gcongr
    _ = 248 * (N : ℝ) := by
      have hm : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N := by
        nlinarith
      rw [show 62 * Real.sqrt (N : ℝ) * (4 * Real.sqrt (N : ℝ)) =
        248 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) by ring, hm]

theorem classicalA2B_inner_sum_le
    {N L : ℕ} {tau : ℝ} (hN : 1 ≤ N) (hL : L ≤ N)
    (htauLow : 9 / 4 ≤ tau) (htauHigh : tau ≤ 4) :
    logarithmicA2BInnerSumBound ((N : ℝ) ^ tau) ((N : ℝ) + 1)
        L (classicalA2BFirstShift N tau)
          (classicalA2BSecondShift N tau) ≤
      296 * (N : ℝ) := by
  have hfirst := classicalA2B_inner_first_le hN hL htauHigh
  have hsecond := classicalA2B_inner_second_le (tau := tau) hN hL
  have hthird := classicalA2B_inner_third_le hN hL htauLow htauHigh
  unfold logarithmicA2BInnerSumBound
  linarith

theorem norm_pintz2023ExponentialBlock_sq_le_A2B_power
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauLow : 9 / 4 ≤ tau) (htauHigh : tau ≤ 4)
    (hlong : classicalA2BFirstShift N tau +
      classicalA2BSecondShift N tau ≤ R - N) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ^ 2 ≤
      2372 * (N : ℝ) ^ ((tau + 10) / 7) := by
  let L := R - N
  let Y := classicalA2BScale N tau
  let H₁ := classicalA2BFirstShift N tau
  let H₂ := classicalA2BSecondShift N tau
  let S := logarithmicA2BInnerSumBound ((N : ℝ) ^ tau) ((N : ℝ) + 1)
    L H₁ H₂
  have hNOne : 1 ≤ N := by omega
  have hNPos : 0 < N := by omega
  have hL : L ≤ N := by dsimp only [L]; omega
  have hH₁pos : 0 < H₁ := by
    dsimp only [H₁]
    exact classicalA2BFirstShift_pos hNOne htauHigh
  have hH₁real : (0 : ℝ) < H₁ := by exact_mod_cast hH₁pos
  have hYpos : 0 < Y := by
    dsimp only [Y]
    exact classicalA2BScale_pos hNPos
  have hH₁lower : Y / 2 ≤ (H₁ : ℝ) := by
    dsimp only [Y, H₁]
    exact classicalA2BScale_half_le_firstShift hNOne htauHigh
  have hS : S ≤ 296 * (N : ℝ) := by
    dsimp only [S, L, H₁, H₂]
    exact classicalA2B_inner_sum_le hNOne hL htauLow htauHigh
  have hSnonneg : 0 ≤ S := by
    dsimp only [S]
    exact logarithmicA2BInnerSumBound_nonneg _ _ _ _ _
  have hLReal : (L : ℝ) ≤ N := by exact_mod_cast hL
  have hfactor : 2 * (L : ℝ) / (H₁ : ℝ) ≤ 4 * (N : ℝ) / Y := by
    rw [div_le_iff₀ hH₁real]
    calc
      2 * (L : ℝ) ≤ 2 * (N : ℝ) := by linarith
      _ = (4 * (N : ℝ) / Y) * (Y / 2) := by
        field_simp [hYpos.ne']
        norm_num
      _ ≤ (4 * (N : ℝ) / Y) * (H₁ : ℝ) := by gcongr
  have hbracket : (L : ℝ) + 2 * S ≤ 593 * (N : ℝ) := by
    linarith
  have hraw := norm_pintz2023ExponentialBlock_sq_le_A2B_selected
    hN hNR hR htauHigh hlong
  calc
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ^ 2 ≤
        (2 * (L : ℝ) / (H₁ : ℝ)) * ((L : ℝ) + 2 * S) := by
      simpa only [L, H₁, H₂, S, Nat.cast_add, Nat.cast_one] using hraw
    _ ≤ (4 * (N : ℝ) / Y) * (593 * (N : ℝ)) := by
      exact mul_le_mul hfactor hbracket (by positivity)
        (by positivity)
    _ = 2372 * ((N : ℝ) ^ 2 / Y) := by ring
    _ = 2372 * (N : ℝ) ^ ((tau + 10) / 7) := by
      rw [show (N : ℝ) ^ 2 / Y =
        (N : ℝ) ^ ((tau + 10) / 7) by
          simpa only [Y] using base_sq_div_classicalA2BScale
            (tau := tau) hNPos]

theorem norm_pintz2023ExponentialBlock_le_A2B_power_of_long
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauLow : 9 / 4 ≤ tau) (htauHigh : tau ≤ 4)
    (hlong : classicalA2BFirstShift N tau +
      classicalA2BSecondShift N tau ≤ R - N) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      49 * (N : ℝ) ^ ((tau + 10) / 14) := by
  have hNPos : (0 : ℝ) < N := by positivity
  have hsq := norm_pintz2023ExponentialBlock_sq_le_A2B_power
    hN hNR hR htauLow htauHigh hlong
  have hpowSq :
      ((N : ℝ) ^ ((tau + 10) / 14)) ^ 2 =
        (N : ℝ) ^ ((tau + 10) / 7) := by
    calc
      ((N : ℝ) ^ ((tau + 10) / 14)) ^ 2 =
          ((N : ℝ) ^ ((tau + 10) / 14)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (N : ℝ) ^ (((tau + 10) / 14) * 2) :=
        (Real.rpow_mul hNPos.le _ _).symm
      _ = (N : ℝ) ^ ((tau + 10) / 7) := by ring_nf
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ^ 2 ≤
        2372 * (N : ℝ) ^ ((tau + 10) / 7) := hsq
    _ ≤ 2401 * (N : ℝ) ^ ((tau + 10) / 7) := by
      have hp : 0 ≤ (N : ℝ) ^ ((tau + 10) / 7) := by positivity
      nlinarith
    _ = (49 * (N : ℝ) ^ ((tau + 10) / 14)) ^ 2 := by
      rw [mul_pow, hpowSq]
      norm_num

theorem norm_pintz2023ExponentialBlock_le_A2B_power_of_short
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R)
    (htauLow : 9 / 4 ≤ tau)
    (hshort : R - N < classicalA2BFirstShift N tau +
      classicalA2BSecondShift N tau) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      49 * (N : ℝ) ^ ((tau + 10) / 14) := by
  have hNOne : 1 ≤ N := by omega
  have hlen := norm_pintz2023ExponentialBlock_le_length
    hNR.le ((N : ℝ) ^ tau)
  have hfirst := classicalA2BFirstShift_cast_le_sqrt hNOne htauLow
  have hsecond := classicalA2BSecondShift_cast_le_sqrt hNOne htauLow
  have hshortNat : R - N ≤ classicalA2BFirstShift N tau +
      classicalA2BSecondShift N tau := by omega
  have hshortReal : ((R - N : ℕ) : ℝ) ≤
      (classicalA2BFirstShift N tau : ℝ) +
        classicalA2BSecondShift N tau := by exact_mod_cast hshortNat
  have hexp : (1 / 2 : ℝ) ≤ (tau + 10) / 14 := by linarith
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hNOne
  have hpow : Real.sqrt (N : ℝ) ≤
      (N : ℝ) ^ ((tau + 10) / 14) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hNReal hexp
  calc
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        ((R - N : ℕ) : ℝ) := hlen
    _ ≤ (classicalA2BFirstShift N tau : ℝ) +
        classicalA2BSecondShift N tau := hshortReal
    _ ≤ 2 * Real.sqrt (N : ℝ) := by linarith
    _ ≤ 49 * (N : ℝ) ^ ((tau + 10) / 14) := by
      have hp : 0 ≤ (N : ℝ) ^ ((tau + 10) / 14) := by positivity
      nlinarith

/-- The classical exponent pair `(1/14, 11/14)` for Pintz's logarithmic
phase, with an explicit constant and all floor/end-point losses retained. -/
theorem norm_pintz2023ExponentialBlock_le_A2B_power
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauLow : 9 / 4 ≤ tau) (htauHigh : tau ≤ 4) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      49 * (N : ℝ) ^ ((tau + 10) / 14) := by
  by_cases hlong : classicalA2BFirstShift N tau +
      classicalA2BSecondShift N tau ≤ R - N
  · exact norm_pintz2023ExponentialBlock_le_A2B_power_of_long
      hN hNR hR htauLow htauHigh hlong
  · exact norm_pintz2023ExponentialBlock_le_A2B_power_of_short
      hN hNR htauLow (by omega)

#print axioms classicalA2B_inner_first_le
#print axioms classicalA2B_nested_curvature_le
#print axioms classicalA2B_inner_second_le
#print axioms classicalA2B_inverse_curvature_factor_le
#print axioms classicalA2B_inner_sum_le
#print axioms norm_pintz2023ExponentialBlock_sq_le_A2B_power
#print axioms norm_pintz2023ExponentialBlock_le_A2B_power

end

end GafniTao
