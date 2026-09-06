import GafniTao.ClassicalA3BChosen

/-!
# Optimization of the selected `A³B` scales

The exact finite outer sum is reduced to the common power
`N^((τ+25)/15)` after squaring.  All rounding losses are explicit.
-/

namespace GafniTao

noncomputable section

theorem classicalA3BSecondShift_sqrt_lower
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    classicalA3BScale N tau / 2 ≤
      Real.sqrt (classicalA3BSecondShift N tau : ℝ) := by
  let Y := classicalA3BScale N tau
  have hY := classicalA3BScale_one_le hN htau
  have hlower : Y ^ 2 / 2 ≤ (classicalA3BSecondShift N tau : ℝ) :=
    classicalA3BScale_sq_half_le_secondShift hN htau
  apply Real.le_sqrt_of_sq_le
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  nlinarith [sq_nonneg Y]

theorem classicalA3BThirdShift_sqrt_lower
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    classicalA3BScale N tau ^ 2 / 2 ≤
      Real.sqrt (classicalA3BThirdShift N tau : ℝ) := by
  let Y := classicalA3BScale N tau
  have hY := classicalA3BScale_one_le hN htau
  have hlower : Y ^ 4 / 2 ≤ (classicalA3BThirdShift N tau : ℝ) :=
    classicalA3BScale_fourth_half_le_thirdShift hN htau
  apply Real.le_sqrt_of_sq_le
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  nlinarith [sq_nonneg (Y ^ 2)]

theorem sqrt_sqrt_sqrt_inv_eighth {Y : ℝ} (hY : 0 < Y) :
    Real.sqrt (Real.sqrt (Real.sqrt (1 / Y ^ 8))) = 1 / Y := by
  have h1 : 0 ≤ 1 / Y := by positivity
  have h2 : 0 ≤ 1 / Y ^ 2 := by positivity
  have h4 : 0 ≤ 1 / Y ^ 4 := by positivity
  have hs1 : Real.sqrt (1 / Y ^ 8) = 1 / Y ^ 4 := by
    rw [show 1 / Y ^ 8 = (1 / Y ^ 4) ^ 2 by field_simp [hY.ne'],
      Real.sqrt_sq_eq_abs, abs_of_nonneg h4]
  have hs2 : Real.sqrt (1 / Y ^ 4) = 1 / Y ^ 2 := by
    rw [show 1 / Y ^ 4 = (1 / Y ^ 2) ^ 2 by field_simp [hY.ne'],
      Real.sqrt_sq_eq_abs, abs_of_nonneg h2]
  rw [hs1, hs2,
    show 1 / Y ^ 2 = (1 / Y) ^ 2 by field_simp [hY.ne'],
    Real.sqrt_sq_eq_abs, abs_of_nonneg h1]

theorem classicalA3B_selected_curvature_le
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) :
    (N : ℝ) ^ tau * (classicalA3BFirstShift N tau : ℝ) *
        (classicalA3BSecondShift N tau : ℝ) *
        (classicalA3BThirdShift N tau : ℝ) / ((N : ℝ) + 1) ^ 5 ≤
      1 / classicalA3BScale N tau ^ 8 := by
  let Y := classicalA3BScale N tau
  have hNPos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hYpos : 0 < Y := classicalA3BScale_pos hNPos
  have h1 : (classicalA3BFirstShift N tau : ℝ) ≤ Y :=
    Nat.floor_le hYpos.le
  have h2 : (classicalA3BSecondShift N tau : ℝ) ≤ Y ^ 2 :=
    Nat.floor_le (sq_nonneg Y)
  have h3 : (classicalA3BThirdShift N tau : ℝ) ≤ Y ^ 4 :=
    Nat.floor_le (by positivity)
  have hden : (N : ℝ) ^ 5 ≤ ((N : ℝ) + 1) ^ 5 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 5
  calc
    _ ≤ (N : ℝ) ^ tau * Y * Y ^ 2 * Y ^ 4 / ((N : ℝ) + 1) ^ 5 := by
      gcongr
    _ ≤ (N : ℝ) ^ tau * Y ^ 7 / (N : ℝ) ^ 5 := by
      rw [show (N : ℝ) ^ tau * Y * Y ^ 2 * Y ^ 4 =
        (N : ℝ) ^ tau * Y ^ 7 by ring]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 1 / Y ^ 8 := classicalA3B_height_scale_identity hNPos
    _ = 1 / classicalA3BScale N tau ^ 8 := by rfl

theorem classicalA3B_selected_nested_curvature_le
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) :
    Real.sqrt (Real.sqrt (Real.sqrt
      ((N : ℝ) ^ tau * (classicalA3BFirstShift N tau : ℝ) *
        (classicalA3BSecondShift N tau : ℝ) *
        (classicalA3BThirdShift N tau : ℝ) / ((N : ℝ) + 1) ^ 5))) ≤
      1 / classicalA3BScale N tau := by
  have hNPos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hYpos := classicalA3BScale_pos (tau := tau) hNPos
  calc
    _ ≤ Real.sqrt (Real.sqrt (Real.sqrt
        (1 / classicalA3BScale N tau ^ 8))) := by
      apply Real.sqrt_le_sqrt
      apply Real.sqrt_le_sqrt
      exact Real.sqrt_le_sqrt (classicalA3B_selected_curvature_le hN)
    _ = 1 / classicalA3BScale N tau :=
      sqrt_sqrt_sqrt_inv_eighth hYpos

theorem classicalA3B_outer_first_term_le
    {N L : ℕ} {tau : ℝ} (hN : 1 ≤ N) (hL : L ≤ N) (htau : tau ≤ 5) :
    (classicalA3BFirstShift N tau : ℝ) *
        Real.sqrt (2 * (L : ℝ) ^ 2 / classicalA3BSecondShift N tau) ≤
      2 * (N : ℝ) := by
  let Y := classicalA3BScale N tau
  let H₁ := classicalA3BFirstShift N tau
  let H₂ := classicalA3BSecondShift N tau
  have hYpos : 0 < Y := classicalA3BScale_pos
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hH₁ : (H₁ : ℝ) ≤ Y := Nat.floor_le hYpos.le
  have hH₂pos : 0 < H₂ := classicalA3BSecondShift_pos hN htau
  have hH₂R : (0 : ℝ) < H₂ := by exact_mod_cast hH₂pos
  have hH₂lower : Y ^ 2 / 2 ≤ (H₂ : ℝ) :=
    classicalA3BScale_sq_half_le_secondShift hN htau
  have hroot : Real.sqrt (2 * (L : ℝ) ^ 2 / H₂) ≤ 2 * N / Y := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [div_pow]
      field_simp [hYpos.ne', hH₂R.ne']
      have hLR : (L : ℝ) ≤ N := by exact_mod_cast hL
      have hLsq : (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (L : ℝ), sq_nonneg (N : ℝ)]
      have hYsq : Y ^ 2 ≤ 2 * (H₂ : ℝ) := by linarith
      have hprod : (L : ℝ) ^ 2 * Y ^ 2 ≤
          2 * (H₂ : ℝ) * (N : ℝ) ^ 2 := by
        calc
          (L : ℝ) ^ 2 * Y ^ 2 ≤ (N : ℝ) ^ 2 * Y ^ 2 := by gcongr
          _ ≤ (N : ℝ) ^ 2 * (2 * (H₂ : ℝ)) := by gcongr
          _ = 2 * (H₂ : ℝ) * (N : ℝ) ^ 2 := by ring
      nlinarith
  calc
    (H₁ : ℝ) * Real.sqrt (2 * (L : ℝ) ^ 2 / H₂) ≤
        Y * (2 * (N : ℝ) / Y) := by gcongr
    _ = 2 * (N : ℝ) := by field_simp [hYpos.ne']

theorem classicalA3B_outer_second_term_le
    {N L : ℕ} {tau : ℝ} (hN : 1 ≤ N) (hL : L ≤ N) (htau : tau ≤ 5) :
    (classicalA3BFirstShift N tau : ℝ) *
        Real.sqrt (8 * (L : ℝ) ^ 2 /
          Real.sqrt (classicalA3BThirdShift N tau : ℝ)) ≤
      4 * (N : ℝ) := by
  let Y := classicalA3BScale N tau
  let H₁ := classicalA3BFirstShift N tau
  let H₃ := classicalA3BThirdShift N tau
  have hYpos : 0 < Y := classicalA3BScale_pos
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hH₁ : (H₁ : ℝ) ≤ Y := Nat.floor_le hYpos.le
  have hsH₃ : Y ^ 2 / 2 ≤ Real.sqrt (H₃ : ℝ) :=
    classicalA3BThirdShift_sqrt_lower hN htau
  have hsH₃pos : 0 < Real.sqrt (H₃ : ℝ) :=
    lt_of_lt_of_le (by positivity : 0 < Y ^ 2 / 2) hsH₃
  have hroot : Real.sqrt (8 * (L : ℝ) ^ 2 / Real.sqrt (H₃ : ℝ)) ≤
      4 * N / Y := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [div_pow]
      field_simp [hYpos.ne', hsH₃pos.ne']
      have hLR : (L : ℝ) ≤ N := by exact_mod_cast hL
      have hLsq : (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (L : ℝ), sq_nonneg (N : ℝ)]
      have hYsq : Y ^ 2 ≤ 2 * Real.sqrt (H₃ : ℝ) := by linarith
      have hprod : (L : ℝ) ^ 2 * Y ^ 2 ≤
          2 * Real.sqrt (H₃ : ℝ) * (N : ℝ) ^ 2 := by
        calc
          (L : ℝ) ^ 2 * Y ^ 2 ≤ (N : ℝ) ^ 2 * Y ^ 2 := by gcongr
          _ ≤ (N : ℝ) ^ 2 * (2 * Real.sqrt (H₃ : ℝ)) := by gcongr
          _ = 2 * Real.sqrt (H₃ : ℝ) * (N : ℝ) ^ 2 := by ring
      nlinarith
  calc
    (H₁ : ℝ) * Real.sqrt (8 * (L : ℝ) ^ 2 / Real.sqrt (H₃ : ℝ)) ≤
        Y * (4 * (N : ℝ) / Y) := by gcongr
    _ = 4 * (N : ℝ) := by field_simp [hYpos.ne']

theorem classicalA3B_outer_third_term_le
    {N L : ℕ} {tau : ℝ} (hN : 1 ≤ N) (hL : L ≤ N) :
    (classicalA3BFirstShift N tau : ℝ) *
        Real.sqrt (412 * (L : ℝ) ^ 2 * Real.sqrt (Real.sqrt
          ((N : ℝ) ^ tau * classicalA3BFirstShift N tau *
            classicalA3BSecondShift N tau * classicalA3BThirdShift N tau /
              ((N : ℝ) + 1) ^ 5))) ≤
      21 * (N : ℝ) := by
  let Y := classicalA3BScale N tau
  let H₁ := classicalA3BFirstShift N tau
  let q : ℝ := (N : ℝ) ^ tau * classicalA3BFirstShift N tau *
    classicalA3BSecondShift N tau * classicalA3BThirdShift N tau /
      ((N : ℝ) + 1) ^ 5
  have hYpos : 0 < Y := classicalA3BScale_pos
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hH₁ : (H₁ : ℝ) ≤ Y := Nat.floor_le hYpos.le
  have hnested : Real.sqrt (Real.sqrt (Real.sqrt q)) ≤ 1 / Y := by
    simpa only [q, Y] using classicalA3B_selected_nested_curvature_le hN
  have hLR : (L : ℝ) ≤ N := by exact_mod_cast hL
  have hroot : Real.sqrt (412 * (L : ℝ) ^ 2 * Real.sqrt (Real.sqrt q)) ≤
      21 * N / Y := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hnestedSq : Real.sqrt (Real.sqrt q) =
          (Real.sqrt (Real.sqrt (Real.sqrt q))) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      rw [hnestedSq, div_pow]
      field_simp [hYpos.ne']
      let w := Real.sqrt (Real.sqrt (Real.sqrt q))
      have hw0 : 0 ≤ w := by positivity
      have hwY : w * Y ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hnested hYpos.le
        field_simp [hYpos.ne'] at this
        simpa only [w] using this
      have hwY0 : 0 ≤ w * Y := mul_nonneg hw0 hYpos.le
      have hwYsq : (w * Y) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (w * Y)]
      have hLsq : (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (L : ℝ), sq_nonneg (N : ℝ)]
      have hcore : (L : ℝ) ^ 2 *
          (Real.sqrt (Real.sqrt (Real.sqrt q))) ^ 2 * Y ^ 2 ≤
          (N : ℝ) ^ 2 := by
        calc
          (L : ℝ) ^ 2 * (Real.sqrt (Real.sqrt (Real.sqrt q))) ^ 2 * Y ^ 2 =
              (L : ℝ) ^ 2 * (w * Y) ^ 2 := by dsimp only [w]; ring
          _ ≤ (N : ℝ) ^ 2 * 1 := by gcongr
          _ = (N : ℝ) ^ 2 := by ring
      nlinarith
  change (H₁ : ℝ) * Real.sqrt (412 * (L : ℝ) ^ 2 * Real.sqrt (Real.sqrt q)) ≤
    21 * (N : ℝ)
  calc
    (H₁ : ℝ) * Real.sqrt (412 * (L : ℝ) ^ 2 * Real.sqrt (Real.sqrt q)) ≤
        Y * (21 * (N : ℝ) / Y) := by gcongr
    _ = 21 * (N : ℝ) := by field_simp [hYpos.ne']

theorem classicalA3B_base_curvature_identity
    {N : ℕ} {tau : ℝ} (hN : 0 < N) :
    (N : ℝ) ^ tau / (N : ℝ) ^ 5 =
      1 / classicalA3BScale N tau ^ 15 := by
  let Y := classicalA3BScale N tau
  have hYpos : 0 < Y := classicalA3BScale_pos hN
  have hsource := classicalA3B_height_scale_identity (tau := tau) hN
  calc
    (N : ℝ) ^ tau / (N : ℝ) ^ 5 =
        ((N : ℝ) ^ tau * Y ^ 7 / (N : ℝ) ^ 5) / Y ^ 7 := by
      field_simp [hYpos.ne']
    _ = (1 / Y ^ 8) / Y ^ 7 := by
      rw [show (N : ℝ) ^ tau * Y ^ 7 / (N : ℝ) ^ 5 = 1 / Y ^ 8 by
        simpa only [Y] using hsource]
    _ = 1 / Y ^ 15 := by field_simp [hYpos.ne']
    _ = 1 / classicalA3BScale N tau ^ 15 := by rfl

theorem classicalA3B_phase_curvature_sq_lower
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) :
    1 / (32 * classicalA3BScale N tau ^ 15) ≤
      Real.sqrt
        ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 5) ^ 2 := by
  let Y := classicalA3BScale N tau
  have hNPos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hYpos : 0 < Y := classicalA3BScale_pos hNPos
  have hden : ((N : ℝ) + 1) ^ 5 ≤ 32 * (N : ℝ) ^ 5 := by
    have htwo : (N : ℝ) + 1 ≤ 2 * N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    calc
      ((N : ℝ) + 1) ^ 5 ≤ (2 * (N : ℝ)) ^ 5 :=
        pow_le_pow_left₀ (by positivity) htwo 5
      _ = 32 * (N : ℝ) ^ 5 := by ring
  have hquot :
      (N : ℝ) ^ tau / (32 * (N : ℝ) ^ 5) ≤
        (N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 5 := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  rw [Real.sq_sqrt (by positivity)]
  have hbase :
      (N : ℝ) ^ tau / (N : ℝ) ^ 5 = 1 / Y ^ 15 := by
    simpa only [Y] using classicalA3B_base_curvature_identity
      (tau := tau) hNPos
  calc
    1 / (32 * Y ^ 15) = (1 / Y ^ 15) / 32 := by ring
    _ = ((N : ℝ) ^ tau / (N : ℝ) ^ 5) / 32 := by rw [hbase]
    _ = (N : ℝ) ^ tau / (32 * (N : ℝ) ^ 5) := by ring
    _ ≤ (N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 5 := hquot

/-- The inverse-curvature and rounded-shift factor in the fourth outer
`A³B` contribution.  Squaring twice exposes the exact cancellation
`Y² · Y⁴ · Y⁻¹⁵` against the three powers of the first shift. -/
theorem classicalA3B_inverse_outer_factor_le
    {N : ℕ} {tau : ℝ} (hN : 1 ≤ N) (htau : tau ≤ 5) :
    Real.sqrt (1 /
        (Real.sqrt (classicalA3BThirdShift N tau : ℝ) *
          Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 5))) *
      (Real.sqrt (classicalA3BSecondShift N tau : ℝ) *
        Real.sqrt (2 * Real.sqrt
          (classicalA3BSecondShift N tau : ℝ))) /
      classicalA3BSecondShift N tau *
      ((classicalA3BFirstShift N tau : ℝ) *
        Real.sqrt (classicalA3BFirstShift N tau : ℝ) *
        Real.sqrt (2 * Real.sqrt
          (classicalA3BFirstShift N tau : ℝ))) ≤
      64 * classicalA3BScale N tau ^ 4 := by
  let Y := classicalA3BScale N tau
  let H₁ := classicalA3BFirstShift N tau
  let H₂ := classicalA3BSecondShift N tau
  let H₃ := classicalA3BThirdShift N tau
  let s₂ := Real.sqrt (H₂ : ℝ)
  let s₃ := Real.sqrt (H₃ : ℝ)
  let q := Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 5)
  let a := Real.sqrt (H₁ : ℝ)
  let b₂ := Real.sqrt (2 * s₂)
  let b₁ := Real.sqrt (2 * a)
  let z := Real.sqrt (1 / (s₃ * q))
  let D := z * (s₂ * b₂) / (H₂ : ℝ) * ((H₁ : ℝ) * a * b₁)
  have hNPos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hYone : 1 ≤ Y := classicalA3BScale_one_le hN htau
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hYone
  have hH₁pos : 0 < H₁ := classicalA3BFirstShift_pos hN htau
  have hH₂pos : 0 < H₂ := classicalA3BSecondShift_pos hN htau
  have hH₃pos : 0 < H₃ := classicalA3BThirdShift_pos hN htau
  have hH₂R : (0 : ℝ) < H₂ := by exact_mod_cast hH₂pos
  have hs₂pos : 0 < s₂ := by
    dsimp only [s₂]
    exact Real.sqrt_pos.2 hH₂R
  have hs₃pos : 0 < s₃ := by
    dsimp only [s₃]
    exact Real.sqrt_pos.2 (by exact_mod_cast hH₃pos)
  have hqpos : 0 < q := by dsimp only [q]; positivity
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hb₂0 : 0 ≤ b₂ := by dsimp only [b₂]; positivity
  have hb₁0 : 0 ≤ b₁ := by dsimp only [b₁]; positivity
  have hz0 : 0 ≤ z := by dsimp only [z]; positivity
  have hH₁Y : (H₁ : ℝ) ≤ Y := by
    dsimp only [H₁, classicalA3BFirstShift]
    exact Nat.floor_le hYpos.le
  have hH₂Y : Y ^ 2 / 2 ≤ (H₂ : ℝ) := by
    simpa only [H₂, Y] using
      classicalA3BScale_sq_half_le_secondShift hN htau
  have hH₃Y : Y ^ 4 / 2 ≤ (H₃ : ℝ) := by
    simpa only [H₃, Y] using
      classicalA3BScale_fourth_half_le_thirdShift hN htau
  have hs₂sq : s₂ ^ 2 = (H₂ : ℝ) := by
    dsimp only [s₂]
    exact Real.sq_sqrt hH₂R.le
  have hs₃sq : s₃ ^ 2 = (H₃ : ℝ) := by
    dsimp only [s₃]
    exact Real.sq_sqrt (by positivity)
  have hqsq : q ^ 2 = (N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 5 := by
    dsimp only [q]
    exact Real.sq_sqrt (by positivity)
  have hasq : a ^ 2 = (H₁ : ℝ) := by
    dsimp only [a]
    exact Real.sq_sqrt (by positivity)
  have hb₂sq : b₂ ^ 2 = 2 * s₂ := by
    dsimp only [b₂]
    exact Real.sq_sqrt (by positivity)
  have hb₁sq : b₁ ^ 2 = 2 * a := by
    dsimp only [b₁]
    exact Real.sq_sqrt (by positivity)
  have hzsq : z ^ 2 = 1 / (s₃ * q) := by
    dsimp only [z]
    exact Real.sq_sqrt (by positivity)
  have hqLower : 1 / (32 * Y ^ 15) ≤ q ^ 2 := by
    simpa only [q, Y] using classicalA3B_phase_curvature_sq_lower
      (tau := tau) hN
  have hDsq : D ^ 2 =
      (4 * (H₁ : ℝ) ^ 3 * a) / (s₂ * s₃ * q) := by
    dsimp only [D]
    rw [show (z * (s₂ * b₂) / (H₂ : ℝ) * ((H₁ : ℝ) * a * b₁)) ^ 2 =
      z ^ 2 * s₂ ^ 2 * b₂ ^ 2 / (H₂ : ℝ) ^ 2 *
        (H₁ : ℝ) ^ 2 * a ^ 2 * b₁ ^ 2 by ring,
      hzsq, hs₂sq, hb₂sq, hasq, hb₁sq]
    field_simp [hH₂R.ne', hs₂pos.ne', hs₃pos.ne', hqpos.ne']
    rw [hs₂sq]
    ring
  have hleftSq :
      (4 * (H₁ : ℝ) ^ 3 * a) ^ 2 ≤ 16 * Y ^ 7 := by
    rw [show (4 * (H₁ : ℝ) ^ 3 * a) ^ 2 =
      16 * (H₁ : ℝ) ^ 6 * a ^ 2 by ring, hasq]
    have hp : (H₁ : ℝ) ^ 7 ≤ Y ^ 7 :=
      pow_le_pow_left₀ (by positivity) hH₁Y 7
    nlinarith
  have hrightSq :
      16 * Y ^ 7 ≤ (4096 * Y ^ 8 * s₂ * s₃ * q) ^ 2 := by
    rw [show (4096 * Y ^ 8 * s₂ * s₃ * q) ^ 2 =
      4096 ^ 2 * Y ^ 16 * s₂ ^ 2 * s₃ ^ 2 * q ^ 2 by ring,
      hs₂sq, hs₃sq]
    calc
      16 * Y ^ 7 ≤ 4096 ^ 2 * Y ^ 16 * (Y ^ 2 / 2) *
          (Y ^ 4 / 2) * (1 / (32 * Y ^ 15)) := by
        field_simp [hYpos.ne']
        nlinarith [pow_pos hYpos 7]
      _ ≤ 4096 ^ 2 * Y ^ 16 * (H₂ : ℝ) * (H₃ : ℝ) * q ^ 2 := by
        gcongr
  have hlinear :
      4 * (H₁ : ℝ) ^ 3 * a ≤ 4096 * Y ^ 8 * s₂ * s₃ * q :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp
      (hleftSq.trans hrightSq)
  have hDsqBound : D ^ 2 ≤ (64 * Y ^ 4) ^ 2 := by
    rw [hDsq, div_le_iff₀ (mul_pos (mul_pos hs₂pos hs₃pos) hqpos)]
    simpa only [show (64 * Y ^ 4) ^ 2 = 4096 * Y ^ 8 by ring,
      mul_assoc] using hlinear
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hD : D ≤ 64 * Y ^ 4 :=
    (sq_le_sq₀ hD0 (by positivity)).mp hDsqBound
  simpa only [D, z, b₂, b₁, a, q, s₂, s₃, H₁, H₂, H₃, Y] using hD

theorem classicalA3B_outer_fourth_term_le
    {N L : ℕ} {tau : ℝ} (hN : 1 ≤ N) (hL : L ≤ N)
    (htauLow : 25 / 8 ≤ tau) (htauHigh : tau ≤ 5) :
    Real.sqrt (584 * (L : ℝ) * Real.sqrt (L : ℝ) /
        classicalA3BSecondShift N tau *
        Real.sqrt (1 /
          (Real.sqrt (classicalA3BThirdShift N tau : ℝ) *
            Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 5))) *
        (Real.sqrt (classicalA3BSecondShift N tau : ℝ) *
          Real.sqrt (2 * Real.sqrt
            (classicalA3BSecondShift N tau : ℝ)))) *
      (Real.sqrt (classicalA3BFirstShift N tau : ℝ) *
        Real.sqrt (Real.sqrt (classicalA3BFirstShift N tau : ℝ) *
          Real.sqrt (2 * Real.sqrt
            (classicalA3BFirstShift N tau : ℝ)))) ≤
      194 * (N : ℝ) := by
  let Y := classicalA3BScale N tau
  let H₁ := classicalA3BFirstShift N tau
  let H₂ := classicalA3BSecondShift N tau
  let H₃ := classicalA3BThirdShift N tau
  let s₂ := Real.sqrt (H₂ : ℝ)
  let s₃ := Real.sqrt (H₃ : ℝ)
  let q := Real.sqrt ((N : ℝ) ^ tau / ((N : ℝ) + 1) ^ 5)
  let a := Real.sqrt (H₁ : ℝ)
  let b₂ := Real.sqrt (2 * s₂)
  let b₁ := Real.sqrt (2 * a)
  let z := Real.sqrt (1 / (s₃ * q))
  let c := Real.sqrt (a * b₁)
  let D := z * (s₂ * b₂) / (H₂ : ℝ) * ((H₁ : ℝ) * a * b₁)
  let F := Real.sqrt (584 * (L : ℝ) * Real.sqrt (L : ℝ) /
      (H₂ : ℝ) * z * (s₂ * b₂)) * (a * c)
  have hH₁pos : 0 < H₁ := classicalA3BFirstShift_pos hN htauHigh
  have hH₂pos : 0 < H₂ := classicalA3BSecondShift_pos hN htauHigh
  have hH₃pos : 0 < H₃ := classicalA3BThirdShift_pos hN htauHigh
  have hasq : a ^ 2 = (H₁ : ℝ) := by
    dsimp only [a]
    exact Real.sq_sqrt (by positivity)
  have hcsq : c ^ 2 = a * b₁ := by
    dsimp only [c]
    exact Real.sq_sqrt (by positivity)
  have hinside : 0 ≤ 584 * (L : ℝ) * Real.sqrt (L : ℝ) /
      (H₂ : ℝ) * z * (s₂ * b₂) := by positivity
  have hFsq : F ^ 2 = 584 * (L : ℝ) * Real.sqrt (L : ℝ) * D := by
    dsimp only [F]
    rw [show (Real.sqrt (584 * (L : ℝ) * Real.sqrt (L : ℝ) /
          (H₂ : ℝ) * z * (s₂ * b₂)) * (a * c)) ^ 2 =
        Real.sqrt (584 * (L : ℝ) * Real.sqrt (L : ℝ) /
          (H₂ : ℝ) * z * (s₂ * b₂)) ^ 2 * a ^ 2 * c ^ 2 by ring,
      Real.sq_sqrt hinside, hasq, hcsq]
    dsimp only [D]
    ring
  have hD : D ≤ 64 * Y ^ 4 := by
    simpa only [D, z, b₂, b₁, a, q, s₂, s₃, H₁, H₂, H₃, Y] using
      classicalA3B_inverse_outer_factor_le (tau := tau) hN htauHigh
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hY4 : Y ^ 4 ≤ Real.sqrt (N : ℝ) := by
    simpa only [Y] using classicalA3BScale_fourth_le_sqrt hN htauLow
  have hDsqrt : D ≤ 64 * Real.sqrt (N : ℝ) :=
    hD.trans (mul_le_mul_of_nonneg_left hY4 (by norm_num))
  have hLR : (L : ℝ) ≤ N := by exact_mod_cast hL
  have hsqrtL : Real.sqrt (L : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt hLR
  have hsqrtN : Real.sqrt (N : ℝ) ^ 2 = N :=
    Real.sq_sqrt (by positivity)
  have hFsqBound : F ^ 2 ≤ 37376 * (N : ℝ) ^ 2 := by
    rw [hFsq]
    calc
      584 * (L : ℝ) * Real.sqrt (L : ℝ) * D ≤
          584 * (N : ℝ) * Real.sqrt (N : ℝ) *
            (64 * Real.sqrt (N : ℝ)) := by gcongr
      _ = 37376 * (N : ℝ) * Real.sqrt (N : ℝ) ^ 2 := by ring
      _ = 37376 * (N : ℝ) ^ 2 := by rw [hsqrtN]; ring
  have hFsqTarget : F ^ 2 ≤ (194 * (N : ℝ)) ^ 2 := by
    calc
      F ^ 2 ≤ 37376 * (N : ℝ) ^ 2 := hFsqBound
      _ ≤ (194 * (N : ℝ)) ^ 2 := by
        have hNsq : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
        nlinarith
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hF : F ≤ 194 * (N : ℝ) :=
    (sq_le_sq₀ hF0 (by positivity)).mp hFsqTarget
  simpa only [F, c, z, b₂, b₁, a, q, s₂, s₃, H₁, H₂, H₃, Y] using hF

theorem classicalA3B_outer_sum_le
    {N L : ℕ} {tau : ℝ} (hN : 1 ≤ N) (hL : L ≤ N)
    (htauLow : 25 / 8 ≤ tau) (htauHigh : tau ≤ 5) :
    logarithmicA3BOuterSumBound ((N : ℝ) ^ tau) ((N : ℝ) + 1)
        L (classicalA3BFirstShift N tau)
          (classicalA3BSecondShift N tau)
          (classicalA3BThirdShift N tau) ≤
      221 * (N : ℝ) := by
  have hfirst := classicalA3B_outer_first_term_le
    (tau := tau) hN hL htauHigh
  have hsecond := classicalA3B_outer_second_term_le
    (tau := tau) hN hL htauHigh
  have hthird := classicalA3B_outer_third_term_le
    (tau := tau) hN hL
  have hfourth := classicalA3B_outer_fourth_term_le
    (tau := tau) hN hL htauLow htauHigh
  unfold logarithmicA3BOuterSumBound
  linarith

theorem norm_pintz2023ExponentialBlock_sq_le_A3B_power
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauLow : 25 / 8 ≤ tau) (htauHigh : tau ≤ 5)
    (hlong : classicalA3BFirstShift N tau +
      classicalA3BSecondShift N tau + classicalA3BThirdShift N tau ≤ R - N) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ^ 2 ≤
      1772 * (N : ℝ) ^ ((tau + 25) / 15) := by
  let L := R - N
  let Y := classicalA3BScale N tau
  let H₁ := classicalA3BFirstShift N tau
  let H₂ := classicalA3BSecondShift N tau
  let H₃ := classicalA3BThirdShift N tau
  let S := logarithmicA3BOuterSumBound ((N : ℝ) ^ tau) ((N : ℝ) + 1)
    L H₁ H₂ H₃
  have hNOne : 1 ≤ N := by omega
  have hNPos : 0 < N := by omega
  have hL : L ≤ N := by dsimp only [L]; omega
  have hH₁pos : 0 < H₁ := by
    dsimp only [H₁]
    exact classicalA3BFirstShift_pos hNOne htauHigh
  have hH₁real : (0 : ℝ) < H₁ := by exact_mod_cast hH₁pos
  have hYpos : 0 < Y := by
    dsimp only [Y]
    exact classicalA3BScale_pos hNPos
  have hH₁lower : Y / 2 ≤ (H₁ : ℝ) := by
    simpa only [Y, H₁] using
      classicalA3BScale_half_le_firstShift hNOne htauHigh
  have hS : S ≤ 221 * (N : ℝ) := by
    dsimp only [S, L, H₁, H₂, H₃]
    exact classicalA3B_outer_sum_le hNOne hL htauLow htauHigh
  have hSnonneg : 0 ≤ S := by
    dsimp only [S, logarithmicA3BOuterSumBound]
    positivity
  have hLReal : (L : ℝ) ≤ N := by exact_mod_cast hL
  have hfactor : 2 * (L : ℝ) / (H₁ : ℝ) ≤ 4 * (N : ℝ) / Y := by
    rw [div_le_iff₀ hH₁real]
    calc
      2 * (L : ℝ) ≤ 2 * (N : ℝ) := by linarith
      _ = (4 * (N : ℝ) / Y) * (Y / 2) := by
        field_simp [hYpos.ne']
        norm_num
      _ ≤ (4 * (N : ℝ) / Y) * (H₁ : ℝ) := by gcongr
  have hbracket : (L : ℝ) + 2 * S ≤ 443 * (N : ℝ) := by linarith
  have hraw := norm_pintz2023ExponentialBlock_sq_le_A3B_selected
    hN hNR hR htauHigh hlong
  calc
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ^ 2 ≤
        (2 * (L : ℝ) / (H₁ : ℝ)) * ((L : ℝ) + 2 * S) := by
      simpa only [L, H₁, H₂, H₃, S, Nat.cast_add, Nat.cast_one] using hraw
    _ ≤ (4 * (N : ℝ) / Y) * (443 * (N : ℝ)) :=
      mul_le_mul hfactor hbracket (by positivity) (by positivity)
    _ = 1772 * ((N : ℝ) ^ 2 / Y) := by ring
    _ = 1772 * (N : ℝ) ^ ((tau + 25) / 15) := by
      rw [show (N : ℝ) ^ 2 / Y =
        (N : ℝ) ^ ((tau + 25) / 15) by
          exact base_sq_div_classicalA3BScale (tau := tau) hNPos]

theorem norm_pintz2023ExponentialBlock_le_A3B_power_of_long
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauLow : 25 / 8 ≤ tau) (htauHigh : tau ≤ 5)
    (hlong : classicalA3BFirstShift N tau +
      classicalA3BSecondShift N tau + classicalA3BThirdShift N tau ≤ R - N) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      43 * (N : ℝ) ^ ((tau + 25) / 30) := by
  have hNPos : (0 : ℝ) < N := by positivity
  have hsq := norm_pintz2023ExponentialBlock_sq_le_A3B_power
    hN hNR hR htauLow htauHigh hlong
  have hpowSq :
      ((N : ℝ) ^ ((tau + 25) / 30)) ^ 2 =
        (N : ℝ) ^ ((tau + 25) / 15) := by
    calc
      ((N : ℝ) ^ ((tau + 25) / 30)) ^ 2 =
          ((N : ℝ) ^ ((tau + 25) / 30)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (N : ℝ) ^ (((tau + 25) / 30) * 2) :=
        (Real.rpow_mul hNPos.le _ _).symm
      _ = (N : ℝ) ^ ((tau + 25) / 15) := by ring_nf
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ^ 2 ≤
        1772 * (N : ℝ) ^ ((tau + 25) / 15) := hsq
    _ ≤ 1849 * (N : ℝ) ^ ((tau + 25) / 15) := by
      have hp : 0 ≤ (N : ℝ) ^ ((tau + 25) / 15) := by positivity
      nlinarith
    _ = (43 * (N : ℝ) ^ ((tau + 25) / 30)) ^ 2 := by
      rw [mul_pow, hpowSq]
      norm_num

theorem norm_pintz2023ExponentialBlock_le_A3B_power_of_short
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R)
    (htauLow : 25 / 8 ≤ tau) (htauHigh : tau ≤ 5)
    (hshort : R - N < classicalA3BFirstShift N tau +
      classicalA3BSecondShift N tau + classicalA3BThirdShift N tau) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      43 * (N : ℝ) ^ ((tau + 25) / 30) := by
  let Y := classicalA3BScale N tau
  have hNOne : 1 ≤ N := by omega
  have hYone : 1 ≤ Y := classicalA3BScale_one_le hNOne htauHigh
  have hY4 := classicalA3BScale_fourth_le_sqrt hNOne htauLow
  have hY_Y4 : Y ≤ Y ^ 4 := by
    nlinarith [sq_nonneg (Y - 1), sq_nonneg (Y ^ 2)]
  have hY2_Y4 : Y ^ 2 ≤ Y ^ 4 := by
    nlinarith [sq_nonneg (Y ^ 2 - 1)]
  have hfirst : (classicalA3BFirstShift N tau : ℝ) ≤ Real.sqrt (N : ℝ) :=
    (Nat.floor_le (zero_le_one.trans hYone)).trans (hY_Y4.trans hY4)
  have hsecond : (classicalA3BSecondShift N tau : ℝ) ≤ Real.sqrt (N : ℝ) :=
    (Nat.floor_le (sq_nonneg Y)).trans (hY2_Y4.trans hY4)
  have hthird : (classicalA3BThirdShift N tau : ℝ) ≤ Real.sqrt (N : ℝ) :=
    (Nat.floor_le (by positivity)).trans hY4
  have hshortNat : R - N ≤ classicalA3BFirstShift N tau +
      classicalA3BSecondShift N tau + classicalA3BThirdShift N tau := by omega
  have hshortReal : ((R - N : ℕ) : ℝ) ≤
      (classicalA3BFirstShift N tau : ℝ) +
        classicalA3BSecondShift N tau + classicalA3BThirdShift N tau := by
    exact_mod_cast hshortNat
  have hexp : (1 / 2 : ℝ) ≤ (tau + 25) / 30 := by linarith
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hNOne
  have hpow : Real.sqrt (N : ℝ) ≤
      (N : ℝ) ^ ((tau + 25) / 30) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hNReal hexp
  have hlen := norm_pintz2023ExponentialBlock_le_length
    hNR.le ((N : ℝ) ^ tau)
  calc
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        ((R - N : ℕ) : ℝ) := hlen
    _ ≤ (classicalA3BFirstShift N tau : ℝ) +
        classicalA3BSecondShift N tau + classicalA3BThirdShift N tau := hshortReal
    _ ≤ 3 * Real.sqrt (N : ℝ) := by linarith
    _ ≤ 43 * (N : ℝ) ^ ((tau + 25) / 30) := by
      have hp : 0 ≤ (N : ℝ) ^ ((tau + 25) / 30) := by positivity
      nlinarith

/-- The classical `A³B` estimate for the logarithmic phase in the range used
to close Pintz's near-one density argument.  Both the exact finite long-block
chain and its endpoint-short complement are included. -/
theorem norm_pintz2023ExponentialBlock_le_A3B_power
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauLow : 25 / 8 ≤ tau) (htauHigh : tau ≤ 7 / 2) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      43 * (N : ℝ) ^ ((tau + 25) / 30) := by
  have htauFive : tau ≤ 5 := by linarith
  by_cases hlong : classicalA3BFirstShift N tau +
      classicalA3BSecondShift N tau + classicalA3BThirdShift N tau ≤ R - N
  · exact norm_pintz2023ExponentialBlock_le_A3B_power_of_long
      hN hNR hR htauLow htauFive hlong
  · exact norm_pintz2023ExponentialBlock_le_A3B_power_of_short
      hN hNR htauLow htauFive (by omega)

#print axioms classicalA3B_selected_nested_curvature_le
#print axioms classicalA3B_outer_first_term_le
#print axioms classicalA3B_outer_second_term_le
#print axioms classicalA3B_outer_third_term_le
#print axioms classicalA3B_phase_curvature_sq_lower
#print axioms classicalA3B_inverse_outer_factor_le
#print axioms classicalA3B_outer_fourth_term_le
#print axioms classicalA3B_outer_sum_le
#print axioms norm_pintz2023ExponentialBlock_sq_le_A3B_power
#print axioms norm_pintz2023ExponentialBlock_le_A3B_power

end

end GafniTao
