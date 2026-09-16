import Tao2026.SylvesterSchurPrimeCountTailSixThousand

/-!
# Prime-counted Sylvester--Schur tail from length 2200

An adaptive near/far split closes the next bridge.  For `2200 ≤ H < 3000`
the transition is `16H`; for `3000 ≤ H < 6000` it is `20H`.  The exact
bounded estimate `4 * π(m) ≤ m + 12` controls the low-prime exponent in both
near ranges, while `π(H) ≤ H/4` supplies the two far baselines.
-/

namespace Tao2026

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-- Exact bounded prime-count envelope for the adaptive bridge. -/
theorem four_mul_primeCounting_le_add_twelve_of_bounded
    {m : ℕ} (hm : 60 ≤ m) (hmUpper : m < 400) :
    4 * m.primeCounting ≤ m + 12 := by
  have hqLower : 15 ≤ m / 4 := by omega
  have hqUpper : m / 4 < 100 := by omega
  let qFin : Fin 100 := ⟨m / 4, hqUpper⟩
  have hfinite : ∀ q : Fin 100, 15 ≤ q.1 →
      (4 * q.1 + 3).primeCounting ≤ q.1 + 3 := by
    decide
  have hmLe : m ≤ 4 * (m / 4) + 3 := by omega
  have hpi : m.primeCounting ≤ m / 4 + 3 :=
    (Nat.monotone_primeCounting hmLe).trans (by
      simpa [qFin] using hfinite qFin (by simpa [qFin] using hqLower))
  omega

/-- From `H=2200`, `log H ≤ 19 sqrt(H)/100`. -/
theorem log_nat_le_nineteen_sqrt_div_hundred_of_twoThousandTwoHundred
    {H : ℕ} (hH : 2_200 ≤ H) :
    Real.log H ≤ 19 * Real.sqrt H / 100 := by
  let X : ℝ := H
  let Y : ℝ := 2_116
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hYPos : 0 < Y := by positivity
  have hYX : Y ≤ X := by
    dsimp [Y, X]
    exact_mod_cast (show 2_116 ≤ H by omega)
  have hpowLower : (2 : ℝ) ^ 11 ≤ Y := by norm_num [Y]
  have hpowUpper : Y ≤ (2 : ℝ) ^ 12 := by norm_num [Y]
  have hlogLower : 11 * Real.log 2 ≤ Real.log Y := by
    calc
      11 * Real.log 2 = Real.log ((2 : ℝ) ^ 11) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log Y := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hYPos) hpowLower
  have hlogUpper : Real.log Y ≤ 12 * Real.log 2 := by
    calc
      Real.log Y ≤ Real.log ((2 : ℝ) ^ 12) :=
        Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hYPos)
          (Set.mem_Ioi.mpr (by positivity)) hpowUpper
      _ = 12 * Real.log 2 := by
        rw [Real.log_pow]
        norm_num
  have hTwoLog : (2 : ℝ) ≤ Real.log Y := by
    nlinarith [Real.log_two_gt_d9]
  have hExp : Real.exp 2 ≤ Y := by
    rw [← Real.exp_log hYPos]
    exact Real.exp_le_exp.mpr hTwoLog
  have hanti : Real.log X / Real.sqrt X ≤
      Real.log Y / Real.sqrt Y :=
    Real.log_div_sqrt_antitoneOn hExp (hExp.trans hYX) hYX
  have hSqrtY : Real.sqrt Y = 46 := by
    have hsq : Y = (46 : ℝ) ^ 2 := by norm_num [Y]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hbase : Real.log Y / Real.sqrt Y < (19 / 100 : ℝ) := by
    rw [hSqrtY, div_lt_iff₀ (by positivity)]
    nlinarith [Real.log_two_lt_d9]
  have hratio : Real.log X / Real.sqrt X < (19 / 100 : ℝ) :=
    hanti.trans_lt hbase
  have hSqrtPos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXPos
  rw [div_lt_iff₀ hSqrtPos] at hratio
  dsimp [X] at hratio ⊢
  nlinarith

/-- From `H=3000`, `log H ≤ 16 sqrt(H)/100`. -/
theorem log_nat_le_sixteen_sqrt_div_hundred_of_threeThousand
    {H : ℕ} (hH : 3_000 ≤ H) :
    Real.log H ≤ 16 * Real.sqrt H / 100 := by
  let X : ℝ := H
  let Y : ℝ := 2_916
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hYPos : 0 < Y := by positivity
  have hYX : Y ≤ X := by
    dsimp [Y, X]
    exact_mod_cast (show 2_916 ≤ H by omega)
  have hpowLower : (2 : ℝ) ^ 11 ≤ Y := by norm_num [Y]
  have hpowUpper : Y ≤ (2 : ℝ) ^ 12 := by norm_num [Y]
  have hlogLower : 11 * Real.log 2 ≤ Real.log Y := by
    calc
      11 * Real.log 2 = Real.log ((2 : ℝ) ^ 11) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log Y := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hYPos) hpowLower
  have hlogUpper : Real.log Y ≤ 12 * Real.log 2 := by
    calc
      Real.log Y ≤ Real.log ((2 : ℝ) ^ 12) :=
        Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hYPos)
          (Set.mem_Ioi.mpr (by positivity)) hpowUpper
      _ = 12 * Real.log 2 := by
        rw [Real.log_pow]
        norm_num
  have hTwoLog : (2 : ℝ) ≤ Real.log Y := by
    nlinarith [Real.log_two_gt_d9]
  have hExp : Real.exp 2 ≤ Y := by
    rw [← Real.exp_log hYPos]
    exact Real.exp_le_exp.mpr hTwoLog
  have hanti : Real.log X / Real.sqrt X ≤
      Real.log Y / Real.sqrt Y :=
    Real.log_div_sqrt_antitoneOn hExp (hExp.trans hYX) hYX
  have hSqrtY : Real.sqrt Y = 54 := by
    have hsq : Y = (54 : ℝ) ^ 2 := by norm_num [Y]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hbase : Real.log Y / Real.sqrt Y < (16 / 100 : ℝ) := by
    rw [hSqrtY, div_lt_iff₀ (by positivity)]
    nlinarith [Real.log_two_lt_d9]
  have hratio : Real.log X / Real.sqrt X < (16 / 100 : ℝ) :=
    hanti.trans_lt hbase
  have hSqrtPos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXPos
  rw [div_lt_iff₀ hSqrtPos] at hratio
  dsimp [X] at hratio ⊢
  nlinarith

/-- The prime-count logarithmic baseline at `16H`. -/
theorem primeCountTail_primeCounting_log_baseline_sixteen
    {H : ℕ} (hH : 2_200 ≤ H) (hHUpper : H < 3_000) :
    (H.primeCounting : ℝ) * Real.log (16 * H) <
      (H : ℝ) * Real.log 16 := by
  let X : ℝ := H
  let P : ℝ := H.primeCounting
  let L : ℝ := Real.log X
  let C : ℝ := Real.log 16
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hCPos : 0 < C := by dsimp [C]; positivity
  have hpiNat : H.primeCounting ≤ H / 4 :=
    primeCounting_le_div_four_of_twoThousandTwoHundred_le hH
  have hpiFour : 4 * P ≤ X := by
    dsimp [P, X]
    exact_mod_cast (show 4 * H.primeCounting ≤ H by omega)
  have hHCube : H < 16 ^ 3 := by norm_num; omega
  have hlogCube : Real.log X < Real.log ((16 : ℝ) ^ 3) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr hXPos
    · exact Set.mem_Ioi.mpr (by positivity)
    · dsimp [X]
      exact_mod_cast hHCube
  have hLC : L < 3 * C := by
    dsimp [L, C] at hlogCube ⊢
    rw [Real.log_pow] at hlogCube
    norm_num at hlogCube ⊢
    exact hlogCube
  have hsumPos : 0 ≤ L + C := by positivity
  have hmul : (4 * P) * (L + C) ≤ X * (L + C) :=
    mul_le_mul_of_nonneg_right hpiFour hsumPos
  have htargetMul : X * (L + C) < X * (4 * C) :=
    mul_lt_mul_of_pos_left (by nlinarith) hXPos
  have hmain : P * (L + C) < X * C := by nlinarith
  have hlogMul : Real.log (16 * H) = L + C := by
    dsimp [L, C, X]
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hXPos.ne']
    ring
  rw [hlogMul]
  exact hmain

/-- The prime-count logarithmic baseline at `20H`. -/
theorem primeCountTail_primeCounting_log_baseline_twenty
    {H : ℕ} (hH : 3_000 ≤ H) (hHUpper : H < 6_000) :
    (H.primeCounting : ℝ) * Real.log (20 * H) <
      (H : ℝ) * Real.log 20 := by
  let X : ℝ := H
  let P : ℝ := H.primeCounting
  let L : ℝ := Real.log X
  let C : ℝ := Real.log 20
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hCPos : 0 < C := by dsimp [C]; positivity
  have hpiNat : H.primeCounting ≤ H / 4 :=
    primeCounting_le_div_four_of_twoThousandTwoHundred_le (by omega)
  have hpiFour : 4 * P ≤ X := by
    dsimp [P, X]
    exact_mod_cast (show 4 * H.primeCounting ≤ H by omega)
  have hHCube : H < 20 ^ 3 := by norm_num; omega
  have hlogCube : Real.log X < Real.log ((20 : ℝ) ^ 3) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr hXPos
    · exact Set.mem_Ioi.mpr (by positivity)
    · dsimp [X]
      exact_mod_cast hHCube
  have hLC : L < 3 * C := by
    dsimp [L, C] at hlogCube ⊢
    rw [Real.log_pow] at hlogCube
    norm_num at hlogCube ⊢
    exact hlogCube
  have hsumPos : 0 ≤ L + C := by positivity
  have hmul : (4 * P) * (L + C) ≤ X * (L + C) :=
    mul_le_mul_of_nonneg_right hpiFour hsumPos
  have htargetMul : X * (L + C) < X * (4 * C) :=
    mul_lt_mul_of_pos_left (by nlinarith) hXPos
  have hmain : P * (L + C) < X * C := by nlinarith
  have hlogMul : Real.log (20 * H) = L + C := by
    dsimp [L, C, X]
    rw [Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) hXPos.ne']
    ring
  rw [hlogMul]
  exact hmain

/-- A logarithmic prime-count baseline implies the binomial-growth baseline. -/
theorem primeCountTail_choose_growth_baseline_of_log
    {C H : ℕ} (hC : 1 ≤ C) (hH : 1 ≤ H)
    (hlog : (H.primeCounting : ℝ) * Real.log (C * H) <
      (H : ℝ) * Real.log C) :
    (C * H) ^ (H + 1).primesBelow.card < (C * H).choose H := by
  have hbasePos : 0 < C * H := by positivity
  have hlogMul :
      (H.primeCounting : ℝ) * Real.log (C * H) +
          (H : ℝ) * Real.log H <
        (H : ℝ) * Real.log (C * H) := by
    have hsplit : Real.log (C * H) = Real.log C + Real.log H := by
      rw [Real.log_mul (by exact_mod_cast (show C ≠ 0 by omega) : (C : ℝ) ≠ 0)
        (by exact_mod_cast (show H ≠ 0 by omega) : (H : ℝ) ≠ 0)]
    rw [hsplit] at hlog ⊢
    nlinarith
  rw [card_primesBelow_succ_eq_primeCounting]
  have hpowers :
      (C * H) ^ H.primeCounting * H ^ H < (C * H) ^ H :=
    nat_pow_mul_pow_lt_pow_of_log_lt hbasePos (by omega) hbasePos (by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      exact hlogMul)
  have hlower : (C * H) ^ H ≤ (C * H).choose H * H ^ H :=
    pow_le_choose_mul_pow (by nlinarith)
  exact Nat.lt_of_mul_lt_mul_right (hpowers.trans_le hlower)

/-- Far-branch binomial growth from the `16H` baseline. -/
theorem primeCountTail_choose_growth_of_sixteen_le
    {n H : ℕ} (hH : 2_200 ≤ H) (hHUpper : H < 3_000)
    (hn : 16 * H ≤ n) :
    n ^ (H + 1).primesBelow.card < n.choose H := by
  apply choose_growth_of_le (m := 16 * H)
  · omega
  · rw [card_primesBelow_succ_eq_primeCounting]
    exact primeCounting_lt_self (by omega)
  · exact hn
  · exact primeCountTail_choose_growth_baseline_of_log (by omega) (by omega)
      (primeCountTail_primeCounting_log_baseline_sixteen hH hHUpper)

/-- Far-branch binomial growth from the `20H` baseline. -/
theorem primeCountTail_choose_growth_of_twenty_le
    {n H : ℕ} (hH : 3_000 ≤ H) (hHUpper : H < 6_000)
    (hn : 20 * H ≤ n) :
    n ^ (H + 1).primesBelow.card < n.choose H := by
  apply choose_growth_of_le (m := 20 * H)
  · omega
  · rw [card_primesBelow_succ_eq_primeCounting]
    exact primeCounting_lt_self (by omega)
  · exact hn
  · exact primeCountTail_choose_growth_baseline_of_log (by omega) (by omega)
      (primeCountTail_primeCounting_log_baseline_twenty hH hHUpper)

/-- The prime-counted near gap through `16H` on the lower bridge. -/
theorem primeCountTailSixteen_near_gap
    {n H : ℕ} (hH : 2_200 ≤ H) (hHUpper : H < 3_000)
    (hhalf : 2 * H ≤ n) (hn : n ≤ 16 * H) :
    H * (n ^ n.sqrt.primeCounting * 3 ^ (H + 1)) < 4 ^ H := by
  let X : ℝ := H
  let Z : ℝ := n
  let S : ℝ := Real.sqrt X
  let L : ℝ := Real.log X
  let P : ℝ := n.sqrt.primeCounting
  have hXPos : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < H)
  have hZPos : 0 < Z := by dsimp [Z]; exact_mod_cast (by omega : 0 < n)
  have hSSq : S * S = X := Real.mul_self_sqrt hXPos.le
  have hSGe : (46 : ℝ) ≤ S := by
    dsimp [S]
    apply Real.le_sqrt_of_sq_le
    dsimp [X]
    exact_mod_cast (show 46 ^ 2 ≤ H by norm_num; omega)
  have hSLe : S ≤ X / 46 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 46)]
    nlinarith
  have hLLe : L ≤ 19 * S / 100 := by
    simpa [L, S, X] using
      log_nat_le_nineteen_sqrt_div_hundred_of_twoThousandTwoHundred hH
  have hZLe : Z ≤ 16 * X := by dsimp [Z, X]; exact_mod_cast hn
  have hSqrtZ : Real.sqrt Z ≤ 4 * S := by
    calc
      Real.sqrt Z ≤ Real.sqrt (16 * X) := Real.sqrt_le_sqrt hZLe
      _ = 4 * S := by
        dsimp [S]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
  have hLogZ : Real.log Z ≤ L + 3 := by
    calc
      Real.log Z ≤ Real.log (16 * X) :=
        Real.strictMonoOn_log.monotoneOn hZPos
          (mul_pos (by norm_num) hXPos) hZLe
      _ = Real.log 16 + L := by
        dsimp [L]
        rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hXPos.ne']
      _ ≤ L + 3 := by
        have hlog16 : Real.log 16 = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
          norm_num
        rw [hlog16]
        nlinarith [Real.log_two_lt_d9]
  have hSqrtNatLower : 60 ≤ n.sqrt := by rw [Nat.le_sqrt]; nlinarith
  have hnUpper : n < 400 ^ 2 := by nlinarith
  have hSqrtNatUpper : n.sqrt < 400 := Nat.sqrt_lt'.mpr hnUpper
  have hpiNat : 4 * n.sqrt.primeCounting ≤ n.sqrt + 12 :=
    four_mul_primeCounting_le_add_twelve_of_bounded
      hSqrtNatLower hSqrtNatUpper
  have hpi : 4 * P ≤ (n.sqrt : ℝ) + 12 := by
    dsimp [P]
    exact_mod_cast hpiNat
  have hNatSqrt : (n.sqrt : ℝ) ≤ Real.sqrt Z := by
    simpa [Z] using (Real.nat_sqrt_le_real_sqrt (a := n))
  have hPLe : P ≤ S + 3 := by nlinarith
  have hsub : P * Real.log n ≤ (272 / 1000 : ℝ) * X := by
    calc
      P * Real.log n = P * Real.log Z := by rfl
      _ ≤ (S + 3) * (L + 3) := by
        exact mul_le_mul hPLe hLogZ (by positivity) (by positivity)
      _ ≤ (272 / 1000 : ℝ) * X := by
        have hSL : S * L ≤ 19 * X / 100 := by
          calc
            S * L ≤ S * (19 * S / 100) :=
              mul_le_mul_of_nonneg_left hLLe (Real.sqrt_nonneg X)
            _ = 19 * X / 100 := by rw [← hSSq]; ring
        have hconst : (9 : ℝ) ≤ X * (5 / 1000) := by
          have hcast : (2_200 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast hH
          nlinarith
        nlinarith
  have hlogHSmall : L ≤ (5 / 1000 : ℝ) * X := by
    calc
      L ≤ 19 * S / 100 := hLLe
      _ ≤ 19 * (X / 46) / 100 := by gcongr
      _ ≤ (5 / 1000 : ℝ) * X := by nlinarith [hXPos]
  have hlogFour : (1386 / 1000 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlogThree : Real.log 3 < (1099 / 1000 : ℝ) :=
    Real.log_three_lt_d9.trans (by norm_num)
  have hHExtra : (1099 / 1000 : ℝ) ≤ X / 2_000 := by
    have hcast : (2_198 : ℝ) ≤ X := by
      dsimp [X]
      exact_mod_cast (show 2_198 ≤ H by omega)
    nlinarith
  have hlogGap :
      (1 : ℝ) * Real.log H + P * Real.log n +
          (H + 1 : ℕ) * Real.log 3 < (H : ℝ) * Real.log 4 := by
    norm_num only [one_mul, Nat.cast_add, Nat.cast_one]
    dsimp [L, X] at hlogHSmall hHExtra ⊢
    nlinarith
  simpa [mul_assoc] using
    (nat_three_pow_product_lt_of_log_lt
      (a := H) (b := n) (c := 3) (d := 4)
      (r := 1) (s := n.sqrt.primeCounting) (t := H + 1) (u := H)
      (by omega) (by omega) (by norm_num) (by norm_num) (by
        simpa only [P, Nat.cast_one, Nat.cast_ofNat, Nat.cast_add] using hlogGap))

/-- The prime-counted near gap through `20H` on the upper bridge. -/
theorem primeCountTailTwenty_near_gap
    {n H : ℕ} (hH : 3_000 ≤ H) (hHUpper : H < 6_000)
    (hhalf : 2 * H ≤ n) (hn : n ≤ 20 * H) :
    H * (n ^ n.sqrt.primeCounting * 3 ^ (H + 1)) < 4 ^ H := by
  let X : ℝ := H
  let Z : ℝ := n
  let S : ℝ := Real.sqrt X
  let L : ℝ := Real.log X
  let P : ℝ := n.sqrt.primeCounting
  have hXPos : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < H)
  have hZPos : 0 < Z := by dsimp [Z]; exact_mod_cast (by omega : 0 < n)
  have hSSq : S * S = X := Real.mul_self_sqrt hXPos.le
  have hSGe : (54 : ℝ) ≤ S := by
    dsimp [S]
    apply Real.le_sqrt_of_sq_le
    dsimp [X]
    exact_mod_cast (show 54 ^ 2 ≤ H by norm_num; omega)
  have hSLe : S ≤ X / 54 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 54)]
    nlinarith
  have hLLe : L ≤ 16 * S / 100 := by
    simpa [L, S, X] using
      log_nat_le_sixteen_sqrt_div_hundred_of_threeThousand hH
  have hZLe : Z ≤ 20 * X := by dsimp [Z, X]; exact_mod_cast hn
  have hZLeTwentyFive : Z ≤ 25 * X := by nlinarith
  have hSqrtZ : Real.sqrt Z ≤ 5 * S := by
    calc
      Real.sqrt Z ≤ Real.sqrt (25 * X) := Real.sqrt_le_sqrt hZLeTwentyFive
      _ = 5 * S := by
        dsimp [S]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 25)]
        norm_num
  have hLogZ : Real.log Z ≤ L + 3 := by
    calc
      Real.log Z ≤ Real.log (20 * X) :=
        Real.strictMonoOn_log.monotoneOn hZPos
          (mul_pos (by norm_num) hXPos) hZLe
      _ = Real.log 20 + L := by
        dsimp [L]
        rw [Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) hXPos.ne']
      _ ≤ L + 3 := by
        have hlog20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
          rw [show (20 : ℝ) = 4 * 5 by norm_num,
            Real.log_mul (by norm_num) (by norm_num),
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        rw [hlog20]
        nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hSqrtNatLower : 60 ≤ n.sqrt := by rw [Nat.le_sqrt]; nlinarith
  have hnUpper : n < 400 ^ 2 := by nlinarith
  have hSqrtNatUpper : n.sqrt < 400 := Nat.sqrt_lt'.mpr hnUpper
  have hpiNat : 4 * n.sqrt.primeCounting ≤ n.sqrt + 12 :=
    four_mul_primeCounting_le_add_twelve_of_bounded
      hSqrtNatLower hSqrtNatUpper
  have hpi : 4 * P ≤ (n.sqrt : ℝ) + 12 := by
    dsimp [P]
    exact_mod_cast hpiNat
  have hNatSqrt : (n.sqrt : ℝ) ≤ Real.sqrt Z := by
    simpa [Z] using (Real.nat_sqrt_le_real_sqrt (a := n))
  have hPLe : P ≤ 5 * S / 4 + 3 := by nlinarith
  have hsub : P * Real.log n ≤ (282 / 1000 : ℝ) * X := by
    calc
      P * Real.log n = P * Real.log Z := by rfl
      _ ≤ (5 * S / 4 + 3) * (L + 3) := by
        exact mul_le_mul hPLe hLogZ (by positivity) (by positivity)
      _ ≤ (282 / 1000 : ℝ) * X := by
        have hSL : S * L ≤ 16 * X / 100 := by
          calc
            S * L ≤ S * (16 * S / 100) :=
              mul_le_mul_of_nonneg_left hLLe (Real.sqrt_nonneg X)
            _ = 16 * X / 100 := by rw [← hSSq]; ring
        have hconst : (9 : ℝ) ≤ X * (3 / 1000) := by
          have hcast : (3_000 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast hH
          nlinarith
        nlinarith
  have hlogHSmall : L ≤ (3 / 1000 : ℝ) * X := by
    calc
      L ≤ 16 * S / 100 := hLLe
      _ ≤ 16 * (X / 54) / 100 := by gcongr
      _ ≤ (3 / 1000 : ℝ) * X := by nlinarith [hXPos]
  have hlogFour : (1386 / 1000 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlogThree : Real.log 3 < (1099 / 1000 : ℝ) :=
    Real.log_three_lt_d9.trans (by norm_num)
  have hHExtra : (1099 / 1000 : ℝ) ≤ X / 2_500 := by
    have hcast : (2_748 : ℝ) ≤ X := by
      dsimp [X]
      exact_mod_cast (show 2_748 ≤ H by omega)
    nlinarith
  have hlogGap :
      (1 : ℝ) * Real.log H + P * Real.log n +
          (H + 1 : ℕ) * Real.log 3 < (H : ℝ) * Real.log 4 := by
    norm_num only [one_mul, Nat.cast_add, Nat.cast_one]
    dsimp [L, X] at hlogHSmall hHExtra ⊢
    nlinarith
  simpa [mul_assoc] using
    (nat_three_pow_product_lt_of_log_lt
      (a := H) (b := n) (c := 3) (d := 4)
      (r := 1) (s := n.sqrt.primeCounting) (t := H + 1) (u := H)
      (by omega) (by omega) (by norm_num) (by norm_num) (by
        simpa only [P, Nat.cast_one, Nat.cast_ofNat, Nat.cast_add] using hlogGap))

/-- Effective all-start tail beginning at length `2200`. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_twoThousandTwoHundred
    {N H : ℕ} (hH : 2_200 ≤ H) (hHN : H < N) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  by_cases hOldTail : 6_000 ≤ H
  · exact exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_sixThousand
      hOldTail hHN
  have hHUpper : H < 6_000 := Nat.lt_of_not_ge hOldTail
  have hhalf : 2 * H ≤ N + H := by omega
  have hsumPos : 0 < N + H := by omega
  by_cases hthree : 3_000 ≤ H
  · by_cases hnear : N + H ≤ 20 * H
    · have hgap := primeCountTailTwenty_near_gap
        hthree hHUpper hhalf hnear
      exact
        exists_large_prime_dvd_consecutiveProduct_of_primeCounting_sqrt_three_gap
          (by omega) hHN hgap
    · have hgrowth := primeCountTail_choose_growth_of_twenty_le
        hthree hHUpper (Nat.le_of_not_ge hnear)
      obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
        exists_large_prime_dvd_choose_of_pow_card_lt
          (by omega : H ≤ N + H) hsumPos hgrowth
      refine ⟨p, hpPrime, hHltp, ?_⟩
      rw [consecutiveProduct_eq_ascFactorial,
        Nat.ascFactorial_eq_factorial_mul_choose]
      exact dvd_mul_of_dvd_right hpChoose H.factorial
  · have hThreeUpper : H < 3_000 := Nat.lt_of_not_ge hthree
    by_cases hnear : N + H ≤ 16 * H
    · have hgap := primeCountTailSixteen_near_gap
        hH hThreeUpper hhalf hnear
      exact
        exists_large_prime_dvd_consecutiveProduct_of_primeCounting_sqrt_three_gap
          (by omega) hHN hgap
    · have hgrowth := primeCountTail_choose_growth_of_sixteen_le
        hH hThreeUpper (Nat.le_of_not_ge hnear)
      obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
        exists_large_prime_dvd_choose_of_pow_card_lt
          (by omega : H ≤ N + H) hsumPos hgrowth
      refine ⟨p, hpPrime, hHltp, ?_⟩
      rw [consecutiveProduct_eq_ascFactorial,
        Nat.ascFactorial_eq_factorial_mul_choose]
      exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- The length residual after the `H ≥ 2200` tail. -/
def SylvesterSchurPrimeCountTwoThousandTwoHundredResidualRectangle : Prop :=
  ∀ {N H : ℕ}, 101 ≤ H → H < 2_200 → H < N →
    N + 1 < sylvesterSchurPrimeCountFactorialThreshold H →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- Discharging the `101 ≤ H < 2200` rectangle proves unrestricted
Sylvester--Schur. -/
theorem sylvesterSchurConclusion_of_primeCountTwoThousandTwoHundredResidualRectangle
    (hrect : SylvesterSchurPrimeCountTwoThousandTwoHundredResidualRectangle) :
    SylvesterSchurConclusion := by
  intro N H hH hHN
  by_cases hsmallLength : H < 101
  · exact sylvesterSchurBelow_oneHundredOne hH hsmallLength hHN
  by_cases htail : 2_200 ≤ H
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_twoThousandTwoHundred
        htail hHN
  by_cases hsmallStart :
      N + 1 < sylvesterSchurPrimeCountFactorialThreshold H
  · exact hrect (by omega) (by omega) hHN hsmallStart
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCountFactorialThreshold_le
        hH hHN (Nat.le_of_not_gt hsmallStart)

end Tao2026
