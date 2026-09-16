import Tao2026.SylvesterSchurPrimeCountCertificatesSixC

/-!
# Prime-counted Sylvester--Schur tail from length 512

The transition is `5H` on `512 ≤ H < 625`, `6H` on
`625 ≤ H < 1134`, and `5H` again on `1134 ≤ H < 2200`.
Finite exact prime-count certificates provide the far baselines and a sharp
bounded square-root envelope provides the near gaps.
-/

namespace Tao2026

open Finset

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

private theorem primeCounting_le_pi1906_add_coprime_card
    {H b : ℕ} (hH : 1_907 ≤ H) (hHb : H ≤ b) :
    H.primeCounting ≤ 291 +
      #{x ∈ Finset.Ico 1_907 (b + 1) | Nat.Coprime 210 x} := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  calc
    Nat.primeCounting' (H + 1) ≤
        #{p ∈ Finset.range 1_907 | p.Prime} +
          #{p ∈ Finset.Ico 1_907 (H + 1) | p.Prime} := by
      rw [Nat.primeCounting', Nat.count_eq_card_filter_range,
        Finset.range_eq_Ico, Finset.range_eq_Ico, ←
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le 1_907) (by omega),
        Finset.filter_union]
      apply Finset.card_union_le
    _ ≤ Nat.primeCounting' 1_907 +
        #{p ∈ Finset.Ico 1_907 (H + 1) | Nat.Coprime 210 p} := by
      rw [Nat.primeCounting', Nat.count_eq_card_filter_range]
      gcongr with p hp
      rw [Nat.coprime_comm]
      exact Nat.coprime_of_lt_prime (by norm_num) <|
        (by norm_num : 210 < 1_907).trans_le (Finset.mem_Ico.1 hp).1
    _ ≤ Nat.primeCounting' 1_907 +
        #{p ∈ Finset.Ico 1_907 (b + 1) | Nat.Coprime 210 p} := by
      gcongr with p hp
    _ = 291 + #{p ∈ Finset.Ico 1_907 (b + 1) | Nat.Coprime 210 p} := by
      rw [← Nat.primeCounting_eq_primeCounting'_succ, pi_1906]

private theorem coprime210_card_1907_2021 :
    #{x ∈ Finset.Ico 1_907 2_021 | Nat.Coprime 210 x} = 26 := by
  decide

private theorem coprime210_card_1907_2101 :
    #{x ∈ Finset.Ico 1_907 2_101 | Nat.Coprime 210 x} = 45 := by
  decide

private theorem coprime210_card_1907_2161 :
    #{x ∈ Finset.Ico 1_907 2_161 | Nat.Coprime 210 x} = 59 := by
  decide

private theorem coprime210_card_1907_2200 :
    #{x ∈ Finset.Ico 1_907 2_200 | Nat.Coprime 210 x} = 67 := by
  decide

/-- A bounded square-root-range estimate used below length `2200`. -/
theorem four_mul_primeCounting_le_add_sixteen_of_bounded
    {m : ℕ} (hm : 20 ≤ m) (hmUpper : m < 200) :
    4 * m.primeCounting ≤ m + 16 := by
  have hqLower : 5 ≤ m / 4 := by omega
  have hqUpper : m / 4 < 50 := by omega
  let qFin : Fin 50 := ⟨m / 4, hqUpper⟩
  have hfinite : ∀ q : Fin 50, 5 ≤ q.1 →
      (4 * q.1 + 3).primeCounting ≤ q.1 + 4 := by
    decide
  have hmLe : m ≤ 4 * (m / 4) + 3 := by omega
  have hpi : m.primeCounting ≤ m / 4 + 4 :=
    (Nat.monotone_primeCounting hmLe).trans (by
      simpa [qFin] using hfinite qFin (by simpa [qFin] using hqLower))
  omega

/-- Exact `π(H) ≤ H/5` certificate on the middle finite range. -/
theorem primeCounting_le_div_five_of_threeSixty_bounded
    {H : ℕ} (hH : 360 ≤ H) (hHUpper : H < 1_134) :
    H.primeCounting ≤ H / 5 := by
  by_cases h : H ≤ 366
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_366]
      omega)
  by_cases h : H ≤ 372
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_372]
      omega)
  by_cases h : H ≤ 378
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_378]
      omega)
  by_cases h : H ≤ 382
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_382]
      omega)
  by_cases h : H ≤ 388
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_388]
      omega)
  by_cases h : H ≤ 396
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_396]
      omega)
  by_cases h : H ≤ 408
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_408]
      omega)
  by_cases h : H ≤ 420
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_420]
      omega)
  by_cases h : H ≤ 438
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_438]
      omega)
  by_cases h : H ≤ 456
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_456]
      omega)
  by_cases h : H ≤ 478
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_478]
      omega)
  by_cases h : H ≤ 502
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_502]
      omega)
  by_cases h : H ≤ 546
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_546]
      omega)
  by_cases h : H ≤ 600
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_600]
      omega)
  by_cases h : H ≤ 660
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_660]
      omega)
  by_cases h : H ≤ 750
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_750]
      omega)
  by_cases h : H ≤ 876
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_876]
      omega)
  by_cases h : H ≤ 1_048
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1048]
      omega)
  · have hlast : H ≤ 1_133 := by omega
    exact (Nat.monotone_primeCounting hlast).trans (by
      rw [pi_1133]
      omega)

/-- Exact `π(H) ≤ H/6` certificate on the upper finite range. -/
theorem primeCounting_le_div_six_of_oneThirteenFour_bounded
    {H : ℕ} (hH : 1_134 ≤ H) (hHUpper : H < 2_200) :
    H.primeCounting ≤ H / 6 := by
  by_cases h : H ≤ 1_150
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1150]
      omega)
  by_cases h : H ≤ 1_162
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1162]
      omega)
  by_cases h : H ≤ 1_180
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1180]
      omega)
  by_cases h : H ≤ 1_200
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1200]
      omega)
  by_cases h : H ≤ 1_228
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1228]
      omega)
  by_cases h : H ≤ 1_258
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1258]
      omega)
  by_cases h : H ≤ 1_290
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1290]
      omega)
  by_cases h : H ≤ 1_320
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1320]
      omega)
  by_cases h : H ≤ 1_380
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1380]
      omega)
  by_cases h : H ≤ 1_452
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1452]
      omega)
  by_cases h : H ≤ 1_542
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1542]
      omega)
  by_cases h : H ≤ 1_626
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1626]
      omega)
  by_cases h : H ≤ 1_746
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1746]
      omega)
  by_cases h : H ≤ 1_906
  · exact (Nat.monotone_primeCounting h).trans (by
      rw [pi_1906]
      omega)
  by_cases h : H ≤ 2_020
  · have hpi := primeCounting_le_pi1906_add_coprime_card (b := 2_020)
        (show 1_907 ≤ H by omega) h
    rw [coprime210_card_1907_2021] at hpi
    omega
  by_cases h : H ≤ 2_100
  · have hpi := primeCounting_le_pi1906_add_coprime_card (b := 2_100)
        (show 1_907 ≤ H by omega) h
    rw [coprime210_card_1907_2101] at hpi
    omega
  by_cases h : H ≤ 2_160
  · have hpi := primeCounting_le_pi1906_add_coprime_card (b := 2_160)
        (show 1_907 ≤ H by omega) h
    rw [coprime210_card_1907_2161] at hpi
    omega
  · have hlast : H ≤ 2_199 := by omega
    have hpi := primeCounting_le_pi1906_add_coprime_card (b := 2_199)
      (show 1_907 ≤ H by omega) hlast
    rw [coprime210_card_1907_2200] at hpi
    omega

/-- From `H=512`, `log H ≤ 28 sqrt(H)/100`. -/
theorem log_nat_le_twentyEight_sqrt_div_hundred_of_fiveHundredTwelve
    {H : ℕ} (hH : 512 ≤ H) :
    Real.log H ≤ 28 * Real.sqrt H / 100 := by
  let X : ℝ := H
  let Y : ℝ := 512
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hYPos : 0 < Y := by positivity
  have hYX : Y ≤ X := by
    dsimp [Y, X]
    exact_mod_cast hH
  have hlogY : Real.log Y = 9 * Real.log 2 := by
    dsimp [Y]
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    norm_num
  have hTwoLog : (2 : ℝ) ≤ Real.log Y := by
    rw [hlogY]
    nlinarith [Real.log_two_gt_d9]
  have hExp : Real.exp 2 ≤ Y := by
    rw [← Real.exp_log hYPos]
    exact Real.exp_le_exp.mpr hTwoLog
  have hanti : Real.log X / Real.sqrt X ≤
      Real.log Y / Real.sqrt Y :=
    Real.log_div_sqrt_antitoneOn hExp (hExp.trans hYX) hYX
  have hSqrtYLower : (113 / 5 : ℝ) ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    norm_num [Y]
  have hSqrtYPos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hYPos
  have hbase : Real.log Y / Real.sqrt Y < (28 / 100 : ℝ) := by
    rw [div_lt_iff₀ hSqrtYPos]
    rw [hlogY]
    nlinarith [Real.log_two_lt_d9]
  have hratio : Real.log X / Real.sqrt X < (28 / 100 : ℝ) :=
    hanti.trans_lt hbase
  have hSqrtPos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXPos
  rw [div_lt_iff₀ hSqrtPos] at hratio
  dsimp [X] at hratio ⊢
  nlinarith

/-- From `H=625`, `log H ≤ 26 sqrt(H)/100`. -/
theorem log_nat_le_twentySix_sqrt_div_hundred_of_sixHundredTwentyFive
    {H : ℕ} (hH : 625 ≤ H) :
    Real.log H ≤ 26 * Real.sqrt H / 100 := by
  let X : ℝ := H
  let Y : ℝ := 625
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hYPos : 0 < Y := by positivity
  have hYX : Y ≤ X := by
    dsimp [Y, X]
    exact_mod_cast hH
  have hlogY : Real.log Y = 4 * Real.log 5 := by
    dsimp [Y]
    rw [show (625 : ℝ) = 5 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hTwoLog : (2 : ℝ) ≤ Real.log Y := by
    rw [hlogY]
    nlinarith [Real.log_five_gt_d9]
  have hExp : Real.exp 2 ≤ Y := by
    rw [← Real.exp_log hYPos]
    exact Real.exp_le_exp.mpr hTwoLog
  have hanti : Real.log X / Real.sqrt X ≤
      Real.log Y / Real.sqrt Y :=
    Real.log_div_sqrt_antitoneOn hExp (hExp.trans hYX) hYX
  have hSqrtY : Real.sqrt Y = 25 := by
    have hsq : Y = (25 : ℝ) ^ 2 := by norm_num [Y]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hbase : Real.log Y / Real.sqrt Y < (26 / 100 : ℝ) := by
    rw [hSqrtY, div_lt_iff₀ (by positivity), hlogY]
    nlinarith [Real.log_five_lt_d9]
  have hratio : Real.log X / Real.sqrt X < (26 / 100 : ℝ) :=
    hanti.trans_lt hbase
  have hSqrtPos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXPos
  rw [div_lt_iff₀ hSqrtPos] at hratio
  dsimp [X] at hratio ⊢
  nlinarith

/-- Far logarithmic baseline at `5H` using `π(H) ≤ H/5`. -/
theorem primeCountTail_primeCounting_log_baseline_five_div_five
    {H : ℕ} (hH : 512 ≤ H) (hHUpper : H < 625) :
    (H.primeCounting : ℝ) * Real.log (5 * H) <
      (H : ℝ) * Real.log 5 := by
  let X : ℝ := H
  let P : ℝ := H.primeCounting
  let L : ℝ := Real.log X
  let C : ℝ := Real.log 5
  have hXPos : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < H)
  have hCPos : 0 < C := by dsimp [C]; positivity
  have hpiNat : H.primeCounting ≤ H / 5 :=
    primeCounting_le_div_five_of_threeSixty_bounded (by omega) (by omega)
  have hpiFive : 5 * P ≤ X := by
    dsimp [P, X]
    exact_mod_cast (show 5 * H.primeCounting ≤ H by omega)
  have hHPow : H < 5 ^ 4 := by norm_num; omega
  have hlogPow : Real.log X < Real.log ((5 : ℝ) ^ 4) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr hXPos
    · exact Set.mem_Ioi.mpr (by positivity)
    · dsimp [X]
      exact_mod_cast hHPow
  have hLC : L < 4 * C := by
    dsimp [L, C] at hlogPow ⊢
    rw [Real.log_pow] at hlogPow
    norm_num at hlogPow ⊢
    exact hlogPow
  have hsumPos : 0 ≤ L + C := by positivity
  have hmul : (5 * P) * (L + C) ≤ X * (L + C) :=
    mul_le_mul_of_nonneg_right hpiFive hsumPos
  have htarget : X * (L + C) < X * (5 * C) :=
    mul_lt_mul_of_pos_left (by nlinarith) hXPos
  have hmain : P * (L + C) < X * C := by nlinarith
  have hlogMul : Real.log (5 * H) = L + C := by
    dsimp [L, C, X]
    rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hXPos.ne']
    ring
  rw [hlogMul]
  exact hmain

/-- Far logarithmic baseline at `6H` using `π(H) ≤ H/5`. -/
theorem primeCountTail_primeCounting_log_baseline_six_div_five
    {H : ℕ} (hH : 625 ≤ H) (hHUpper : H < 1_134) :
    (H.primeCounting : ℝ) * Real.log (6 * H) <
      (H : ℝ) * Real.log 6 := by
  let X : ℝ := H
  let P : ℝ := H.primeCounting
  let L : ℝ := Real.log X
  let C : ℝ := Real.log 6
  have hXPos : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < H)
  have hCPos : 0 < C := by dsimp [C]; positivity
  have hpiNat : H.primeCounting ≤ H / 5 :=
    primeCounting_le_div_five_of_threeSixty_bounded (by omega) hHUpper
  have hpiFive : 5 * P ≤ X := by
    dsimp [P, X]
    exact_mod_cast (show 5 * H.primeCounting ≤ H by omega)
  have hHPow : H < 6 ^ 4 := by norm_num; omega
  have hlogPow : Real.log X < Real.log ((6 : ℝ) ^ 4) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr hXPos
    · exact Set.mem_Ioi.mpr (by positivity)
    · dsimp [X]
      exact_mod_cast hHPow
  have hLC : L < 4 * C := by
    dsimp [L, C] at hlogPow ⊢
    rw [Real.log_pow] at hlogPow
    norm_num at hlogPow ⊢
    exact hlogPow
  have hsumPos : 0 ≤ L + C := by positivity
  have hmul : (5 * P) * (L + C) ≤ X * (L + C) :=
    mul_le_mul_of_nonneg_right hpiFive hsumPos
  have htarget : X * (L + C) < X * (5 * C) :=
    mul_lt_mul_of_pos_left (by nlinarith) hXPos
  have hmain : P * (L + C) < X * C := by nlinarith
  have hlogMul : Real.log (6 * H) = L + C := by
    dsimp [L, C, X]
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hXPos.ne']
    ring
  rw [hlogMul]
  exact hmain

/-- Far logarithmic baseline at `5H` using `π(H) ≤ H/6`. -/
theorem primeCountTail_primeCounting_log_baseline_five_div_six
    {H : ℕ} (hH : 1_134 ≤ H) (hHUpper : H < 2_200) :
    (H.primeCounting : ℝ) * Real.log (5 * H) <
      (H : ℝ) * Real.log 5 := by
  let X : ℝ := H
  let P : ℝ := H.primeCounting
  let L : ℝ := Real.log X
  let C : ℝ := Real.log 5
  have hXPos : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < H)
  have hCPos : 0 < C := by dsimp [C]; positivity
  have hpiNat : H.primeCounting ≤ H / 6 :=
    primeCounting_le_div_six_of_oneThirteenFour_bounded hH hHUpper
  have hpiSix : 6 * P ≤ X := by
    dsimp [P, X]
    exact_mod_cast (show 6 * H.primeCounting ≤ H by omega)
  have hHPow : H < 5 ^ 5 := by norm_num; omega
  have hlogPow : Real.log X < Real.log ((5 : ℝ) ^ 5) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr hXPos
    · exact Set.mem_Ioi.mpr (by positivity)
    · dsimp [X]
      exact_mod_cast hHPow
  have hLC : L < 5 * C := by
    dsimp [L, C] at hlogPow ⊢
    rw [Real.log_pow] at hlogPow
    norm_num at hlogPow ⊢
    exact hlogPow
  have hsumPos : 0 ≤ L + C := by positivity
  have hmul : (6 * P) * (L + C) ≤ X * (L + C) :=
    mul_le_mul_of_nonneg_right hpiSix hsumPos
  have htarget : X * (L + C) < X * (6 * C) :=
    mul_lt_mul_of_pos_left (by nlinarith) hXPos
  have hmain : P * (L + C) < X * C := by nlinarith
  have hlogMul : Real.log (5 * H) = L + C := by
    dsimp [L, C, X]
    rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hXPos.ne']
    ring
  rw [hlogMul]
  exact hmain

/-- Binomial growth propagated from a `5H` baseline with `π(H) ≤ H/5`. -/
theorem primeCountTail_choose_growth_of_five_div_five_le
    {n H : ℕ} (hH : 512 ≤ H) (hHUpper : H < 625) (hn : 5 * H ≤ n) :
    n ^ (H + 1).primesBelow.card < n.choose H := by
  apply choose_growth_of_le (m := 5 * H)
  · omega
  · rw [card_primesBelow_succ_eq_primeCounting]
    exact primeCounting_lt_self (by omega)
  · exact hn
  · exact primeCountTail_choose_growth_baseline_of_log (by omega) (by omega)
      (primeCountTail_primeCounting_log_baseline_five_div_five hH hHUpper)

/-- Binomial growth propagated from the `6H` baseline. -/
theorem primeCountTail_choose_growth_of_six_div_five_le
    {n H : ℕ} (hH : 625 ≤ H) (hHUpper : H < 1_134) (hn : 6 * H ≤ n) :
    n ^ (H + 1).primesBelow.card < n.choose H := by
  apply choose_growth_of_le (m := 6 * H)
  · omega
  · rw [card_primesBelow_succ_eq_primeCounting]
    exact primeCounting_lt_self (by omega)
  · exact hn
  · exact primeCountTail_choose_growth_baseline_of_log (by omega) (by omega)
      (primeCountTail_primeCounting_log_baseline_six_div_five hH hHUpper)

/-- Binomial growth propagated from a `5H` baseline with `π(H) ≤ H/6`. -/
theorem primeCountTail_choose_growth_of_five_div_six_le
    {n H : ℕ} (hH : 1_134 ≤ H) (hHUpper : H < 2_200) (hn : 5 * H ≤ n) :
    n ^ (H + 1).primesBelow.card < n.choose H := by
  apply choose_growth_of_le (m := 5 * H)
  · omega
  · rw [card_primesBelow_succ_eq_primeCounting]
    exact primeCounting_lt_self (by omega)
  · exact hn
  · exact primeCountTail_choose_growth_baseline_of_log (by omega) (by omega)
      (primeCountTail_primeCounting_log_baseline_five_div_six hH hHUpper)

/-- The prime-counted near gap through `5H` from length `512`. -/
theorem primeCountTailFive_near_gap
    {n H : ℕ} (hH : 512 ≤ H) (hHUpper : H < 2_200)
    (hhalf : 2 * H ≤ n) (hn : n ≤ 5 * H) :
    H * (n ^ n.sqrt.primeCounting * 3 ^ (H + 1)) < 4 ^ H := by
  let X : ℝ := H
  let Z : ℝ := n
  let S : ℝ := Real.sqrt X
  let L : ℝ := Real.log X
  let P : ℝ := n.sqrt.primeCounting
  have hXPos : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < H)
  have hZPos : 0 < Z := by dsimp [Z]; exact_mod_cast (by omega : 0 < n)
  have hSSq : S * S = X := Real.mul_self_sqrt hXPos.le
  have hSGe : (22 : ℝ) ≤ S := by
    dsimp [S]
    apply Real.le_sqrt_of_sq_le
    dsimp [X]
    exact_mod_cast (show 22 ^ 2 ≤ H by norm_num; omega)
  have hSLe : S ≤ X / 22 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 22)]
    nlinarith
  have hLLe : L ≤ 28 * S / 100 := by
    simpa [L, S, X] using
      log_nat_le_twentyEight_sqrt_div_hundred_of_fiveHundredTwelve hH
  have hZLe : Z ≤ 5 * X := by dsimp [Z, X]; exact_mod_cast hn
  have hSqrtZ : Real.sqrt Z ≤ 9 * S / 4 := by
    have hsqZ : Real.sqrt Z * Real.sqrt Z = Z := Real.mul_self_sqrt hZPos.le
    have hSNonneg : 0 ≤ S := Real.sqrt_nonneg X
    have hSqrtZNonneg : 0 ≤ Real.sqrt Z := Real.sqrt_nonneg Z
    nlinarith
  have hLogZ : Real.log Z ≤ L + 161 / 100 := by
    calc
      Real.log Z ≤ Real.log (5 * X) :=
        Real.strictMonoOn_log.monotoneOn hZPos
          (mul_pos (by norm_num) hXPos) hZLe
      _ = Real.log 5 + L := by
        dsimp [L]
        rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hXPos.ne']
      _ ≤ L + 161 / 100 := by
        nlinarith [Real.log_five_lt_d9]
  have hSqrtNatLower : 20 ≤ n.sqrt := by rw [Nat.le_sqrt]; nlinarith
  have hnUpper : n < 200 ^ 2 := by nlinarith
  have hSqrtNatUpper : n.sqrt < 200 := Nat.sqrt_lt'.mpr hnUpper
  have hpiNat : 4 * n.sqrt.primeCounting ≤ n.sqrt + 16 :=
    four_mul_primeCounting_le_add_sixteen_of_bounded
      hSqrtNatLower hSqrtNatUpper
  have hpi : 4 * P ≤ (n.sqrt : ℝ) + 16 := by
    dsimp [P]
    exact_mod_cast hpiNat
  have hNatSqrt : (n.sqrt : ℝ) ≤ Real.sqrt Z := by
    simpa [Z] using (Real.nat_sqrt_le_real_sqrt (a := n))
  have hPLe : P ≤ 9 * S / 16 + 4 := by nlinarith
  have hsub : P * Real.log n ≤ (263 / 1000 : ℝ) * X := by
    calc
      P * Real.log n = P * Real.log Z := by rfl
      _ ≤ (9 * S / 16 + 4) * (L + 161 / 100) := by
        exact mul_le_mul hPLe hLogZ (by positivity) (by positivity)
      _ ≤ (263 / 1000 : ℝ) * X := by
        have hSL : S * L ≤ 28 * X / 100 := by
          calc
            S * L ≤ S * (28 * S / 100) :=
              mul_le_mul_of_nonneg_left hLLe (Real.sqrt_nonneg X)
            _ = 28 * X / 100 := by rw [← hSSq]; ring
        have hconst : (644 / 100 : ℝ) ≤ X * (13 / 1000) := by
          have hcast : (512 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast hH
          nlinarith
        nlinarith
  have hlogHSmall : L ≤ (13 / 1000 : ℝ) * X := by
    calc
      L ≤ 28 * S / 100 := hLLe
      _ ≤ 28 * (X / 22) / 100 := by gcongr
      _ ≤ (13 / 1000 : ℝ) * X := by nlinarith [hXPos]
  have hlogFour : (1386 / 1000 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlogThree : Real.log 3 < (1099 / 1000 : ℝ) :=
    Real.log_three_lt_d9.trans (by norm_num)
  have hHExtra : (1099 / 1000 : ℝ) ≤ X / 450 := by
    have hcast : (495 : ℝ) ≤ X := by
      dsimp [X]
      exact_mod_cast (show 495 ≤ H by omega)
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

/-- The prime-counted near gap through `6H` from length `625`. -/
theorem primeCountTailSix_near_gap
    {n H : ℕ} (hH : 625 ≤ H) (hHUpper : H < 1_134)
    (hhalf : 2 * H ≤ n) (hn : n ≤ 6 * H) :
    H * (n ^ n.sqrt.primeCounting * 3 ^ (H + 1)) < 4 ^ H := by
  let X : ℝ := H
  let Z : ℝ := n
  let S : ℝ := Real.sqrt X
  let L : ℝ := Real.log X
  let P : ℝ := n.sqrt.primeCounting
  have hXPos : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < H)
  have hZPos : 0 < Z := by dsimp [Z]; exact_mod_cast (by omega : 0 < n)
  have hSSq : S * S = X := Real.mul_self_sqrt hXPos.le
  have hSGe : (25 : ℝ) ≤ S := by
    dsimp [S]
    apply Real.le_sqrt_of_sq_le
    dsimp [X]
    exact_mod_cast (show 25 ^ 2 ≤ H by norm_num; omega)
  have hSLe : S ≤ X / 25 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 25)]
    nlinarith
  have hLLe : L ≤ 26 * S / 100 := by
    simpa [L, S, X] using
      log_nat_le_twentySix_sqrt_div_hundred_of_sixHundredTwentyFive hH
  have hZLe : Z ≤ 6 * X := by dsimp [Z, X]; exact_mod_cast hn
  have hSqrtZ : Real.sqrt Z ≤ 5 * S / 2 := by
    have hsqZ : Real.sqrt Z * Real.sqrt Z = Z := Real.mul_self_sqrt hZPos.le
    have hSNonneg : 0 ≤ S := Real.sqrt_nonneg X
    have hSqrtZNonneg : 0 ≤ Real.sqrt Z := Real.sqrt_nonneg Z
    nlinarith
  have hLogZ : Real.log Z ≤ L + 18 / 10 := by
    calc
      Real.log Z ≤ Real.log (6 * X) :=
        Real.strictMonoOn_log.monotoneOn hZPos
          (mul_pos (by norm_num) hXPos) hZLe
      _ = Real.log 6 + L := by
        dsimp [L]
        rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hXPos.ne']
      _ ≤ L + 18 / 10 := by
        have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
          rw [show (6 : ℝ) = 2 * 3 by norm_num,
            Real.log_mul (by norm_num) (by norm_num)]
        rw [hlog6]
        nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have hSqrtNatLower : 20 ≤ n.sqrt := by rw [Nat.le_sqrt]; nlinarith
  have hnUpper : n < 200 ^ 2 := by nlinarith
  have hSqrtNatUpper : n.sqrt < 200 := Nat.sqrt_lt'.mpr hnUpper
  have hpiNat : 4 * n.sqrt.primeCounting ≤ n.sqrt + 16 :=
    four_mul_primeCounting_le_add_sixteen_of_bounded
      hSqrtNatLower hSqrtNatUpper
  have hpi : 4 * P ≤ (n.sqrt : ℝ) + 16 := by
    dsimp [P]
    exact_mod_cast hpiNat
  have hNatSqrt : (n.sqrt : ℝ) ≤ Real.sqrt Z := by
    simpa [Z] using (Real.nat_sqrt_le_real_sqrt (a := n))
  have hPLe : P ≤ 5 * S / 8 + 4 := by nlinarith
  have hsub : P * Real.log n ≤ (261 / 1000 : ℝ) * X := by
    calc
      P * Real.log n = P * Real.log Z := by rfl
      _ ≤ (5 * S / 8 + 4) * (L + 18 / 10) := by
        exact mul_le_mul hPLe hLogZ (by positivity) (by positivity)
      _ ≤ (261 / 1000 : ℝ) * X := by
        have hSL : S * L ≤ 26 * X / 100 := by
          calc
            S * L ≤ S * (26 * S / 100) :=
              mul_le_mul_of_nonneg_left hLLe (Real.sqrt_nonneg X)
            _ = 26 * X / 100 := by rw [← hSSq]; ring
        have hconst : (72 / 10 : ℝ) ≤ X * (12 / 1000) := by
          have hcast : (625 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast hH
          nlinarith
        nlinarith
  have hlogHSmall : L ≤ (11 / 1000 : ℝ) * X := by
    calc
      L ≤ 26 * S / 100 := hLLe
      _ ≤ 26 * (X / 25) / 100 := by gcongr
      _ ≤ (11 / 1000 : ℝ) * X := by nlinarith [hXPos]
  have hlogFour : (1386 / 1000 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlogThree : Real.log 3 < (1099 / 1000 : ℝ) :=
    Real.log_three_lt_d9.trans (by norm_num)
  have hHExtra : (1099 / 1000 : ℝ) ≤ X / 550 := by
    have hcast : (605 : ℝ) ≤ X := by
      dsimp [X]
      exact_mod_cast (show 605 ≤ H by omega)
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

/-- Effective all-start tail beginning at length `512`. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_fiveHundredTwelve
    {N H : ℕ} (hH : 512 ≤ H) (hHN : H < N) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  by_cases hOldTail : 2_200 ≤ H
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_twoThousandTwoHundred
        hOldTail hHN
  have hHUpper : H < 2_200 := Nat.lt_of_not_ge hOldTail
  have hhalf : 2 * H ≤ N + H := by omega
  have hsumPos : 0 < N + H := by omega
  by_cases hSixBand : 625 ≤ H ∧ H < 1_134
  · by_cases hnear : N + H ≤ 6 * H
    · have hgap := primeCountTailSix_near_gap
        hSixBand.1 hSixBand.2 hhalf hnear
      exact
        exists_large_prime_dvd_consecutiveProduct_of_primeCounting_sqrt_three_gap
          (by omega) hHN hgap
    · have hgrowth := primeCountTail_choose_growth_of_six_div_five_le
        hSixBand.1 hSixBand.2 (Nat.le_of_not_ge hnear)
      obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
        exists_large_prime_dvd_choose_of_pow_card_lt
          (by omega : H ≤ N + H) hsumPos hgrowth
      refine ⟨p, hpPrime, hHltp, ?_⟩
      rw [consecutiveProduct_eq_ascFactorial,
        Nat.ascFactorial_eq_factorial_mul_choose]
      exact dvd_mul_of_dvd_right hpChoose H.factorial
  · by_cases hnear : N + H ≤ 5 * H
    · have hgap := primeCountTailFive_near_gap hH hHUpper hhalf hnear
      exact
        exists_large_prime_dvd_consecutiveProduct_of_primeCounting_sqrt_three_gap
          (by omega) hHN hgap
    · by_cases hLowerBand : H < 625
      · have hgrowth := primeCountTail_choose_growth_of_five_div_five_le
          hH hLowerBand (Nat.le_of_not_ge hnear)
        obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
          exists_large_prime_dvd_choose_of_pow_card_lt
            (by omega : H ≤ N + H) hsumPos hgrowth
        refine ⟨p, hpPrime, hHltp, ?_⟩
        rw [consecutiveProduct_eq_ascFactorial,
          Nat.ascFactorial_eq_factorial_mul_choose]
        exact dvd_mul_of_dvd_right hpChoose H.factorial
      · have hUpperBand : 1_134 ≤ H := by omega
        have hgrowth := primeCountTail_choose_growth_of_five_div_six_le
          hUpperBand hHUpper (Nat.le_of_not_ge hnear)
        obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
          exists_large_prime_dvd_choose_of_pow_card_lt
            (by omega : H ≤ N + H) hsumPos hgrowth
        refine ⟨p, hpPrime, hHltp, ?_⟩
        rw [consecutiveProduct_eq_ascFactorial,
          Nat.ascFactorial_eq_factorial_mul_choose]
        exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- The length residual after the `H ≥ 512` tail. -/
def SylvesterSchurPrimeCountFiveHundredTwelveResidualRectangle : Prop :=
  ∀ {N H : ℕ}, 101 ≤ H → H < 512 → H < N →
    N + 1 < sylvesterSchurPrimeCountFactorialThreshold H →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- Discharging the `101 ≤ H < 512` rectangle proves unrestricted
Sylvester--Schur. -/
theorem sylvesterSchurConclusion_of_primeCountFiveHundredTwelveResidualRectangle
    (hrect : SylvesterSchurPrimeCountFiveHundredTwelveResidualRectangle) :
    SylvesterSchurConclusion := by
  intro N H hH hHN
  by_cases hsmallLength : H < 101
  · exact sylvesterSchurBelow_oneHundredOne hH hsmallLength hHN
  by_cases htail : 512 ≤ H
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_fiveHundredTwelve
        htail hHN
  by_cases hsmallStart :
      N + 1 < sylvesterSchurPrimeCountFactorialThreshold H
  · exact hrect (by omega) (by omega) hHN hsmallStart
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCountFactorialThreshold_le
        hH hHN (Nat.le_of_not_gt hsmallStart)

end Tao2026
