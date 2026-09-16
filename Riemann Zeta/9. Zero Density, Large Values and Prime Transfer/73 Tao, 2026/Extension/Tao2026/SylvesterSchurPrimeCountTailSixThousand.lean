import Tao2026.SylvesterSchurPrimeCountTail

/-!
# Prime-counted Sylvester--Schur tail from length 6000

On the finite bridge below length `10000`, the exact certificate
`6 * π(m) ≤ m + 84` for `100 ≤ m < 800` improves the low-prime part of the
square-root envelope. This closes the near branch from `H = 6000`; the
existing prime-count baseline closes the far branch.
-/

namespace Tao2026

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-- A finite exact prime-count envelope on the square-root range needed below
length `10000`. -/
theorem six_mul_primeCounting_le_add_eightyFour_of_bounded
    {m : ℕ} (hm : 100 ≤ m) (hmUpper : m < 800) :
    6 * m.primeCounting ≤ m + 84 := by
  have hqLower : 16 ≤ m / 6 := by omega
  have hqUpper : m / 6 < 134 := by omega
  let qFin : Fin 134 := ⟨m / 6, hqUpper⟩
  have hfinite : ∀ q : Fin 134, 16 ≤ q.1 →
      (6 * q.1 + 5).primeCounting ≤ q.1 + 14 := by
    decide
  have hmLe : m ≤ 6 * (m / 6) + 5 := by omega
  have hpi : m.primeCounting ≤ m / 6 + 14 :=
    (Nat.monotone_primeCounting hmLe).trans (by
      simpa [qFin] using hfinite qFin (by simpa [qFin] using hqLower))
  omega

/-- From `H=6000`, `log H` is at most `13 sqrt(H) / 100`. -/
theorem log_nat_le_thirteen_sqrt_div_hundred_of_sixThousand
    {H : ℕ} (hH : 6_000 ≤ H) :
    Real.log H ≤ 13 * Real.sqrt H / 100 := by
  let X : ℝ := H
  let Y : ℝ := 5_625
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hYPos : 0 < Y := by positivity
  have hYX : Y ≤ X := by
    dsimp [Y, X]
    exact_mod_cast (show 5_625 ≤ H by omega)
  have hpowLower : (2 : ℝ) ^ 12 ≤ Y := by norm_num [Y]
  have hpowUpper : Y ≤ (2 : ℝ) ^ 13 := by norm_num [Y]
  have hlogLower : 12 * Real.log 2 ≤ Real.log Y := by
    calc
      12 * Real.log 2 = Real.log ((2 : ℝ) ^ 12) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log Y := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hYPos) hpowLower
  have hlogUpper : Real.log Y ≤ 13 * Real.log 2 := by
    calc
      Real.log Y ≤ Real.log ((2 : ℝ) ^ 13) :=
        Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hYPos)
          (Set.mem_Ioi.mpr (by positivity)) hpowUpper
      _ = 13 * Real.log 2 := by
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
  have hSqrtY : Real.sqrt Y = 75 := by
    have hsq : Y = (75 : ℝ) ^ 2 := by norm_num [Y]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hbase : Real.log Y / Real.sqrt Y < (13 / 100 : ℝ) := by
    rw [hSqrtY, div_lt_iff₀ (by positivity)]
    nlinarith [Real.log_two_lt_d9]
  have hratio : Real.log X / Real.sqrt X < (13 / 100 : ℝ) :=
    hanti.trans_lt hbase
  have hSqrtPos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXPos
  rw [div_lt_iff₀ hSqrtPos] at hratio
  dsimp [X] at hratio ⊢
  nlinarith

/-- On the bridge `6000 ≤ H < 10000`, the prime-counted square-root/Hanson
gap holds through upper index `64H`. -/
theorem primeCountTailSixThousand_near_gap
    {n H : ℕ} (hH : 6_000 ≤ H) (hHUpper : H < 10_000)
    (hhalf : 2 * H ≤ n) (hn : n ≤ 64 * H) :
    H * (n ^ n.sqrt.primeCounting * 3 ^ (H + 1)) < 4 ^ H := by
  let X : ℝ := H
  let Z : ℝ := n
  let S : ℝ := Real.sqrt X
  let L : ℝ := Real.log X
  let P : ℝ := n.sqrt.primeCounting
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hZPos : 0 < Z := by
    dsimp [Z]
    exact_mod_cast (by omega : 0 < n)
  have hSSq : S * S = X := Real.mul_self_sqrt hXPos.le
  have hSGe : (75 : ℝ) ≤ S := by
    dsimp [S]
    apply Real.le_sqrt_of_sq_le
    dsimp [X]
    exact_mod_cast (show 75 ^ 2 ≤ H by norm_num; omega)
  have hSLe : S ≤ X / 75 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 75)]
    nlinarith
  have hLLe : L ≤ 13 * S / 100 := by
    simpa [L, S, X] using
      log_nat_le_thirteen_sqrt_div_hundred_of_sixThousand hH
  have hZLe : Z ≤ 64 * X := by
    dsimp [Z, X]
    exact_mod_cast hn
  have hSqrtZ : Real.sqrt Z ≤ 8 * S := by
    calc
      Real.sqrt Z ≤ Real.sqrt (64 * X) := Real.sqrt_le_sqrt hZLe
      _ = 8 * S := by
        dsimp [S]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
        norm_num
  have hLogZ : Real.log Z ≤ L + 21 / 5 := by
    calc
      Real.log Z ≤ Real.log (64 * X) :=
        Real.strictMonoOn_log.monotoneOn hZPos
          (mul_pos (by norm_num) hXPos) hZLe
      _ = Real.log 64 + L := by
        dsimp [L]
        rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) hXPos.ne']
      _ ≤ L + 21 / 5 := by
        have hlog64 : Real.log 64 = 6 * Real.log 2 := by
          rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
          norm_num
        rw [hlog64]
        nlinarith [Real.log_two_lt_d9]
  have hSqrtNatLower : 100 ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    nlinarith
  have hnUpper : n < 800 ^ 2 := by
    nlinarith
  have hSqrtNatUpper : n.sqrt < 800 := Nat.sqrt_lt'.mpr hnUpper
  have hpiNat : 6 * n.sqrt.primeCounting ≤ n.sqrt + 84 :=
    six_mul_primeCounting_le_add_eightyFour_of_bounded
      hSqrtNatLower hSqrtNatUpper
  have hpi : 6 * P ≤ (n.sqrt : ℝ) + 84 := by
    dsimp [P]
    exact_mod_cast hpiNat
  have hNatSqrt : (n.sqrt : ℝ) ≤ Real.sqrt Z := by
    simpa [Z] using (Real.nat_sqrt_le_real_sqrt (a := n))
  have hPLe : P ≤ 4 * S / 3 + 14 := by
    nlinarith
  have hsub : P * Real.log n ≤ (283 / 1000 : ℝ) * X := by
    calc
      P * Real.log n = P * Real.log Z := by rfl
      _ ≤ (4 * S / 3 + 14) * (L + 21 / 5) := by
        exact mul_le_mul hPLe hLogZ (by positivity) (by positivity)
      _ ≤ (283 / 1000 : ℝ) * X := by
        have hSL : S * L ≤ 13 * X / 100 := by
          calc
            S * L ≤ S * (13 * S / 100) :=
              mul_le_mul_of_nonneg_left hLLe (Real.sqrt_nonneg X)
            _ = 13 * X / 100 := by rw [← hSSq]; ring
        have hconst : (294 / 5 : ℝ) ≤ X * (10 / 1000) := by
          have hcast : (6_000 : ℝ) ≤ X := by
            dsimp [X]
            exact_mod_cast hH
          nlinarith
        nlinarith
  have hlogHSmall : L ≤ (2 / 1000 : ℝ) * X := by
    calc
      L ≤ 13 * S / 100 := hLLe
      _ ≤ 13 * (X / 75) / 100 := by gcongr
      _ ≤ (2 / 1000 : ℝ) * X := by nlinarith [hXPos]
  have hlogFour : (1386 / 1000 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlogThree : Real.log 3 < (1099 / 1000 : ℝ) :=
    Real.log_three_lt_d9.trans (by norm_num)
  have hHExtra : (1099 / 1000 : ℝ) ≤ X / 5_000 := by
    have hcast : (5_495 : ℝ) ≤ X := by
      dsimp [X]
      exact_mod_cast (show 5_495 ≤ H by omega)
    nlinarith
  have hlogGap :
      (1 : ℝ) * Real.log H + P * Real.log n +
          (H + 1 : ℕ) * Real.log 3 <
        (H : ℝ) * Real.log 4 := by
    norm_num only [one_mul, Nat.cast_add, Nat.cast_one]
    dsimp [L, X] at hlogHSmall hHExtra ⊢
    nlinarith
  simpa [mul_assoc] using
    (nat_three_pow_product_lt_of_log_lt
      (a := H) (b := n) (c := 3) (d := 4)
      (r := 1) (s := n.sqrt.primeCounting) (t := H + 1) (u := H)
      (by omega) (by omega) (by norm_num) (by norm_num) (by
        simpa only [P, Nat.cast_one, Nat.cast_ofNat, Nat.cast_add] using hlogGap))

/-- Effective all-start tail beginning at length `6000`. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_sixThousand
    {N H : ℕ} (hH : 6_000 ≤ H) (hHN : H < N) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  by_cases hOldTail : 10_000 ≤ H
  · exact exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail
      hOldTail hHN
  have hHUpper : H < 10_000 := Nat.lt_of_not_ge hOldTail
  have hhalf : 2 * H ≤ N + H := by omega
  have hsumPos : 0 < N + H := by omega
  by_cases hnear : N + H ≤ 64 * H
  · have hgap := primeCountTailSixThousand_near_gap
      hH hHUpper hhalf hnear
    exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCounting_sqrt_three_gap
        (by omega) hHN hgap
  · have hgrowth :
        (N + H) ^ (H + 1).primesBelow.card < (N + H).choose H :=
      primeCountTail_choose_growth_of_baseline_le (by omega) (by omega)
        (Nat.le_of_not_ge hnear)
    obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
      exists_large_prime_dvd_choose_of_pow_card_lt
        (by omega : H ≤ N + H) hsumPos hgrowth
    refine ⟨p, hpPrime, hHltp, ?_⟩
    rw [consecutiveProduct_eq_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- The length residual after the `H ≥ 6000` tail. -/
def SylvesterSchurPrimeCountSixThousandResidualRectangle : Prop :=
  ∀ {N H : ℕ}, 101 ≤ H → H < 6_000 → H < N →
    N + 1 < sylvesterSchurPrimeCountFactorialThreshold H →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- Discharging the `101 ≤ H < 6000` rectangle proves unrestricted
Sylvester--Schur. -/
theorem sylvesterSchurConclusion_of_primeCountSixThousandResidualRectangle
    (hrect : SylvesterSchurPrimeCountSixThousandResidualRectangle) :
    SylvesterSchurConclusion := by
  intro N H hH hHN
  by_cases hsmallLength : H < 101
  · exact sylvesterSchurBelow_oneHundredOne hH hsmallLength hHN
  by_cases htail : 6_000 ≤ H
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_sixThousand
        htail hHN
  by_cases hsmallStart :
      N + 1 < sylvesterSchurPrimeCountFactorialThreshold H
  · exact hrect (by omega) (by omega) hHN hsmallStart
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCountFactorialThreshold_le
        hH hHN (Nat.le_of_not_gt hsmallStart)

end Tao2026
