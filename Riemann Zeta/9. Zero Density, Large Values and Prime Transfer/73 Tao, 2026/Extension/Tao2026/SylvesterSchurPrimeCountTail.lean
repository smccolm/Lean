import Tao2026.SylvesterSchurPrimeCountEnvelope

/-!
# Sharpened all-start Sylvester--Schur tail

The exact low-prime exponent `π(sqrt n)` makes the square-root/Hanson branch
small enough already at `H = 10000`.  On the far branch, an elementary
reduced-residue count modulo `210` gives `π(H) ≤ H/4`; since
`H < 64^3`, this supplies the binomial-growth baseline at `64H`.
-/

namespace Tao2026

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-- From `H=10000`, `log H` is at most `sqrt H / 10`. -/
theorem log_nat_le_sqrt_div_ten_of_primeCountTail
    {H : ℕ} (hH : 10_000 ≤ H) :
    Real.log H ≤ Real.sqrt H / 10 := by
  let X : ℝ := H
  let Y : ℝ := 10_000
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hYPos : 0 < Y := by positivity
  have hYX : Y ≤ X := by
    dsimp [Y, X]
    exact_mod_cast hH
  have hpowLower : (2 : ℝ) ^ 13 ≤ Y := by norm_num [Y]
  have hpowUpper : Y ≤ (2 : ℝ) ^ 14 := by norm_num [Y]
  have hlogLower : 13 * Real.log 2 ≤ Real.log Y := by
    calc
      13 * Real.log 2 = Real.log ((2 : ℝ) ^ 13) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log Y := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hYPos) hpowLower
  have hlogUpper : Real.log Y ≤ 14 * Real.log 2 := by
    calc
      Real.log Y ≤ Real.log ((2 : ℝ) ^ 14) :=
        Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hYPos)
          (Set.mem_Ioi.mpr (by positivity)) hpowUpper
      _ = 14 * Real.log 2 := by
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
  have hSqrtY : Real.sqrt Y = 100 := by
    have hsq : Y = (100 : ℝ) ^ 2 := by norm_num [Y]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hbase : Real.log Y / Real.sqrt Y < (1 / 10 : ℝ) := by
    rw [hSqrtY, div_lt_iff₀ (by positivity)]
    nlinarith [Real.log_two_lt_d9]
  have hratio : Real.log X / Real.sqrt X < (1 / 10 : ℝ) :=
    hanti.trans_lt hbase
  have hSqrtPos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXPos
  rw [div_lt_iff₀ hSqrtPos] at hratio
  dsimp [X] at hratio ⊢
  nlinarith

/-- A reduced-residue count modulo `210` gives `π(H) ≤ H/4` throughout the
new explicit tail. -/
theorem primeCounting_le_div_four_of_twoThousandTwoHundred_le
    {H : ℕ} (hH : 2_200 ≤ H) : H.primeCounting ≤ H / 4 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (show 210 ≤ H by omega)
  have hcount := Nat.primeCounting_add_le
    (a := 210) (k := 210) (by norm_num) (by norm_num) q
  have hpi : Nat.primeCounting 210 = 46 := by decide
  have hphi : Nat.totient 210 = 48 := by decide
  rw [hpi, hphi] at hcount
  omega

/-- A compact endpoint certificate below `690` and a reduced-residue count
modulo `210` thereafter give `π(m) ≤ m/4` for every `m ≥ 120`. -/
theorem primeCounting_le_div_four_of_oneTwenty_le
    {m : ℕ} (hm : 120 ≤ m) : m.primeCounting ≤ m / 4 := by
  by_cases hmUpper : m < 690
  · have hqLower : 30 ≤ m / 4 := by omega
    have hqUpper : m / 4 < 173 := by omega
    let qFin : Fin 173 := ⟨m / 4, hqUpper⟩
    have hfinite : ∀ q : Fin 173, 30 ≤ q.1 →
        (4 * q.1 + 3).primeCounting ≤ q.1 := by
      decide
    have hmLe : m ≤ 4 * (m / 4) + 3 := by omega
    exact (Nat.monotone_primeCounting hmLe).trans (by
      simpa [qFin] using hfinite qFin (by simpa [qFin] using hqLower))
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le
      (show 690 ≤ m by omega)
    have hcount := Nat.primeCounting_add_le
      (a := 210) (k := 690) (by norm_num) (by norm_num) q
    have hpi : Nat.primeCounting 690 = 124 := by decide
    have hphi : Nat.totient 210 = 48 := by decide
    rw [hpi, hphi] at hcount
    omega

/-- On `10000 ≤ H < 250000`, the exact prime count at upper index `64H`
fits below the binomial-growth margin. -/
theorem primeCountTail_primeCounting_log_baseline
    {H : ℕ} (hH : 2_200 ≤ H) (hHUpper : H < 250_000) :
    (H.primeCounting : ℝ) * Real.log (64 * H) <
      (H : ℝ) * Real.log 64 := by
  let X : ℝ := H
  let P : ℝ := H.primeCounting
  let L : ℝ := Real.log X
  let C : ℝ := Real.log 64
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hXOne : 1 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 1 < H)
  have hLPos : 0 < L := Real.log_pos hXOne
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  have hpiNat : H.primeCounting ≤ H / 4 :=
    primeCounting_le_div_four_of_twoThousandTwoHundred_le (by omega)
  have hpiFourNat : 4 * H.primeCounting ≤ H := by omega
  have hpiFour : 4 * P ≤ X := by
    dsimp [P, X]
    exact_mod_cast hpiFourNat
  have hHCube : H < 64 ^ 3 := by norm_num; omega
  have hlogCube : Real.log X < Real.log ((64 : ℝ) ^ 3) := by
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
  have htargetMul : X * (L + C) < X * (4 * C) := by
    exact mul_lt_mul_of_pos_left (by nlinarith) hXPos
  have hmain : P * (L + C) < X * C := by
    nlinarith [hmul, htargetMul]
  have hlogMul : Real.log (64 * H) = L + C := by
    dsimp [L, C, X]
    rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) hXPos.ne']
    ring
  rw [hlogMul]
  exact hmain

/-- The binomial-growth baseline at `64H` on the sharpened finite band. -/
theorem primeCountTail_choose_growth_baseline
    {H : ℕ} (hH : 2_200 ≤ H) (hHUpper : H < 250_000) :
    (64 * H) ^ (H + 1).primesBelow.card < (64 * H).choose H := by
  have hHPos : 0 < H := by omega
  have hbasePos : 0 < 64 * H := by positivity
  have hlog := primeCountTail_primeCounting_log_baseline hH hHUpper
  rw [card_primesBelow_succ_eq_primeCounting]
  have hlogMul :
      (H.primeCounting : ℝ) * Real.log (64 * H) +
          (H : ℝ) * Real.log H <
        (H : ℝ) * Real.log (64 * H) := by
    have hsplit : Real.log (64 * H) =
        Real.log 64 + Real.log H := by
      rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0)
        (by exact_mod_cast hHPos.ne' : (H : ℝ) ≠ 0)]
    rw [hsplit] at hlog ⊢
    nlinarith
  have hpowers :
      (64 * H) ^ H.primeCounting * H ^ H < (64 * H) ^ H :=
    nat_pow_mul_pow_lt_pow_of_log_lt hbasePos hHPos hbasePos (by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      exact hlogMul)
  have hlower :
      (64 * H) ^ H ≤ (64 * H).choose H * H ^ H :=
    pow_le_choose_mul_pow (by omega)
  exact Nat.lt_of_mul_lt_mul_right (hpowers.trans_le hlower)

/-- Binomial growth propagates from `64H` throughout the far branch of the
sharpened finite band. -/
theorem primeCountTail_choose_growth_of_baseline_le
    {n H : ℕ} (hH : 2_200 ≤ H) (hHUpper : H < 250_000)
    (hn : 64 * H ≤ n) :
    n ^ (H + 1).primesBelow.card < n.choose H := by
  apply choose_growth_of_le (m := 64 * H)
  · omega
  · rw [card_primesBelow_succ_eq_primeCounting]
    exact primeCounting_lt_self (by omega)
  · exact hn
  · exact primeCountTail_choose_growth_baseline hH hHUpper

/-- The prime-counted square-root/Hanson gap holds through upper index `64H`
already from `H=10000`. -/
theorem primeCountTail_near_gap
    {n H : ℕ} (hH : 10_000 ≤ H)
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
  have hSGe : (100 : ℝ) ≤ S := by
    dsimp [S]
    apply Real.le_sqrt_of_sq_le
    dsimp [X]
    exact_mod_cast hH
  have hSLe : S ≤ X / 100 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100)]
    nlinarith
  have hLLe : L ≤ S / 10 := by
    simpa [L, S, X] using
      log_nat_le_sqrt_div_ten_of_primeCountTail hH
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
  have hSqrtNatLower : 120 ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    nlinarith
  have hpiNat : n.sqrt.primeCounting ≤ n.sqrt / 4 :=
    primeCounting_le_div_four_of_oneTwenty_le hSqrtNatLower
  have hpiFourNat : 4 * n.sqrt.primeCounting ≤ n.sqrt := by omega
  have hpiFour : 4 * P ≤ (n.sqrt : ℝ) := by
    dsimp [P]
    exact_mod_cast hpiFourNat
  have hNatSqrt : (n.sqrt : ℝ) ≤ Real.sqrt Z := by
    simpa [Z] using (Real.nat_sqrt_le_real_sqrt (a := n))
  have hPLe : P ≤ 2 * S := by
    nlinarith
  have hLogZNonneg : 0 ≤ Real.log Z := Real.log_nonneg (by
    dsimp [Z]
    exact_mod_cast (by omega : 1 ≤ n))
  have hsub : P * Real.log n ≤ (285 / 1000 : ℝ) * X := by
    calc
      P * Real.log n = P * Real.log Z := by rfl
      _ ≤ (2 * S) * (L + 21 / 5) := by
        exact mul_le_mul hPLe hLogZ (by positivity) (by positivity)
      _ ≤ (285 / 1000 : ℝ) * X := by
        have hSL : S * L ≤ X / 10 := by
          calc
            S * L ≤ S * (S / 10) :=
              mul_le_mul_of_nonneg_left hLLe (Real.sqrt_nonneg X)
            _ = X / 10 := by rw [← hSSq]; ring
        nlinarith
  have hlogHSmall : L ≤ X / 1_000 := by
    calc
      L ≤ S / 10 := hLLe
      _ ≤ (X / 100) / 10 := by gcongr
      _ = X / 1_000 := by ring
  have hlogFour : (1386 / 1000 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlogThree : Real.log 3 < (1099 / 1000 : ℝ) :=
    Real.log_three_lt_d9.trans (by norm_num)
  have hHExtra : (1099 / 1000 : ℝ) ≤ X / 9_000 := by
    have hcast : (9_891 : ℝ) ≤ X := by
      dsimp [X]
      exact_mod_cast (show 9_891 ≤ H by omega)
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

/-- Effective all-start tail beginning at length `10000`. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail
    {N H : ℕ} (hH : 10_000 ≤ H) (hHN : H < N) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  by_cases hOldTail : 250_000 ≤ H
  · exact exists_large_prime_dvd_consecutiveProduct_of_explicit_tail
      hOldTail hHN
  have hHUpper : H < 250_000 := Nat.lt_of_not_ge hOldTail
  have hhalf : 2 * H ≤ N + H := by omega
  have hsumPos : 0 < N + H := by omega
  by_cases hnear : N + H ≤ 64 * H
  · have hgap := primeCountTail_near_gap hH hhalf hnear
    exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCounting_sqrt_three_gap
        (by omega) hHN hgap
  · have hgrowth :
        (N + H) ^ (H + 1).primesBelow.card < (N + H).choose H :=
      primeCountTail_choose_growth_of_baseline_le (by omega) hHUpper
        (Nat.le_of_not_ge hnear)
    obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
      exists_large_prime_dvd_choose_of_pow_card_lt
        (by omega : H ≤ N + H) hsumPos hgrowth
    refine ⟨p, hpPrime, hHltp, ?_⟩
    rw [consecutiveProduct_eq_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- The sharpened explicit residual rectangle. -/
def SylvesterSchurPrimeCountResidualRectangle : Prop :=
  ∀ {N H : ℕ}, 101 ≤ H → H < 10_000 → H < N →
    N + 1 < sylvesterSchurPrimeCountFactorialThreshold H →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- Discharging the sharpened rectangle proves unrestricted
Sylvester--Schur. -/
theorem sylvesterSchurConclusion_of_primeCountResidualRectangle
    (hrect : SylvesterSchurPrimeCountResidualRectangle) :
    SylvesterSchurConclusion := by
  intro N H hH hHN
  by_cases hsmallLength : H < 101
  · exact sylvesterSchurBelow_oneHundredOne hH hsmallLength hHN
  by_cases htail : 10_000 ≤ H
  · exact exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail htail hHN
  by_cases hsmallStart :
      N + 1 < sylvesterSchurPrimeCountFactorialThreshold H
  · exact hrect (by omega) (by omega) hHN hsmallStart
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCountFactorialThreshold_le
        hH hHN (Nat.le_of_not_gt hsmallStart)

end Tao2026
