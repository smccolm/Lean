import Tao2026.SylvesterSchurCentralTail
import Tao2026.SmoothNumberPrimeSum

/-!
# An effective all-start Sylvester--Schur tail

The qualitative PNT argument in `VeryBadIntervals` gives an unspecified
large-length threshold.  This file supplies a completely explicit elementary
threshold.  Up to upper index `64H`, the square-root/Hanson envelope is
absorbed directly.  At `64H`, Mathlib's explicit Chebyshev bound proves the
small-prime binomial-growth inequality, and the existing monotonicity theorem
propagates it to every larger upper index.
-/

namespace Tao2026

/-- On the effective tail, `log H` is at most one fortieth of `sqrt H`. -/
theorem log_nat_le_sqrt_div_forty_of_explicitTail
    {H : ℕ} (hH : 250_000 ≤ H) :
    Real.log H ≤ Real.sqrt H / 40 := by
  let X : ℝ := H
  let Y : ℝ := 250_000
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hYPos : 0 < Y := by positivity
  have hYX : Y ≤ X := by
    dsimp [Y, X]
    exact_mod_cast hH
  have hpowLower : (2 : ℝ) ^ 17 ≤ Y := by norm_num [Y]
  have hpowUpper : Y ≤ (2 : ℝ) ^ 18 := by norm_num [Y]
  have hlogLower : 17 * Real.log 2 ≤ Real.log Y := by
    calc
      17 * Real.log 2 = Real.log ((2 : ℝ) ^ 17) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log Y := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hYPos) hpowLower
  have hlogUpper : Real.log Y ≤ 18 * Real.log 2 := by
    calc
      Real.log Y ≤ Real.log ((2 : ℝ) ^ 18) :=
        Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hYPos)
          (Set.mem_Ioi.mpr (by positivity)) hpowUpper
      _ = 18 * Real.log 2 := by
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
  have hSqrtY : Real.sqrt Y = 500 := by
    have hsq : Y = (500 : ℝ) ^ 2 := by norm_num [Y]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hbase : Real.log Y / Real.sqrt Y < (1 / 40 : ℝ) := by
    rw [hSqrtY, div_lt_iff₀ (by positivity)]
    nlinarith [Real.log_two_lt_d9]
  have hratio : Real.log X / Real.sqrt X < (1 / 40 : ℝ) :=
    hanti.trans_lt hbase
  have hSqrtPos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXPos
  rw [div_lt_iff₀ hSqrtPos] at hratio
  dsimp [X] at hratio ⊢
  nlinarith

/-- At the explicit cutoff, the Chebyshev prime-count contribution at upper
index `64H` fits strictly below the available logarithmic gap. -/
theorem explicitTail_primeCounting_log_baseline
    {H : ℕ} (hH : 250_000 ≤ H) :
    (H.primeCounting : ℝ) * Real.log (64 * H) <
      (H : ℝ) * Real.log 64 := by
  let X : ℝ := H
  let S : ℝ := Real.sqrt X
  let L : ℝ := Real.log X
  let C : ℝ := Real.log 64
  have hHBig : 250_000 ≤ H := hH
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hXOne : 1 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 1 < H)
  have hLPos : 0 < L := by exact Real.log_pos hXOne
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlog64 : C = 6 * Real.log 2 := by
    dsimp [C]
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num]
    rw [Real.log_pow]
    norm_num
  have hCUpper : C < (21 / 5 : ℝ) := by
    rw [hlog64]
    nlinarith [Real.log_two_lt_d9]
  have hCLower : (41 / 10 : ℝ) < C := by
    rw [hlog64]
    nlinarith [Real.log_two_gt_d9]
  have hlogFourUpper : Real.log 4 < (7 / 5 : ℝ) := by
    rw [hlogFour]
    nlinarith [Real.log_two_lt_d9]
  have hXBound : (2 : ℝ) ^ 17 ≤ X := by
    dsimp [X]
    exact_mod_cast ((by norm_num : 2 ^ 17 ≤ 250_000).trans hH)
  have hlogMono : Real.log ((2 : ℝ) ^ 17) ≤ L := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr hXPos
    · exact hXBound
  have hL : (11 : ℝ) < L := by
    have hpowLog : Real.log ((2 : ℝ) ^ 17) = 17 * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    rw [hpowLog] at hlogMono
    nlinarith [Real.log_two_gt_d9]
  have hSNonneg : 0 ≤ S := Real.sqrt_nonneg X
  have hSSq : S * S = X := Real.mul_self_sqrt hXPos.le
  have hSGe : (500 : ℝ) ≤ S := by
    dsimp [S]
    apply Real.le_sqrt_of_sq_le
    dsimp [X]
    exact_mod_cast hHBig
  have hSLe : S ≤ X / 500 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 500)]
    nlinarith
  have hLogLe : L ≤ S / 40 := by
    simpa [L, S, X] using log_nat_le_sqrt_div_forty_of_explicitTail hH
  have hSL : S * L ≤ X / 40 := by
    calc
      S * L ≤ S * (S / 40) :=
        mul_le_mul_of_nonneg_left hLogLe (Real.sqrt_nonneg X)
      _ = X / 40 := by rw [← hSSq]; ring
  have hPrime := primeCounting_cast_le_chebyshevPrimeCountingMajorant
    (n := H) (by omega : 2 ≤ H)
  have hPrime' :
      (H.primeCounting : ℝ) ≤
        2 * Real.log 4 * X / L + S := by
    rw [chebyshevPrimeCountingMajorant,
      Real.log_sqrt (by exact_mod_cast (Nat.zero_le H))] at hPrime
    dsimp [X, S, L] at hPrime ⊢
    convert hPrime using 1
    field_simp
  have hA : Real.log (64 * H) = L + C := by
    dsimp [L, C, X]
    rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) hXPos.ne']
    ring
  rw [hA]
  have hANonneg : 0 ≤ L + C := by positivity
  have hpiA :
      (H.primeCounting : ℝ) * (L + C) ≤
        (2 * Real.log 4 * X / L + S) * (L + C) :=
    mul_le_mul_of_nonneg_right hPrime' hANonneg
  have hfirst :
      (2 * Real.log 4 * X / L) * (L + C) <
        (98 / 25 : ℝ) * X := by
    have hXC : X * C / L < (2 / 5 : ℝ) * X := by
      rw [div_lt_iff₀ hLPos, div_mul_eq_mul_div]
      have : C * 5 < 2 * L := by nlinarith
      nlinarith
    have hmain : 2 * Real.log 4 * X < (14 / 5 : ℝ) * X := by
      nlinarith
    have hcoeff : 2 * Real.log 4 < (14 / 5 : ℝ) := by nlinarith
    have hXCPos : 0 < X * C / L := by positivity
    calc
      (2 * Real.log 4 * X / L) * (L + C) =
          2 * Real.log 4 * X + 2 * Real.log 4 * (X * C / L) := by
        field_simp
      _ < (14 / 5 : ℝ) * X +
          (14 / 5 : ℝ) * (X * C / L) := by
        exact add_lt_add hmain (mul_lt_mul_of_pos_right hcoeff hXCPos)
      _ < (14 / 5 : ℝ) * X +
          (14 / 5 : ℝ) * ((2 / 5 : ℝ) * X) := by
        simpa [add_comm] using add_lt_add_left
          (mul_lt_mul_of_pos_left hXC
            (by norm_num : (0 : ℝ) < 14 / 5)) ((14 / 5 : ℝ) * X)
      _ = (98 / 25 : ℝ) * X := by ring
  have hsqrtPart : S * (L + C) < (17 / 500 : ℝ) * X := by
    have hSC : S * C < (21 / 5 : ℝ) * (X / 500) := by
      nlinarith
    nlinarith
  have htotal :
      (2 * Real.log 4 * X / L + S) * (L + C) <
        (1977 / 500 : ℝ) * X := by
    nlinarith
  have htarget : (1977 / 500 : ℝ) * X < X * C := by
    have : (0 : ℝ) < X := hXPos
    nlinarith
  exact hpiA.trans_lt (htotal.trans htarget)

/-- The binomial coefficient at upper index `64H` exceeds the complete
small-prime factorization envelope. -/
theorem explicitTail_choose_growth_baseline
    {H : ℕ} (hH : 250_000 ≤ H) :
    (64 * H) ^ (H + 1).primesBelow.card < (64 * H).choose H := by
  have hHPos : 0 < H := by omega
  have hbasePos : 0 < 64 * H := by positivity
  have hlog := explicitTail_primeCounting_log_baseline hH
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

/-- Binomial growth propagates from `64H` to every larger upper index. -/
theorem explicitTail_choose_growth_of_baseline_le
    {n H : ℕ} (hH : 250_000 ≤ H)
    (hn : 64 * H ≤ n) :
    n ^ (H + 1).primesBelow.card < n.choose H := by
  apply choose_growth_of_le (m := 64 * H)
  · omega
  · rw [card_primesBelow_succ_eq_primeCounting]
    exact primeCounting_lt_self (by omega)
  · exact hn
  · exact explicitTail_choose_growth_baseline hH

/-- Convert a strict logarithmic comparison into a natural inequality for a
product of three powers. -/
theorem nat_three_pow_product_lt_of_log_lt
    {a b c d r s t u : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d)
    (hlog : (r : ℝ) * Real.log a + (s : ℝ) * Real.log b +
      (t : ℝ) * Real.log c < (u : ℝ) * Real.log d) :
    a ^ r * b ^ s * c ^ t < d ^ u := by
  have haReal : (0 : ℝ) < a := by exact_mod_cast ha
  have hbReal : (0 : ℝ) < b := by exact_mod_cast hb
  have hcReal : (0 : ℝ) < c := by exact_mod_cast hc
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hreal :
      (a : ℝ) ^ r * (b : ℝ) ^ s * (c : ℝ) ^ t < (d : ℝ) ^ u := by
    rw [← Real.log_lt_log_iff
      (mul_pos (mul_pos (pow_pos haReal r) (pow_pos hbReal s))
        (pow_pos hcReal t)) (pow_pos hdReal u),
      Real.log_mul
        (mul_ne_zero (pow_ne_zero r haReal.ne') (pow_ne_zero s hbReal.ne'))
        (pow_ne_zero t hcReal.ne'),
      Real.log_mul (pow_ne_zero r haReal.ne') (pow_ne_zero s hbReal.ne'),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    exact hlog
  exact_mod_cast hreal

/-- The square-root/Hanson gap holds uniformly up to upper index `64H`. -/
theorem explicitTail_near_gap
    {n H : ℕ} (hH : 250_000 ≤ H)
    (hhalf : 2 * H ≤ n) (hn : n ≤ 64 * H) :
    H * (n ^ n.sqrt * 3 ^ (H + 1)) < 4 ^ H := by
  let X : ℝ := H
  let Z : ℝ := n
  let S : ℝ := Real.sqrt X
  let L : ℝ := Real.log X
  have hHBig : 250_000 ≤ H := hH
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hZPos : 0 < Z := by
    dsimp [Z]
    exact_mod_cast (by omega : 0 < n)
  have hSSq : S * S = X := Real.mul_self_sqrt hXPos.le
  have hSGe : (500 : ℝ) ≤ S := by
    dsimp [S]
    apply Real.le_sqrt_of_sq_le
    dsimp [X]
    exact_mod_cast hHBig
  have hSLe : S ≤ X / 500 := by
    nlinarith
  have hLLe : L ≤ S / 40 := by
    simpa [L, S, X] using
      log_nat_le_sqrt_div_forty_of_explicitTail hH
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
  have hLogZ : Real.log Z ≤ L + 5 := by
    calc
      Real.log Z ≤ Real.log (64 * X) :=
        Real.strictMonoOn_log.monotoneOn hZPos
          (mul_pos (by norm_num) hXPos) hZLe
      _ = Real.log 64 + L := by
        dsimp [L]
        rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) hXPos.ne']
      _ ≤ L + 5 := by
        have hlog64 : Real.log 64 = 6 * Real.log 2 := by
          rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
          norm_num
        rw [hlog64]
        nlinarith [Real.log_two_lt_d9]
  have hLogZNonneg : 0 ≤ Real.log Z := Real.log_nonneg (by
    dsimp [Z]
    exact_mod_cast (by omega : 1 ≤ n))
  have hLNonneg : 0 ≤ L := Real.log_nonneg (by
    dsimp [X]
    exact_mod_cast (by omega : 1 ≤ H))
  have hNatSqrt : (n.sqrt : ℝ) ≤ Real.sqrt Z := by
    simpa [Z] using (Real.nat_sqrt_le_real_sqrt (a := n))
  have hsub : (n.sqrt : ℝ) * Real.log n ≤ (281 / 1000 : ℝ) * X := by
    calc
      (n.sqrt : ℝ) * Real.log n ≤ Real.sqrt Z * Real.log Z := by
        dsimp [Z]
        exact mul_le_mul hNatSqrt le_rfl hLogZNonneg
          (by positivity)
      _ ≤ (8 * S) * (L + 5) := by
        exact mul_le_mul hSqrtZ hLogZ hLogZNonneg
          (by positivity)
      _ ≤ (281 / 1000 : ℝ) * X := by
        have hSL : S * L ≤ X / 40 := by
          calc
            S * L ≤ S * (S / 40) :=
              mul_le_mul_of_nonneg_left hLLe (Real.sqrt_nonneg X)
            _ = X / 40 := by rw [← hSSq]; ring
        nlinarith
  have hlogHSmall : L ≤ X / 20_000 := by
    calc
      L ≤ S / 40 := hLLe
      _ ≤ (X / 500) / 40 := by gcongr
      _ = X / 20_000 := by ring
  have hlogFour : (1386 / 1000 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlogThree : Real.log 3 < (1099 / 1000 : ℝ) :=
    Real.log_three_lt_d9.trans (by norm_num)
  have hHExtra : (1099 / 1000 : ℝ) ≤ X / 200_000 := by
    have hcast : (219_800 : ℝ) ≤ X := by
      dsimp [X]
      exact_mod_cast (show 219_800 ≤ H by omega)
    nlinarith
  have hlogGap :
      (1 : ℝ) * Real.log H + (n.sqrt : ℝ) * Real.log n +
          (H + 1 : ℕ) * Real.log 3 <
        (H : ℝ) * Real.log 4 := by
    norm_num only [one_mul, Nat.cast_add, Nat.cast_one]
    dsimp [L, X] at hlogHSmall hHExtra ⊢
    nlinarith
  simpa [mul_assoc] using
    (nat_three_pow_product_lt_of_log_lt
      (a := H) (b := n) (c := 3) (d := 4)
      (r := 1) (s := n.sqrt) (t := H + 1) (u := H)
      (by omega) (by omega) (by norm_num) (by norm_num) (by
        simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.cast_add] using hlogGap))

/-- Effective all-start Sylvester--Schur tail: every interval length at least
`250000` has a prime divisor above its length, uniformly in the start. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_explicit_tail
    {N H : ℕ} (hH : 250_000 ≤ H) (hHN : H < N) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  have hhalf : 2 * H ≤ N + H := by omega
  have hsumPos : 0 < N + H := by omega
  by_cases hnear : N + H ≤ 64 * H
  · have hgap := explicitTail_near_gap hH hhalf hnear
    exact exists_large_prime_dvd_consecutiveProduct_of_sqrt_three_gap
      (by omega) hHN hgap
  · have hgrowth :
        (N + H) ^ (H + 1).primesBelow.card < (N + H).choose H :=
      explicitTail_choose_growth_of_baseline_le hH (Nat.le_of_not_ge hnear)
    obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
      exists_large_prime_dvd_choose_of_pow_card_lt
        (by omega : H ≤ N + H) hsumPos hgrowth
    refine ⟨p, hpPrime, hHltp, ?_⟩
    rw [consecutiveProduct_eq_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- The fully explicit finite residual after combining the proof below length
`101`, the exact prime-count factorial cutoff, and the effective tail. -/
def SylvesterSchurExplicitResidualRectangle : Prop :=
  ∀ {N H : ℕ}, 101 ≤ H → H < 250_000 → H < N →
    N + 1 < sylvesterSchurPrimeCountFactorialThreshold H →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- Discharging the explicit residual rectangle proves unrestricted
Sylvester--Schur.  Unlike the earlier PNT reduction, both length endpoints are
now concrete. -/
theorem sylvesterSchurConclusion_of_explicitResidualRectangle
    (hrect : SylvesterSchurExplicitResidualRectangle) :
    SylvesterSchurConclusion := by
  intro N H hH hHN
  by_cases hsmallLength : H < 101
  · exact sylvesterSchurBelow_oneHundredOne hH hsmallLength hHN
  by_cases htail : 250_000 ≤ H
  · exact exists_large_prime_dvd_consecutiveProduct_of_explicit_tail htail hHN
  by_cases hsmallStart :
      N + 1 < sylvesterSchurPrimeCountFactorialThreshold H
  · exact hrect (by omega) (by omega) hHN hsmallStart
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCountFactorialThreshold_le
        hH hHN (Nat.le_of_not_gt hsmallStart)

end Tao2026
