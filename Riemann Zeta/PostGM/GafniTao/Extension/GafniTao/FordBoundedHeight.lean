import GafniTao.FordLowSigma
import GafniTao.FordExpCertificate

/-!
# Ford Lemma 7.1 on the bounded-height branch

This file treats the second alternative in Ford's Lemma 7.1 for the ordinary
Riemann zeta function.  The first step is the logarithmic version of the
finite-sum estimate (7.2), keeping the head term separate from the harmonic
tail.  Subsequent lemmas certify the two numerical height ranges used in the
source proof.
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem ford_harmonic_tail_le_log {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹) ≤ Real.log M := by
  have hanti : AntitoneOn (fun x : ℝ => x⁻¹)
      (Set.Icc ((1 : ℕ) : ℝ) (M : ℝ)) := by
    intro x hx y hy hxy
    have hxPos : 0 < x :=
      (show (0 : ℝ) < ((1 : ℕ) : ℝ) by norm_num).trans_le hx.1
    exact inv_anti₀ hxPos hxy
  have hsum := hanti.sum_le_integral_Ico hM
  rw [sum_Icc_two_eq_sum_Ico_succ (fun n => (n : ℝ)⁻¹) M]
  calc
    (∑ i ∈ Finset.Ico 1 M, ((i + 1 : ℕ) : ℝ)⁻¹) ≤
        ∫ x in (1 : ℝ)..(M : ℝ), x⁻¹ := by
      simpa only [Nat.cast_add, Nat.cast_one] using hsum
    _ = Real.log M := by
      have hMPos : (0 : ℝ) < M := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
      rw [integral_inv_of_pos (by norm_num) hMPos]
      norm_num

theorem ford_rpow_tail_le_power_mul_harmonic
    {sigma : ℝ} (hsigmaUpper : sigma ≤ 1) (M : ℕ) :
    (∑ n ∈ Finset.Icc 2 M, (n : ℝ) ^ (-sigma)) ≤
      (M : ℝ) ^ (1 - sigma) *
        (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹) := by
  have ha : 0 ≤ 1 - sigma := by linarith
  calc
    (∑ n ∈ Finset.Icc 2 M, (n : ℝ) ^ (-sigma)) =
        ∑ n ∈ Finset.Icc 2 M,
          (n : ℝ) ^ (1 - sigma) * (n : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnPos : 0 < (n : ℝ) := by
        have hnTwo : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        exact_mod_cast (show 0 < n by omega)
      rw [← Real.rpow_neg_one]
      rw [← Real.rpow_add hnPos]
      congr 1
      ring
    _ ≤ ∑ n ∈ Finset.Icc 2 M,
          (M : ℝ) ^ (1 - sigma) * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnM : (n : ℝ) ≤ M := by
        exact_mod_cast (Finset.mem_Icc.mp hn).2
      apply mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) hnM ha)
      positivity
    _ = (M : ℝ) ^ (1 - sigma) *
          (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹) := by
      rw [Finset.mul_sum]

theorem ford_rpow_partial_sum_le_one_add_power_log
    {sigma t : ℝ} (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ t) :
    (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℝ) ^ (-sigma)) ≤
      1 + t ^ (1 - sigma) * Real.log t := by
  have htPos : 0 < t := by linarith
  have hM : 1 ≤ fordFiniteEndpoint t :=
    fordFiniteEndpoint_pos (by linarith)
  have hMPos : (0 : ℝ) < fordFiniteEndpoint t := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hMle : (fordFiniteEndpoint t : ℝ) ≤ t :=
    fordFiniteEndpoint_le (by linarith)
  have ha : 0 ≤ 1 - sigma := by linarith
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hM,
    Finset.sum_insert (by simp)]
  norm_num
  have htail := ford_rpow_tail_le_power_mul_harmonic hsigmaUpper
    (fordFiniteEndpoint t)
  have hharm := ford_harmonic_tail_le_log hM
  have hlogMNonneg : 0 ≤ Real.log (fordFiniteEndpoint t : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  have hpowMNonneg :
      0 ≤ (fordFiniteEndpoint t : ℝ) ^ (1 - sigma) :=
    Real.rpow_nonneg (by positivity) _
  have hlogMono :
      Real.log (fordFiniteEndpoint t : ℝ) ≤ Real.log t :=
    Real.strictMonoOn_log.monotoneOn hMPos htPos hMle
  have hpowMono :
      (fordFiniteEndpoint t : ℝ) ^ (1 - sigma) ≤ t ^ (1 - sigma) :=
    Real.rpow_le_rpow hMPos.le hMle ha
  calc
    (∑ n ∈ Finset.Icc 2 (fordFiniteEndpoint t),
        (n : ℝ) ^ (-sigma)) ≤
        (fordFiniteEndpoint t : ℝ) ^ (1 - sigma) *
          (∑ n ∈ Finset.Icc 2 (fordFiniteEndpoint t), (n : ℝ)⁻¹) := htail
    _ ≤ (fordFiniteEndpoint t : ℝ) ^ (1 - sigma) *
          Real.log (fordFiniteEndpoint t : ℝ) := by gcongr
    _ ≤ t ^ (1 - sigma) * Real.log t := by
      exact mul_le_mul hpowMono hlogMono hlogMNonneg
        (Real.rpow_nonneg (by positivity) _)

theorem norm_fordPartialSum_le_one_add_power_log
    {sigma t : ℝ} (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ t) :
    ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      1 + t ^ (1 - sigma) * Real.log t := by
  calc
    ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
        ∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
          ‖(n : ℂ) ^ (-fordComplexHeight sigma t)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
          (n : ℝ) ^ (-sigma) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnPos : 0 < (n : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
      simp [fordComplexHeight]
    _ ≤ 1 + t ^ (1 - sigma) * Real.log t :=
      ford_rpow_partial_sum_le_one_add_power_log hsigmaUpper ht

theorem log_ten_lt_seven_thirds :
    Real.log 10 < (7 / 3 : ℝ) := by
  calc
    Real.log 10 = Real.log ((2 : ℝ) * 5) := by norm_num
    _ = Real.log 2 + Real.log 5 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    _ < 7 / 3 := by
      nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem log_le_fourteen_of_le_ten_pow_six
    {t : ℝ} (ht : 0 < t) (htUpper : t ≤ (10 : ℝ) ^ 6) :
    Real.log t ≤ 14 := by
  have htenPos : 0 < (10 : ℝ) ^ 6 := by positivity
  have hmono := Real.strictMonoOn_log.monotoneOn ht htenPos htUpper
  have hpow : Real.log ((10 : ℝ) ^ 6) = 6 * Real.log 10 := by
    rw [Real.log_pow]
    norm_num
  rw [hpow] at hmono
  nlinarith [log_ten_lt_seven_thirds]

theorem ten_pow_six_rpow_one_sixteenth_le_three :
    ((10 : ℝ) ^ 6) ^ (1 / 16 : ℝ) ≤ 3 := by
  have hbase : (0 : ℝ) ≤ (10 : ℝ) ^ 6 := by positivity
  have hpow : (10 : ℝ) ^ 6 ≤ (3 : ℝ) ^ 16 := by norm_num
  calc
    ((10 : ℝ) ^ 6) ^ (1 / 16 : ℝ) ≤
        ((3 : ℝ) ^ 16) ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow hbase hpow (by norm_num)
    _ = (((3 : ℝ) ^ (16 : ℝ)) ^ (1 / 16 : ℝ)) := by
      congr 1
      exact (Real.rpow_natCast (3 : ℝ) 16).symm
    _ = (3 : ℝ) ^ ((16 : ℝ) * (1 / 16 : ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ = 3 := by norm_num

theorem t_rpow_one_sub_sigma_le_three
    {sigma t : ℝ} (hsigmaLower : 15 / 16 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ t)
    (htUpper : t ≤ (10 : ℝ) ^ 6) :
    t ^ (1 - sigma) ≤ 3 := by
  have htOne : 1 ≤ t := by linarith
  have haNonneg : 0 ≤ 1 - sigma := by linarith
  have haUpper : 1 - sigma ≤ (1 / 16 : ℝ) := by linarith
  calc
    t ^ (1 - sigma) ≤ t ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le htOne haUpper
    _ ≤ ((10 : ℝ) ^ 6) ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow (by positivity) htUpper (by norm_num)
    _ ≤ 3 := ten_pow_six_rpow_one_sixteenth_le_three

theorem three_rpow_neg_half_le_three_fifths :
    (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 5 := by
  have hleft : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  apply (pow_le_pow_iff_left₀ hleft (by norm_num : (0 : ℝ) ≤ 3 / 5)
    (by norm_num : (2 : ℕ) ≠ 0)).mp
  calc
    ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 : ℕ) =
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
      exact (Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ))) 2).symm
    _ = (3 : ℝ) ^ (-(1 / 2 : ℝ) * 2) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ = 1 / 3 := by
      rw [show -(1 / 2 : ℝ) * 2 = -1 by norm_num,
        Real.rpow_neg_one]
      norm_num
    _ ≤ (3 / 5 : ℝ) ^ (2 : ℕ) := by norm_num

theorem t_rpow_neg_sigma_le_three_fifths
    {sigma t : ℝ} (hsigmaLower : 1 / 2 ≤ sigma) (ht : 3 ≤ t) :
    t ^ (-sigma) ≤ 3 / 5 := by
  have htOne : 1 ≤ t := by linarith
  calc
    t ^ (-sigma) ≤ t ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le htOne (by linarith)
    _ ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) ht (by norm_num)
    _ ≤ 3 / 5 := three_rpow_neg_half_le_three_fifths

theorem twenty_one_twentieth_le_log_rpow_two_thirds
    {t : ℝ} (ht : 3 ≤ t) :
    (21 / 20 : ℝ) ≤ Real.log t ^ (2 / 3 : ℝ) := by
  have htPos : 0 < t := by linarith
  have hlogLower : (109 / 100 : ℝ) ≤ Real.log t := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) htPos ht
    linarith [Real.log_three_gt_d9]
  have hlogNonneg : 0 ≤ Real.log t := by linarith
  have hright : 0 ≤ Real.log t ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg hlogNonneg _
  apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 21 / 20) hright
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hcube : (Real.log t ^ (2 / 3 : ℝ)) ^ (3 : ℕ) =
      Real.log t ^ (2 : ℕ) := by
    calc
      (Real.log t ^ (2 / 3 : ℝ)) ^ (3 : ℕ) =
          (Real.log t ^ (2 / 3 : ℝ)) ^ (3 : ℝ) := by
        exact (Real.rpow_natCast (Real.log t ^ (2 / 3 : ℝ)) 3).symm
      _ = Real.log t ^ ((2 / 3 : ℝ) * 3) := by
        rw [Real.rpow_mul hlogNonneg]
      _ = Real.log t ^ (2 : ℝ) := by norm_num
      _ = Real.log t ^ (2 : ℕ) := Real.rpow_natCast _ 2
  rw [hcube]
  nlinarith [sq_nonneg (Real.log t - 109 / 100)]

theorem norm_riemannZeta_le_ford_boundedHeight_small
    {sigma t : ℝ} (hsigmaLower : 15 / 16 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ t)
    (htUpper : t ≤ (10 : ℝ) ^ 6) :
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) := by
  have hsum := norm_fordPartialSum_le_one_add_power_log hsigmaUpper ht
  have hrem := norm_riemannZeta_sub_fordPartialSum_le_thirty
    (by linarith : 0 ≤ sigma) hsigmaUpper ht
  have htri :
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
        ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
            (n : ℂ) ^ (-fordComplexHeight sigma t)‖ +
          ‖riemannZeta (fordComplexHeight sigma t) -
            (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
              (n : ℂ) ^ (-fordComplexHeight sigma t))‖ := by
    have h := norm_add_le
      (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t))
      (riemannZeta (fordComplexHeight sigma t) -
        (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
          (n : ℂ) ^ (-fordComplexHeight sigma t)))
    simpa [add_sub_cancel_right] using h
  have hpow := t_rpow_one_sub_sigma_le_three
    hsigmaLower hsigmaUpper ht htUpper
  have hlog := log_le_fourteen_of_le_ten_pow_six (by linarith) htUpper
  have hlogNonneg : 0 ≤ Real.log t :=
    Real.log_nonneg (by linarith)
  have hneg := t_rpow_neg_sigma_le_three_fifths
    (by linarith : 1 / 2 ≤ sigma) ht
  have hleft : ‖riemannZeta (fordComplexHeight sigma t)‖ ≤ 61 := by
    calc
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
          ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
              (n : ℂ) ^ (-fordComplexHeight sigma t)‖ +
            ‖riemannZeta (fordComplexHeight sigma t) -
              (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
                (n : ℂ) ^ (-fordComplexHeight sigma t))‖ := htri
      _ ≤ (1 + t ^ (1 - sigma) * Real.log t) + 30 * t ^ (-sigma) := by
        gcongr
      _ ≤ 61 := by nlinarith
  have hpNonneg : 0 ≤ 4 * (1 - sigma) ^ (3 / 2 : ℝ) := by positivity
  have htpow : 1 ≤ t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.one_le_rpow (by linarith) hpNonneg
  have hlogpow := twenty_one_twentieth_le_log_rpow_two_thirds ht
  have hright :
      61 ≤ 58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) := by
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ t)
      (4 * (1 - sigma) ^ (3 / 2 : ℝ))]
  simpa [fordComplexHeight, mul_comm] using hleft.trans hright

/-- The exact one-variable optimizer used in Ford's bounded-height branch.
Writing `a = y²`, the gap from the target exponent factors as
`1/108 - (a - 4 a^(3/2)) = (6y-1)²(12y+1)/108`. -/
theorem ford_exponent_gap_le
    {a : ℝ} (ha : 0 ≤ a) :
    a - 4 * a ^ (3 / 2 : ℝ) ≤ 1 / 108 := by
  let y := Real.sqrt a
  have hy : 0 ≤ y := Real.sqrt_nonneg a
  have hySq : y ^ 2 = a := by
    dsimp [y]
    exact Real.sq_sqrt ha
  have hfactor : 0 ≤ (6 * y - 1) ^ 2 * (12 * y + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  rw [eta_three_halves_eq_mul_sqrt ha, ← Real.sqrt_eq_rpow]
  dsimp [y] at hySq hfactor ⊢
  nlinarith

/-- A fully rational Taylor certificate for the sole exponential constant
needed below. -/
theorem exp_one_hundred_seventy_five_over_eighty_one_le_nine :
    Real.exp (175 / 81 : ℝ) ≤ 9 := by
  have hx : |(175 / 243 : ℝ)| ≤ 1 := by norm_num
  have hbase := real_exp_le_fordExpTaylorUpper
    (n := 12) (x := (175 / 243 : ℝ)) (by norm_num) hx
  have hpow := pow_le_pow_left₀ (Real.exp_pos (175 / 243 : ℝ)).le hbase 3
  calc
    Real.exp (175 / 81 : ℝ) =
        Real.exp (175 / 243 : ℝ) ^ (3 : ℕ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    _ ≤ fordExpTaylorUpper 12 (175 / 243 : ℝ) ^ (3 : ℕ) := hpow
    _ ≤ 9 := by
      norm_num [fordExpTaylorUpper, Finset.sum_range_succ]

theorem log_le_seven_hundred_thirds_of_le_ten_pow_hundred
    {t : ℝ} (ht : 0 < t) (htUpper : t ≤ (10 : ℝ) ^ 100) :
    Real.log t ≤ 700 / 3 := by
  have hmono := Real.strictMonoOn_log.monotoneOn ht
    (by positivity : (0 : ℝ) < (10 : ℝ) ^ 100) htUpper
  have hpow : Real.log ((10 : ℝ) ^ 100) = 100 * Real.log 10 := by
    rw [Real.log_pow]
    norm_num
  rw [hpow] at hmono
  nlinarith [log_ten_lt_seven_thirds]

theorem t_rpow_ford_exponent_gap_le_nine
    {a t : ℝ} (ha : 0 ≤ a) (ht : 1 ≤ t)
    (htUpper : t ≤ (10 : ℝ) ^ 100) :
    t ^ (a - 4 * a ^ (3 / 2 : ℝ)) ≤ 9 := by
  have htPos : 0 < t := by linarith
  have hlogNonneg : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlogUpper :=
    log_le_seven_hundred_thirds_of_le_ten_pow_hundred htPos htUpper
  have hgap := ford_exponent_gap_le ha
  have hproduct :
      Real.log t * (a - 4 * a ^ (3 / 2 : ℝ)) ≤ 175 / 81 := by
    have hmul :
        0 ≤ Real.log t * (1 / 108 - (a - 4 * a ^ (3 / 2 : ℝ))) :=
      mul_nonneg hlogNonneg (by linarith)
    nlinarith
  rw [Real.rpow_def_of_pos htPos]
  exact (Real.exp_le_exp.mpr hproduct).trans
    exp_one_hundred_seventy_five_over_eighty_one_le_nine

theorem log_rpow_one_third_le_thirty_one_fifths
    {t : ℝ} (ht : 1 ≤ t) (htUpper : t ≤ (10 : ℝ) ^ 100) :
    Real.log t ^ (1 / 3 : ℝ) ≤ 31 / 5 := by
  have htPos : 0 < t := by linarith
  have hlogNonneg : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlogUpper :=
    log_le_seven_hundred_thirds_of_le_ten_pow_hundred htPos htUpper
  have hmono :
      Real.log t ^ (1 / 3 : ℝ) ≤ (700 / 3 : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hlogNonneg hlogUpper (by norm_num)
  have hleft : 0 ≤ (700 / 3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hconst : (700 / 3 : ℝ) ^ (1 / 3 : ℝ) ≤ 31 / 5 := by
    apply (pow_le_pow_iff_left₀ hleft (by norm_num : (0 : ℝ) ≤ 31 / 5)
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    calc
      ((700 / 3 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) =
          ((700 / 3 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := by
        exact (Real.rpow_natCast ((700 / 3 : ℝ) ^ (1 / 3 : ℝ)) 3).symm
      _ = (700 / 3 : ℝ) ^ ((1 / 3 : ℝ) * 3) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 700 / 3)]
      _ = 700 / 3 := by norm_num
      _ ≤ (31 / 5 : ℝ) ^ (3 : ℕ) := by norm_num
  exact hmono.trans hconst

theorem five_le_log_rpow_two_thirds_of_ten_pow_six_lt
    {t : ℝ} (ht : (10 : ℝ) ^ 6 < t) :
    5 ≤ Real.log t ^ (2 / 3 : ℝ) := by
  have htPos : 0 < t := by positivity
  have htenPos : (0 : ℝ) < (10 : ℝ) ^ 6 := by positivity
  have hmono := Real.strictMonoOn_log.monotoneOn htenPos htPos ht.le
  have hpow : Real.log ((10 : ℝ) ^ 6) = 6 * Real.log 10 := by
    rw [Real.log_pow]
    norm_num
  rw [hpow] at hmono
  have hlogLower : (69 / 5 : ℝ) ≤ Real.log t := by
    nlinarith [twenty_three_tenths_lt_log_ten]
  have hlogNonneg : 0 ≤ Real.log t := by linarith
  have hright : 0 ≤ Real.log t ^ (2 / 3 : ℝ) := by positivity
  apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 5) hright
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hcube : (Real.log t ^ (2 / 3 : ℝ)) ^ (3 : ℕ) =
      Real.log t ^ (2 : ℕ) := by
    calc
      (Real.log t ^ (2 / 3 : ℝ)) ^ (3 : ℕ) =
          (Real.log t ^ (2 / 3 : ℝ)) ^ (3 : ℝ) := by
        exact (Real.rpow_natCast (Real.log t ^ (2 / 3 : ℝ)) 3).symm
      _ = Real.log t ^ ((2 / 3 : ℝ) * 3) := by
        rw [Real.rpow_mul hlogNonneg]
      _ = Real.log t ^ (2 : ℝ) := by norm_num
      _ = Real.log t ^ (2 : ℕ) := Real.rpow_natCast _ 2
  rw [hcube]
  nlinarith [sq_nonneg (Real.log t - 69 / 5)]

theorem ford_power_log_factorization
    {a p t : ℝ} (ht : 1 < t) :
    t ^ a * Real.log t =
      (t ^ p * Real.log t ^ (2 / 3 : ℝ)) *
        (t ^ (a - p) * Real.log t ^ (1 / 3 : ℝ)) := by
  have htPos : 0 < t := by linarith
  have hlogPos : 0 < Real.log t := Real.log_pos ht
  have htFactor : t ^ a = t ^ p * t ^ (a - p) := by
    rw [← Real.rpow_add htPos]
    congr 1
    ring
  have hlogFactor : Real.log t =
      Real.log t ^ (2 / 3 : ℝ) * Real.log t ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hlogPos]
    norm_num
  calc
    t ^ a * Real.log t =
        (t ^ p * t ^ (a - p)) * Real.log t := by rw [htFactor]
    _ = (t ^ p * t ^ (a - p)) *
        (Real.log t ^ (2 / 3 : ℝ) * Real.log t ^ (1 / 3 : ℝ)) :=
      congrArg (fun x : ℝ => (t ^ p * t ^ (a - p)) * x) hlogFactor
    _ = (t ^ p * Real.log t ^ (2 / 3 : ℝ)) *
        (t ^ (a - p) * Real.log t ^ (1 / 3 : ℝ)) := by ring

theorem ford_main_term_le_large
    {sigma t : ℝ} (hsigmaUpper : sigma ≤ 1) (ht : 1 < t)
    (htUpper : t ≤ (10 : ℝ) ^ 100) :
    t ^ (1 - sigma) * Real.log t ≤
      (279 / 5 : ℝ) *
        (t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ (2 / 3 : ℝ)) := by
  have ha : 0 ≤ 1 - sigma := by linarith
  have htOne : 1 ≤ t := ht.le
  have hgap :
      t ^ ((1 - sigma) - 4 * (1 - sigma) ^ (3 / 2 : ℝ)) ≤ 9 :=
    t_rpow_ford_exponent_gap_le_nine ha htOne htUpper
  have hlog := log_rpow_one_third_le_thirty_one_fifths htOne htUpper
  have hgapNonneg :
      0 ≤ t ^ ((1 - sigma) - 4 * (1 - sigma) ^ (3 / 2 : ℝ)) := by
    positivity
  have hlogNonneg : 0 ≤ Real.log t ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg ht.le) _
  have hfactor :
      t ^ ((1 - sigma) - 4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (1 / 3 : ℝ) ≤ 279 / 5 := by
    nlinarith
  have hcoreNonneg :
      0 ≤ t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (Real.log_nonneg ht.le) _)
  calc
    t ^ (1 - sigma) * Real.log t =
        (t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ (2 / 3 : ℝ)) *
        (t ^ ((1 - sigma) - 4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ (1 / 3 : ℝ)) :=
      ford_power_log_factorization (a := 1 - sigma)
        (p := 4 * (1 - sigma) ^ (3 / 2 : ℝ)) ht
    _ ≤ (t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ (2 / 3 : ℝ)) * (279 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hfactor hcoreNonneg
    _ = (279 / 5 : ℝ) *
        (t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ (2 / 3 : ℝ)) := by ring

theorem ten_pow_six_rpow_neg_half_eq_one_thousandth :
    ((10 : ℝ) ^ 6) ^ (-(1 / 2 : ℝ)) = 1 / 1000 := by
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ 6)]
  have hroot : ((10 : ℝ) ^ 6) ^ (1 / 2 : ℝ) = 1000 := by
    calc
      ((10 : ℝ) ^ 6) ^ (1 / 2 : ℝ) =
          (((1000 : ℝ) ^ 2) ^ (1 / 2 : ℝ)) := by norm_num
      _ = ((1000 : ℝ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        congr 1
        exact (Real.rpow_natCast (1000 : ℝ) 2).symm
      _ = (1000 : ℝ) ^ ((2 : ℝ) * (1 / 2 : ℝ)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1000)]
      _ = 1000 := by norm_num
  rw [hroot]
  norm_num

theorem t_rpow_neg_sigma_le_one_thousandth
    {sigma t : ℝ} (hsigmaLower : 1 / 2 ≤ sigma)
    (ht : (10 : ℝ) ^ 6 < t) :
    t ^ (-sigma) ≤ 1 / 1000 := by
  have htOne : 1 ≤ t := by
    have : (1 : ℝ) < (10 : ℝ) ^ 6 := by norm_num
    linarith
  calc
    t ^ (-sigma) ≤ t ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le htOne (by linarith)
    _ ≤ ((10 : ℝ) ^ 6) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) ht.le (by norm_num)
    _ = 1 / 1000 := ten_pow_six_rpow_neg_half_eq_one_thousandth

theorem norm_riemannZeta_le_ford_boundedHeight_large
    {sigma t : ℝ} (hsigmaLower : 15 / 16 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : (10 : ℝ) ^ 6 < t)
    (htUpper : t ≤ (10 : ℝ) ^ 100) :
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) := by
  have htThree : 3 ≤ t := by
    have : (3 : ℝ) < (10 : ℝ) ^ 6 := by norm_num
    linarith
  have htOne : 1 < t := by linarith
  have hsum := norm_fordPartialSum_le_one_add_power_log hsigmaUpper htThree
  have hrem := norm_riemannZeta_sub_fordPartialSum_le_thirty
    (by linarith : 0 ≤ sigma) hsigmaUpper htThree
  have htri :
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
        ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
            (n : ℂ) ^ (-fordComplexHeight sigma t)‖ +
          ‖riemannZeta (fordComplexHeight sigma t) -
            (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
              (n : ℂ) ^ (-fordComplexHeight sigma t))‖ := by
    have h := norm_add_le
      (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t))
      (riemannZeta (fordComplexHeight sigma t) -
        (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
          (n : ℂ) ^ (-fordComplexHeight sigma t)))
    simpa [add_sub_cancel_right] using h
  let core : ℝ :=
    t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
      Real.log t ^ (2 / 3 : ℝ)
  have hpNonneg : 0 ≤ 4 * (1 - sigma) ^ (3 / 2 : ℝ) := by positivity
  have htpow : 1 ≤ t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.one_le_rpow (by linarith) hpNonneg
  have hlogpow := five_le_log_rpow_two_thirds_of_ten_pow_six_lt ht
  have hlogpowNonneg : 0 ≤ Real.log t ^ (2 / 3 : ℝ) := by
    exact Real.rpow_nonneg (Real.log_nonneg htOne.le) _
  have hcore : 5 ≤ core := by
    dsimp [core]
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ t)
      (4 * (1 - sigma) ^ (3 / 2 : ℝ))]
  have hmain : t ^ (1 - sigma) * Real.log t ≤ (279 / 5 : ℝ) * core := by
    simpa [core] using ford_main_term_le_large hsigmaUpper htOne htUpper
  have hneg := t_rpow_neg_sigma_le_one_thousandth
    (by linarith : 1 / 2 ≤ sigma) ht
  have hleft :
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
        1 + (279 / 5 : ℝ) * core + 3 / 100 := by
    calc
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
          ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
              (n : ℂ) ^ (-fordComplexHeight sigma t)‖ +
            ‖riemannZeta (fordComplexHeight sigma t) -
              (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
                (n : ℂ) ^ (-fordComplexHeight sigma t))‖ := htri
      _ ≤ (1 + t ^ (1 - sigma) * Real.log t) + 30 * t ^ (-sigma) := by
        gcongr
      _ ≤ 1 + (279 / 5 : ℝ) * core + 3 / 100 := by nlinarith
  have hright :
      1 + (279 / 5 : ℝ) * core + 3 / 100 ≤ 58.1 * core := by
    nlinarith
  have hzetaEq :
      riemannZeta (fordComplexHeight sigma t) =
        riemannZeta (sigma + Complex.I * t) := by
    congr 1
    simp [fordComplexHeight, mul_comm]
  calc
    ‖riemannZeta (sigma + Complex.I * t)‖ =
        ‖riemannZeta (fordComplexHeight sigma t)‖ := by rw [hzetaEq]
    _ ≤ 58.1 * core := hleft.trans hright
    _ = 58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) := by
      dsimp [core]
      ring

theorem norm_riemannZeta_le_ford_boundedHeight
    {sigma t : ℝ} (hsigmaLower : 15 / 16 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ t)
    (htUpper : t ≤ (10 : ℝ) ^ 100) :
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) := by
  by_cases hsmall : t ≤ (10 : ℝ) ^ 6
  · exact norm_riemannZeta_le_ford_boundedHeight_small
      hsigmaLower hsigmaUpper ht hsmall
  · exact norm_riemannZeta_le_ford_boundedHeight_large
      hsigmaLower hsigmaUpper (lt_of_not_ge hsmall) htUpper

/-- The two unconditional alternatives in Ford's Lemma 7.1 for ordinary
Riemann zeta: either `σ ≤ 15/16`, or the height is bounded by `10^100`. -/
theorem norm_riemannZeta_le_ford_lemma71_unconditional_ranges
    {sigma t : ℝ} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ t)
    (hrange : sigma ≤ 15 / 16 ∨ t ≤ (10 : ℝ) ^ 100) :
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) := by
  rcases hrange with hsigma | htBounded
  · exact norm_riemannZeta_le_ford_lowSigma
      hsigmaLower hsigma ht
  · by_cases hsigmaCase : sigma ≤ 15 / 16
    · exact norm_riemannZeta_le_ford_lowSigma
        hsigmaLower hsigmaCase ht
    · exact norm_riemannZeta_le_ford_boundedHeight
        (le_of_not_ge hsigmaCase) hsigmaUpper ht htBounded

#print axioms ford_harmonic_tail_le_log
#print axioms ford_rpow_tail_le_power_mul_harmonic
#print axioms ford_rpow_partial_sum_le_one_add_power_log
#print axioms norm_fordPartialSum_le_one_add_power_log
#print axioms log_ten_lt_seven_thirds
#print axioms norm_riemannZeta_le_ford_boundedHeight_small
#print axioms ford_exponent_gap_le
#print axioms exp_one_hundred_seventy_five_over_eighty_one_le_nine
#print axioms t_rpow_ford_exponent_gap_le_nine
#print axioms log_rpow_one_third_le_thirty_one_fifths
#print axioms five_le_log_rpow_two_thirds_of_ten_pow_six_lt
#print axioms ford_main_term_le_large
#print axioms t_rpow_neg_sigma_le_one_thousandth
#print axioms norm_riemannZeta_le_ford_boundedHeight_large
#print axioms norm_riemannZeta_le_ford_boundedHeight
#print axioms norm_riemannZeta_le_ford_lemma71_unconditional_ranges

end

end GafniTao
