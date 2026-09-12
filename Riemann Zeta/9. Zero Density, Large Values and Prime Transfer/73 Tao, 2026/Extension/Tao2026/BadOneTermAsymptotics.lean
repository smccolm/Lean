import Mathlib.NumberTheory.Bertrand
import Tao2026.SmoothNumberStability

/-!
# Asymptotics for Tao's one-term bad set

This module begins the finite summation of Proposition 2.1 over the exact
prime-indexed identity for `badOneTermCount`.  The first layer provides the
diagonal uniformity and perturbation lemmas needed to apply the sequence-form
critical smooth-number estimates uniformly to primes in moving `z`-bands.
-/

open Filter Topology Finset

namespace Tao2026

/-- The smooth scale is subpolynomial on the ambient `x` scale. -/
theorem tendsto_log_taoZ_div_log_nat_zero :
    Tendsto (fun x : ℕ => Real.log (taoZ x) / Real.log x)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℕ => (taoUZero x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_taoUZero_atTop
  apply hinv.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hx hiter
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogz : 0 < Real.log (taoZ x) := by
    rw [log_taoZ]
    positivity
  rw [← log_div_log_taoZ_eq_taoUZero hlogx hiter]
  field_simp

/-- Upper endpoint for the fixed dyadic prime block centered at `taoZ`. -/
noncomputable def taoOneTermCriticalPrimeBandTop (x : ℕ) : ℕ :=
  ⌈2 * taoZ x⌉₊

/-- The prime block `(ceil(2z)/2, ceil(2z)]`, used for the lower half of the
one-term bad-set asymptotic. -/
noncomputable def taoOneTermCriticalPrimeBand (x : ℕ) : Finset ℕ :=
  cepDyadicPrimeBlock (taoOneTermCriticalPrimeBandTop x)

/-- Every prime in the canonical lower block lies between `z` and `3z` once
`z>1`. The slack absorbs the natural ceiling exactly. -/
theorem eventually_mem_taoOneTermCriticalPrimeBand_bounds :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ taoOneTermCriticalPrimeBand x,
      p.Prime ∧ taoZ x < (p : ℝ) ∧ (p : ℝ) < 3 * taoZ x := by
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hz p hp
  have hpData := mem_cepDyadicPrimeBlock_iff.mp hp
  have hceilLow : 2 * taoZ x ≤ (taoOneTermCriticalPrimeBandTop x : ℝ) := by
    exact Nat.le_ceil _
  have htopLt : taoOneTermCriticalPrimeBandTop x < 2 * p := by
    simpa only [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mp hpData.2.1
  have htopLtReal : (taoOneTermCriticalPrimeBandTop x : ℝ) < 2 * p := by
    exact_mod_cast htopLt
  have hpLower : taoZ x < (p : ℝ) := by linarith
  have hceilUpper : (taoOneTermCriticalPrimeBandTop x : ℝ) <
      2 * taoZ x + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hpUpper : (p : ℝ) < 3 * taoZ x := by
    have hpTop : (p : ℝ) ≤ taoOneTermCriticalPrimeBandTop x := by
      exact_mod_cast hpData.2.2
    linarith
  exact ⟨hpData.1, hpLower, hpUpper⟩

/-- Dividing the ambient cutoff by the square of a positive subpolynomial
natural parameter preserves logarithmic exponent one. -/
theorem tendsto_log_natDiv_sq_div_log_nat_one
    {P : ℕ → ℕ}
    (hPpos : ∀ᶠ x : ℕ in atTop, 0 < P x)
    (hPsmall : Tendsto (fun x =>
      Real.log (P x : ℝ) / Real.log x) atTop (𝓝 0)) :
    Tendsto (fun x => Real.log (x / P x ^ 2 : ℕ) / Real.log x)
      atTop (𝓝 1) := by
  have hlogx : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun x : ℕ =>
      1 - 2 * (Real.log (P x : ℝ) / Real.log x) -
        Real.log 2 / Real.log x) atTop (𝓝 1) := by
    have hconst : Tendsto (fun x : ℕ => Real.log 2 / Real.log x)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlogx
    convert (tendsto_const_nhds.sub (tendsto_const_nhds.mul hPsmall)).sub
      hconst using 1
    all_goals norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds
  · filter_upwards [hPpos, hPsmall.eventually (Iio_mem_nhds (show 0 < (1 : ℝ) / 4 by norm_num)),
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hpPos hpRatio hx
    have hlogxPos : 0 < Real.log x := Real.log_pos hx
    have hxNat : 0 < x := by exact_mod_cast (lt_trans zero_lt_one hx)
    have hpRealPos : (0 : ℝ) < P x := by exact_mod_cast hpPos
    have hlogpSq : Real.log ((P x : ℝ) ^ 2) < Real.log x := by
      rw [Real.log_pow]
      norm_num
      have := (div_lt_iff₀ hlogxPos).mp hpRatio
      nlinarith
    have hpSqLtReal : ((P x : ℝ) ^ 2) < x := by
      have hexp := Real.exp_lt_exp.mpr hlogpSq
      rw [Real.exp_log (pow_pos hpRealPos 2),
        Real.exp_log (by exact_mod_cast hxNat)] at hexp
      exact hexp
    have hpSqLe : P x ^ 2 ≤ x := by exact_mod_cast hpSqLtReal.le
    have hqPos : 0 < x / P x ^ 2 :=
      Nat.div_pos hpSqLe (pow_pos hpPos 2)
    have hquot : (x : ℝ) / (P x ^ 2 : ℕ) ≤
        2 * (x / P x ^ 2 : ℕ) :=
      cast_div_le_two_mul_natDiv (pow_pos hpPos 2) hpSqLe
    have hquotPos : 0 < (x : ℝ) / (P x ^ 2 : ℕ) :=
      div_pos (by exact_mod_cast hxNat)
        (by exact_mod_cast (pow_pos hpPos 2))
    have htwoQPos : 0 < (2 : ℝ) * (x / P x ^ 2 : ℕ) := by positivity
    have hlogs := Real.strictMonoOn_log.monotoneOn hquotPos htwoQPos hquot
    rw [Real.log_div (by exact_mod_cast (show x ≠ 0 by omega))
          (by exact_mod_cast (show P x ^ 2 ≠ 0 by positivity)),
      Nat.cast_pow, Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by exact_mod_cast hqPos.ne')] at hlogs
    rw [show 1 - 2 * (Real.log (P x : ℝ) / Real.log x) -
        Real.log 2 / Real.log x =
      (Real.log x - 2 * Real.log (P x : ℝ) - Real.log 2) /
        Real.log x by field_simp]
    rw [div_le_div_iff_of_pos_right hlogxPos]
    linarith
  · filter_upwards [hPpos,
      hPsmall.eventually (Iio_mem_nhds (show 0 < (1 : ℝ) / 4 by norm_num)),
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hpPos hpRatio hx
    have hlogxPos : 0 < Real.log x := Real.log_pos hx
    have hxNat : 0 < x := by exact_mod_cast (lt_trans zero_lt_one hx)
    have hqPos : 0 < x / P x ^ 2 := by
      have hpRealPos : (0 : ℝ) < P x := by exact_mod_cast hpPos
      have hlogpSq : Real.log ((P x : ℝ) ^ 2) < Real.log x := by
        rw [Real.log_pow]
        norm_num
        have := (div_lt_iff₀ hlogxPos).mp hpRatio
        nlinarith
      have hpSqLtReal : ((P x : ℝ) ^ 2) < x := by
        have hexp := Real.exp_lt_exp.mpr hlogpSq
        rw [Real.exp_log (pow_pos hpRealPos 2),
          Real.exp_log (by exact_mod_cast hxNat)] at hexp
        exact hexp
      have hpSqLe : P x ^ 2 ≤ x := by exact_mod_cast hpSqLtReal.le
      exact Nat.div_pos hpSqLe (pow_pos hpPos 2)
    have hqLe : x / P x ^ 2 ≤ x := Nat.div_le_self _ _
    have hlogLe : Real.log (x / P x ^ 2 : ℕ) ≤ Real.log x :=
      Real.strictMonoOn_log.monotoneOn
        (show (0 : ℝ) < (x / P x ^ 2 : ℕ) by exact_mod_cast hqPos)
        (show (0 : ℝ) < x by exact_mod_cast hxNat)
        (by exact_mod_cast hqLe)
    exact (div_le_iff₀ hlogxPos).2 (by simpa using hlogLe)

/-- A natural sequence trapped between two fixed positive multiples of
`taoZ` has logarithmic `taoZ`-exponent one. -/
theorem tendsto_log_natCast_div_log_taoZ_of_const_mul_bounds
    {P : ℕ → ℕ} {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hP : ∀ᶠ x : ℕ in atTop,
      c * taoZ x ≤ (P x : ℝ) ∧ (P x : ℝ) ≤ C * taoZ x) :
    Tendsto (fun x => Real.log (P x : ℝ) / Real.log (taoZ x))
      atTop (𝓝 1) := by
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have hlower : Tendsto (fun x : ℕ =>
      1 + Real.log c / Real.log (taoZ x)) atTop (𝓝 1) := by
    convert tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop hlogZ) using 1
    all_goals norm_num
  have hupper : Tendsto (fun x : ℕ =>
      1 + Real.log C / Real.log (taoZ x)) atTop (𝓝 1) := by
    convert tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop hlogZ) using 1
    all_goals norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hP,
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hx hzOne
    have hlogZPos : 0 < Real.log (taoZ x) := Real.log_pos hzOne
    have hcZPos : 0 < c * taoZ x := mul_pos hc (taoZ_pos x)
    have hPPos : 0 < (P x : ℝ) := hcZPos.trans_le hx.1
    rw [show 1 + Real.log c / Real.log (taoZ x) =
      (Real.log c + Real.log (taoZ x)) / Real.log (taoZ x) by
        field_simp
        ring]
    rw [div_le_div_iff_of_pos_right hlogZPos]
    rw [← Real.log_mul hc.ne' (taoZ_pos x).ne']
    exact Real.strictMonoOn_log.monotoneOn hcZPos hPPos hx.1
  · filter_upwards [hP,
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hx hzOne
    have hlogZPos : 0 < Real.log (taoZ x) := Real.log_pos hzOne
    have hPPos : 0 < (P x : ℝ) :=
      (mul_pos hc (taoZ_pos x)).trans_le hx.1
    have hCZPos : 0 < C * taoZ x := mul_pos hC (taoZ_pos x)
    rw [show 1 + Real.log C / Real.log (taoZ x) =
      (Real.log C + Real.log (taoZ x)) / Real.log (taoZ x) by
        field_simp
        ring]
    rw [div_le_div_iff_of_pos_right hlogZPos]
    rw [← Real.log_mul hC.ne' (taoZ_pos x).ne']
    exact Real.strictMonoOn_log.monotoneOn hPPos hCZPos hx.2

/-- Any selector from the canonical critical prime block has `taoZ`-exponent
one, uniformly enough for diagonalization. -/
theorem tendsto_log_selector_div_log_taoZ_of_mem_criticalPrimeBand
    {P : ℕ → ℕ}
    (hP : ∀ᶠ x : ℕ in atTop, P x ∈ taoOneTermCriticalPrimeBand x) :
    Tendsto (fun x => Real.log (P x : ℝ) / Real.log (taoZ x))
      atTop (𝓝 1) := by
  apply tendsto_log_natCast_div_log_taoZ_of_const_mul_bounds
    (c := 1) (C := 3) (by norm_num) (by norm_num)
  filter_upwards [hP, eventually_mem_taoOneTermCriticalPrimeBand_bounds] with
    x hx hbounds
  have hp := hbounds (P x) hx
  simpa only [one_mul] using ⟨hp.2.1.le, hp.2.2.le⟩

/-- The exact smooth-number arguments `X=x/p²`, `y=p` lie in the critical
regime with exponent one for every selector from the canonical prime block. -/
theorem isTaoCriticalSmoothRegime_natDiv_sq_of_mem_criticalPrimeBand
    {P : ℕ → ℕ}
    (hP : ∀ᶠ x : ℕ in atTop, P x ∈ taoOneTermCriticalPrimeBand x) :
    IsTaoCriticalSmoothRegime (fun x => x / P x ^ 2) P 1 := by
  have hPZ :=
    tendsto_log_selector_div_log_taoZ_of_mem_criticalPrimeBand hP
  have hPsmallProduct := hPZ.mul tendsto_log_taoZ_div_log_nat_zero
  have hPsmall : Tendsto (fun x =>
      Real.log (P x : ℝ) / Real.log x) atTop (𝓝 0) := by
    have hprod0 : Tendsto (fun x =>
        (Real.log (P x : ℝ) / Real.log (taoZ x)) *
          (Real.log (taoZ x) / Real.log x)) atTop (𝓝 0) := by
      simpa using hPsmallProduct
    apply hprod0.congr'
    filter_upwards [tendsto_taoZ_atTop.eventually
        (eventually_gt_atTop (1 : ℝ)),
      tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hz hx
    have hlogz : Real.log (taoZ x) ≠ 0 := (Real.log_pos hz).ne'
    have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp
  have hPpos : ∀ᶠ x : ℕ in atTop, 0 < P x := by
    filter_upwards [hP, eventually_mem_taoOneTermCriticalPrimeBand_bounds] with
      x hp hbounds
    exact (hbounds (P x) hp).1.pos
  exact ⟨tendsto_log_natDiv_sq_div_log_nat_one hPpos hPsmall, hPZ⟩

/-- The canonical critical prime block is eventually nonempty. -/
theorem eventually_taoOneTermCriticalPrimeBand_nonempty :
    ∀ᶠ x : ℕ in atTop, (taoOneTermCriticalPrimeBand x).Nonempty := by
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_ge_atTop (2 : ℝ))] with x hz
  have htop : 2 ≤ taoOneTermCriticalPrimeBandTop x := by
    have : (2 : ℝ) ≤ (taoOneTermCriticalPrimeBandTop x : ℝ) := by
      exact (show (2 : ℝ) ≤ 2 * taoZ x by linarith).trans (Nat.le_ceil _)
    exact_mod_cast this
  have hhalf : taoOneTermCriticalPrimeBandTop x / 2 ≠ 0 := by omega
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    Nat.bertrand (taoOneTermCriticalPrimeBandTop x / 2) hhalf
  refine ⟨p, mem_cepDyadicPrimeBlock_iff.mpr ⟨hpPrime, hpLower, ?_⟩⟩
  exact hpUpper.trans (by omega)

set_option maxHeartbeats 800000 in
/-- Uniform sharp critical lower estimate for every prime in the moving
dyadic block around `taoZ`. -/
theorem eventually_criticalPrimeBand_self_div_taoZ_rpow_le_psiNat
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ taoOneTermCriticalPrimeBand x,
      (x / p ^ 2 : ℕ) / (taoZ x) ^ (1 + ε) ≤
        (psiNat (x / p ^ 2) p : ℝ) := by
  apply eventually_forall_of_forall_selector
    (R := fun x p => p ∈ taoOneTermCriticalPrimeBand x)
    (P := fun x p =>
      (x / p ^ 2 : ℕ) / (taoZ x) ^ (1 + ε) ≤
        (psiNat (x / p ^ 2) p : ℝ))
  · filter_upwards [eventually_taoOneTermCriticalPrimeBand_nonempty] with x hx
    exact hx
  · intro P hP
    simpa only [div_one] using
      (isTaoCriticalSmoothRegime_natDiv_sq_of_mem_criticalPrimeBand hP).eventually_self_div_taoZ_rpow_le_psiNat
        (by norm_num) hε

/-- The PNT envelope gives a uniform reciprocal-prime mass lower bound for
the canonical one-term block. -/
theorem eventually_one_div_eight_log_le_sum_inv_criticalPrimeBand :
    ∀ᶠ x : ℕ in atTop,
      1 / (8 * Real.log (taoOneTermCriticalPrimeBandTop x : ℝ)) ≤
        ∑ p ∈ taoOneTermCriticalPrimeBand x, (p : ℝ)⁻¹ := by
  obtain ⟨B, hB, htheta⟩ := exists_chebyshevTheta_quarter_threshold
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_ge_atTop (B : ℝ))] with x hz
  have htwoB : 2 * B ≤ taoOneTermCriticalPrimeBandTop x := by
    have hreal : (2 * B : ℕ) ≤
        (taoOneTermCriticalPrimeBandTop x : ℝ) := by
      have htwoBreal : ((2 * B : ℕ) : ℝ) ≤ 2 * taoZ x := by
        push_cast
        nlinarith
      exact htwoBreal.trans (Nat.le_ceil _)
    exact_mod_cast hreal
  have hhalfB : B ≤ taoOneTermCriticalPrimeBandTop x / 2 := by omega
  have htopB : B ≤ taoOneTermCriticalPrimeBandTop x :=
    hhalfB.trans (Nat.div_le_self _ _)
  have htopFour : 4 ≤ taoOneTermCriticalPrimeBandTop x :=
    hB.trans htopB
  simpa only [taoOneTermCriticalPrimeBand] using
    one_div_eight_log_le_sum_inv_cepDyadicPrimeBlock htopFour
      (htheta _ htopB).1 (htheta _ hhalfB).2

set_option maxHeartbeats 800000 in
/-- Every prime in the canonical critical block has square at most the ambient
cutoff, uniformly for large `x`. -/
theorem eventually_criticalPrimeBand_sq_le :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ taoOneTermCriticalPrimeBand x, p ^ 2 ≤ x := by
  apply eventually_forall_of_forall_selector
    (R := fun x p => p ∈ taoOneTermCriticalPrimeBand x)
    (P := fun x p => p ^ 2 ≤ x)
  · filter_upwards [eventually_taoOneTermCriticalPrimeBand_nonempty] with x hx
    exact hx
  · intro P hP
    have hregime :=
      isTaoCriticalSmoothRegime_natDiv_sq_of_mem_criticalPrimeBand hP
    filter_upwards [hregime.eventually_two_le_X, hP,
      eventually_mem_taoOneTermCriticalPrimeBand_bounds] with x hx hp hbounds
    have hpPos := (hbounds (P x) hp).1.pos
    have hqPos : 0 < x / P x ^ 2 := by omega
    have hmul := (Nat.le_div_iff_mul_le (pow_pos hpPos 2)).mp hqPos
    simpa using hmul

/-- Finite lower packet obtained by summing the uniform critical estimate over
the canonical prime block while retaining its reciprocal mass. -/
theorem eventually_criticalPrimeBand_packet_le_sum_psiNat
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      ((x : ℝ) /
          (2 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
            (taoZ x) ^ (1 + ε))) *
          (∑ p ∈ taoOneTermCriticalPrimeBand x, (p : ℝ)⁻¹) ≤
        ∑ p ∈ taoOneTermCriticalPrimeBand x,
          (psiNat (x / p ^ 2) p : ℝ) := by
  filter_upwards [eventually_criticalPrimeBand_self_div_taoZ_rpow_le_psiNat hε,
    eventually_criticalPrimeBand_sq_le,
    eventually_mem_taoOneTermCriticalPrimeBand_bounds] with x hpsi hsq hbounds
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpData := hbounds p hp
  have hpPos : 0 < p := hpData.1.pos
  have hnPos : 0 < taoOneTermCriticalPrimeBandTop x := by
    have hpTop := (mem_cepDyadicPrimeBlock_iff.mp hp).2.2
    omega
  have hpTop : (p : ℝ) ≤ taoOneTermCriticalPrimeBandTop x := by
    exact_mod_cast (mem_cepDyadicPrimeBlock_iff.mp hp).2.2
  have hpRealPos : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hnRealPos : (0 : ℝ) < taoOneTermCriticalPrimeBandTop x := by
    exact_mod_cast hnPos
  have hxNonneg : (0 : ℝ) ≤ x := by positivity
  have hpSqLe := hsq p hp
  have hquot : (x : ℝ) / (p ^ 2 : ℕ) ≤
      2 * (x / p ^ 2 : ℕ) :=
    cast_div_le_two_mul_natDiv (pow_pos hpPos 2) hpSqLe
  have hdenom : (p : ℝ) ^ 2 ≤
      (taoOneTermCriticalPrimeBandTop x : ℝ) * p := by
    nlinarith
  have hbase : (x : ℝ) /
      ((taoOneTermCriticalPrimeBandTop x : ℝ) * p) ≤
        (x : ℝ) / (p : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_left hxNonneg (pow_pos hpRealPos 2) hdenom
  have hhalf : (x : ℝ) /
      (2 * (taoOneTermCriticalPrimeBandTop x : ℝ)) * (p : ℝ)⁻¹ ≤
        (x / p ^ 2 : ℕ) := by
    have heq : (x : ℝ) /
        (2 * (taoOneTermCriticalPrimeBandTop x : ℝ)) * (p : ℝ)⁻¹ =
          ((x : ℝ) /
            ((taoOneTermCriticalPrimeBandTop x : ℝ) * p)) / 2 := by
      field_simp
    rw [heq]
    have hquot' : (x : ℝ) / (p : ℝ) ^ 2 ≤
        2 * (x / p ^ 2 : ℕ) := by
      simpa only [Nat.cast_pow] using hquot
    nlinarith
  have hzPowPos : 0 < (taoZ x) ^ (1 + ε) :=
    Real.rpow_pos_of_pos (taoZ_pos x) _
  calc
    (x : ℝ) /
          (2 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
            (taoZ x) ^ (1 + ε)) * (p : ℝ)⁻¹ =
        ((x : ℝ) /
          (2 * (taoOneTermCriticalPrimeBandTop x : ℝ)) * (p : ℝ)⁻¹) /
            (taoZ x) ^ (1 + ε) := by field_simp
    _ ≤ (x / p ^ 2 : ℕ) / (taoZ x) ^ (1 + ε) :=
      div_le_div_of_nonneg_right hhalf hzPowPos.le
    _ ≤ (psiNat (x / p ^ 2) p : ℝ) := hpsi p hp

/-- PNT reciprocal mass inserted into the finite critical packet. -/
theorem eventually_self_div_criticalPrimeBandDenominator_le_sum_psiNat
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) /
          (16 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
            Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) *
            (taoZ x) ^ (1 + ε)) ≤
        ∑ p ∈ taoOneTermCriticalPrimeBand x,
          (psiNat (x / p ^ 2) p : ℝ) := by
  filter_upwards [eventually_criticalPrimeBand_packet_le_sum_psiNat hε,
    eventually_one_div_eight_log_le_sum_inv_criticalPrimeBand,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hpacket hmass hz
  have hfactorNonneg : 0 ≤ (x : ℝ) /
      (2 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
        (taoZ x) ^ (1 + ε)) := by positivity
  calc
    (x : ℝ) /
          (16 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
            Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) *
            (taoZ x) ^ (1 + ε)) =
        ((x : ℝ) /
          (2 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
            (taoZ x) ^ (1 + ε))) *
          (1 / (8 * Real.log (taoOneTermCriticalPrimeBandTop x : ℝ))) := by
      field_simp
      ring
    _ ≤ ((x : ℝ) /
          (2 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
            (taoZ x) ^ (1 + ε))) *
          (∑ p ∈ taoOneTermCriticalPrimeBand x, (p : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left hmass hfactorNonneg
    _ ≤ ∑ p ∈ taoOneTermCriticalPrimeBand x,
          (psiNat (x / p ^ 2) p : ℝ) := hpacket

/-- The ceiling and logarithmic factors in the critical prime packet cost
only an arbitrarily small positive power of `taoZ`. -/
theorem eventually_criticalPrimeBandDenominator_le_taoZ_rpow
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      16 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
          Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) *
          (taoZ x) ^ (1 + δ / 2) ≤
        (taoZ x) ^ (2 + δ) := by
  have hhalf : 0 < δ / 2 := by positivity
  have hlogSmall := (isLittleO_log_rpow_atTop hhalf).def
    (by norm_num : (0 : ℝ) < 1 / 96)
  have hpowTop : Tendsto (fun z : ℝ => z ^ (δ / 2)) atTop atTop :=
    tendsto_rpow_atTop hhalf
  filter_upwards [tendsto_taoZ_atTop.eventually hlogSmall,
    hpowTop.comp tendsto_taoZ_atTop |>.eventually
      (eventually_ge_atTop (96 * Real.log 3 : ℝ)),
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hlog hpow hz
  have hzPos : 0 < taoZ x := taoZ_pos x
  have hzPowNonneg : 0 ≤ (taoZ x) ^ (δ / 2) :=
    Real.rpow_nonneg hzPos.le _
  have hlogzNonneg : 0 ≤ Real.log (taoZ x) := Real.log_nonneg hz
  have hlogz : Real.log (taoZ x) ≤
      (1 / 96 : ℝ) * (taoZ x) ^ (δ / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogzNonneg,
      abs_of_nonneg hzPowNonneg] using hlog
  have htop : (taoOneTermCriticalPrimeBandTop x : ℝ) <
      3 * taoZ x := by
    have hceil : (taoOneTermCriticalPrimeBandTop x : ℝ) <
        2 * taoZ x + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have htopPos : 0 < (taoOneTermCriticalPrimeBandTop x : ℝ) := by
    have : (0 : ℝ) < 2 * taoZ x := by positivity
    exact this.trans_le (Nat.le_ceil _)
  have hlogTop : Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) ≤
      Real.log 3 + Real.log (taoZ x) := by
    calc
      Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) ≤
          Real.log (3 * taoZ x) :=
        Real.strictMonoOn_log.monotoneOn htopPos
          (mul_pos (by norm_num) hzPos) htop.le
      _ = Real.log 3 + Real.log (taoZ x) := by
        rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hzPos.ne']
  have hlogAbsorb : 48 *
      Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) ≤
        (taoZ x) ^ (δ / 2) := by
    have hpow' : 96 * Real.log 3 ≤ (taoZ x) ^ (δ / 2) := by
      simpa [Function.comp_def] using hpow
    calc
      48 * Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) ≤
          48 * (Real.log 3 + Real.log (taoZ x)) := by gcongr
      _ ≤ (1 / 2 : ℝ) * (taoZ x) ^ (δ / 2) +
          (1 / 2 : ℝ) * (taoZ x) ^ (δ / 2) := by
        nlinarith
      _ = (taoZ x) ^ (δ / 2) := by ring
  have htopOne : (1 : ℝ) ≤ taoOneTermCriticalPrimeBandTop x := by
    have htopNat : 1 ≤ taoOneTermCriticalPrimeBandTop x := by
      exact_mod_cast (show (1 : ℝ) ≤ 2 * taoZ x by linarith).trans
        (Nat.le_ceil _)
    exact_mod_cast htopNat
  have hlogTopNonneg : 0 ≤
      Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) :=
    Real.log_nonneg htopOne
  have hzLargePowNonneg : 0 ≤ (taoZ x) ^ (1 + δ / 2) :=
    Real.rpow_nonneg hzPos.le _
  have hcoeff : 16 * (taoOneTermCriticalPrimeBandTop x : ℝ) ≤
      48 * taoZ x := by linarith
  calc
    16 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
          Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) *
          (taoZ x) ^ (1 + δ / 2) ≤
        48 * taoZ x *
          Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) *
          (taoZ x) ^ (1 + δ / 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff hlogTopNonneg)
        hzLargePowNonneg
    _ ≤ (taoZ x) ^ (δ / 2) * taoZ x *
          (taoZ x) ^ (1 + δ / 2) := by
      have hrestNonneg : 0 ≤ taoZ x * (taoZ x) ^ (1 + δ / 2) := by
        positivity
      rw [show 48 * taoZ x *
          Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) *
          (taoZ x) ^ (1 + δ / 2) =
        (48 * Real.log (taoOneTermCriticalPrimeBandTop x : ℝ)) *
          (taoZ x * (taoZ x) ^ (1 + δ / 2)) by ring]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right hlogAbsorb hrestNonneg)
    _ = (taoZ x) ^ (2 + δ) := by
      calc
        (taoZ x) ^ (δ / 2) * taoZ x *
            (taoZ x) ^ (1 + δ / 2) =
          (taoZ x) ^ (δ / 2) * (taoZ x) ^ (1 : ℝ) *
            (taoZ x) ^ (1 + δ / 2) := by
              rw [Real.rpow_one]
        _ =
          (taoZ x) ^ (δ / 2 + 1) *
            (taoZ x) ^ (1 + δ / 2) := by
              rw [← Real.rpow_add hzPos]
        _ = (taoZ x) ^ ((δ / 2 + 1) + (1 + δ / 2)) := by
              exact (Real.rpow_add hzPos _ _).symm
        _ = (taoZ x) ^ (2 + δ) := by ring_nf

/-- The canonical critical block is a subfamily of the exact prime sum for
`badOneTermCount`. -/
theorem eventually_sum_psiNat_criticalPrimeBand_le_badOneTermCount :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoOneTermCriticalPrimeBand x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (badOneTermCount x : ℝ) := by
  filter_upwards [eventually_criticalPrimeBand_sq_le,
    eventually_mem_taoOneTermCriticalPrimeBand_bounds] with x hsq hbounds
  rw [badOneTermCount_eq_sum_psiNat]
  push_cast
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpData := hbounds p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hpData.1.two_le, ?_⟩, hpData.1⟩
    rw [Nat.le_sqrt]
    simpa [pow_two] using hsq p hp
  · intro p _hp _hnot
    positivity

/-- Lower half of Tao's Lemma 1.6(i): the one-term bad set has at least
`x / z^(2+δ)` elements for every fixed positive slack `δ`. -/
theorem eventually_self_div_taoZ_rpow_le_badOneTermCount
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / (taoZ x) ^ (2 + δ) ≤
        (badOneTermCount x : ℝ) := by
  have hhalf : 0 < δ / 2 := by positivity
  filter_upwards [
    eventually_criticalPrimeBandDenominator_le_taoZ_rpow hδ,
    eventually_self_div_criticalPrimeBandDenominator_le_sum_psiNat hhalf,
    eventually_sum_psiNat_criticalPrimeBand_le_badOneTermCount,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hden hpacket hsubset hz
  have hdenPos : 0 <
      16 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
        Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) *
        (taoZ x) ^ (1 + δ / 2) := by
    have htopTwo : (2 : ℝ) ≤ taoOneTermCriticalPrimeBandTop x := by
      have hceil : (2 : ℝ) * taoZ x ≤
          taoOneTermCriticalPrimeBandTop x := Nat.le_ceil _
      linarith
    have hlogPos : 0 <
        Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) :=
      Real.log_pos (one_lt_two.trans_le htopTwo)
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_two htopTwo))
        hlogPos)
      (Real.rpow_pos_of_pos (taoZ_pos x) _)
  have hzPowPos : 0 < (taoZ x) ^ (2 + δ) :=
    Real.rpow_pos_of_pos (taoZ_pos x) _
  calc
    (x : ℝ) / (taoZ x) ^ (2 + δ) ≤
        (x : ℝ) /
          (16 * (taoOneTermCriticalPrimeBandTop x : ℝ) *
            Real.log (taoOneTermCriticalPrimeBandTop x : ℝ) *
            (taoZ x) ^ (1 + δ / 2)) :=
      div_le_div_of_nonneg_left (by positivity) hdenPos hden
    _ ≤ ∑ p ∈ taoOneTermCriticalPrimeBand x,
          (psiNat (x / p ^ 2) p : ℝ) := hpacket
    _ ≤ (badOneTermCount x : ℝ) := hsubset

/-! ## The large-prime part of the upper bound -/

/-- A smooth-number counting function never exceeds its ambient positive
integer interval. -/
theorem psiNat_le_self (X y : ℕ) : psiNat X y ≤ X := by
  have hcard := Nat.smoothNumbersUpTo_card_add_roughNumbersUpTo_card X (y + 1)
  simpa only [psiNat] using Nat.le.intro hcard

/-- Monotonicity of the source-inclusive smooth-number count in its
smoothness parameter. -/
theorem psiNat_mono_right {X y Y : ℕ} (hyY : y ≤ Y) :
    psiNat X y ≤ psiNat X Y := by
  apply Finset.card_le_card
  intro n hn
  rw [mem_smoothNumbersUpTo_source] at hn ⊢
  exact ⟨hn.1, (isSmooth_iff.mpr ⟨(isSmooth_iff.mp hn.2).1,
    fun p hp hpdvd => (isSmooth_iff.mp hn.2).2 p hp hpdvd |>.trans hyY⟩)⟩

/-- Natural cutoff corresponding to `z²` in the large-prime tail. -/
noncomputable def taoOneTermLargePrimeCutoff (x : ℕ) : ℕ :=
  ⌈(taoZ x) ^ (2 : ℕ)⌉₊

/-- The primes `p≥ceil(z²)` occurring in the exact one-term sum. -/
noncomputable def taoOneTermLargePrimeTail (x : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 x.sqrt).filter Nat.Prime).filter
    (fun p => taoOneTermLargePrimeCutoff x ≤ p)

/-- Rounded natural cutoff at a fixed `taoZ` exponent. -/
noncomputable def taoOneTermExponentCutoff (β : ℝ) (x : ℕ) : ℕ :=
  ⌈(taoZ x) ^ β⌉₊

/-- A rounded fixed power of `taoZ` has the expected logarithmic exponent. -/
theorem tendsto_log_exponentCutoff_div_log_taoZ
    {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun x : ℕ =>
      Real.log (taoOneTermExponentCutoff β x : ℝ) /
        Real.log (taoZ x)) atTop (𝓝 β) := by
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have hupper : Tendsto (fun x : ℕ =>
      β + Real.log 2 / Real.log (taoZ x)) atTop (𝓝 β) := by
    have hzero : Tendsto (fun x : ℕ =>
        Real.log 2 / Real.log (taoZ x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlogZ
    simpa using tendsto_const_nhds.add hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hz
    have hzPos : 0 < taoZ x := taoZ_pos x
    have hlogZPos : 0 < Real.log (taoZ x) := Real.log_pos hz
    have hpowPos : 0 < (taoZ x) ^ β :=
      Real.rpow_pos_of_pos hzPos _
    have hcutPos : 0 < (taoOneTermExponentCutoff β x : ℝ) :=
      hpowPos.trans_le (Nat.le_ceil _)
    have hlogLe : Real.log ((taoZ x) ^ β) ≤
        Real.log (taoOneTermExponentCutoff β x : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hpowPos hcutPos (Nat.le_ceil _)
    rw [Real.log_rpow hzPos] at hlogLe
    exact (le_div_iff₀ hlogZPos).2 (by nlinarith)
  · filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hz
    have hzPos : 0 < taoZ x := taoZ_pos x
    have hlogZPos : 0 < Real.log (taoZ x) := Real.log_pos hz
    have hpowPos : 0 < (taoZ x) ^ β :=
      Real.rpow_pos_of_pos hzPos _
    have hpowOne : 1 ≤ (taoZ x) ^ β :=
      Real.one_le_rpow hz.le hβ.le
    have hcutPos : 0 < (taoOneTermExponentCutoff β x : ℝ) :=
      hpowPos.trans_le (Nat.le_ceil _)
    have hcutHigh : (taoOneTermExponentCutoff β x : ℝ) <
        (taoZ x) ^ β + 1 := Nat.ceil_lt_add_one hpowPos.le
    have hcutTwo : (taoOneTermExponentCutoff β x : ℝ) ≤
        2 * (taoZ x) ^ β := by linarith
    have htwoPowPos : 0 < 2 * (taoZ x) ^ β := by positivity
    have hlogLe : Real.log (taoOneTermExponentCutoff β x : ℝ) ≤
        Real.log (2 * (taoZ x) ^ β) :=
      Real.strictMonoOn_log.monotoneOn hcutPos htwoPowPos hcutTwo
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpowPos.ne',
      Real.log_rpow hzPos] at hlogLe
    rw [show β + Real.log 2 / Real.log (taoZ x) =
      (Real.log 2 + β * Real.log (taoZ x)) /
        Real.log (taoZ x) by field_simp; ring]
    exact (div_le_div_iff_of_pos_right hlogZPos).2 hlogLe

/-- Natural cutoff corresponding to `sqrt z` in the small-prime range. -/
noncomputable def taoOneTermSmallPrimeCutoff (x : ℕ) : ℕ :=
  ⌈Real.sqrt (taoZ x)⌉₊

/-- The primes `p≤ceil(sqrt z)` occurring in the exact one-term sum. -/
noncomputable def taoOneTermSmallPrimeRange (x : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 x.sqrt).filter Nat.Prime).filter
    (fun p => p ≤ taoOneTermSmallPrimeCutoff x)

/-- Rounding `sqrt z` to a natural preserves logarithmic `z`-exponent
one half. -/
theorem tendsto_log_smallPrimeCutoff_div_log_taoZ_half :
    Tendsto (fun x : ℕ =>
      Real.log (taoOneTermSmallPrimeCutoff x : ℝ) / Real.log (taoZ x))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hsq : Tendsto (fun x : ℕ =>
      Real.log ((taoOneTermSmallPrimeCutoff x ^ 2 : ℕ) : ℝ) /
        Real.log (taoZ x)) atTop (𝓝 1) := by
    apply tendsto_log_natCast_div_log_taoZ_of_const_mul_bounds
      (P := fun x => taoOneTermSmallPrimeCutoff x ^ 2)
      (c := 1) (C := 4) (by norm_num) (by norm_num)
    filter_upwards [tendsto_taoZ_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hz
    have hsqrtNonneg : 0 ≤ Real.sqrt (taoZ x) := Real.sqrt_nonneg _
    have hsqrtOne : 1 ≤ Real.sqrt (taoZ x) := by
      rw [Real.le_sqrt (by norm_num) (taoZ_pos x).le]
      nlinarith
    have hceilLow : Real.sqrt (taoZ x) ≤
        (taoOneTermSmallPrimeCutoff x : ℝ) := Nat.le_ceil _
    have hceilHigh : (taoOneTermSmallPrimeCutoff x : ℝ) <
        Real.sqrt (taoZ x) + 1 := Nat.ceil_lt_add_one hsqrtNonneg
    have hsqEq : (Real.sqrt (taoZ x)) ^ 2 = taoZ x :=
      Real.sq_sqrt (taoZ_pos x).le
    constructor
    · push_cast
      nlinarith
    · push_cast
      nlinarith
  have hscaled : Tendsto (fun x : ℕ =>
      (1 / 2 : ℝ) *
        (Real.log ((taoOneTermSmallPrimeCutoff x ^ 2 : ℕ) : ℝ) /
          Real.log (taoZ x))) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [mul_one] using
      (tendsto_const_nhds.mul hsq : Tendsto (fun x : ℕ =>
        (1 / 2 : ℝ) *
          (Real.log ((taoOneTermSmallPrimeCutoff x ^ 2 : ℕ) : ℝ) /
            Real.log (taoZ x))) atTop (𝓝 ((1 / 2 : ℝ) * 1)))
  apply hscaled.congr'
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hz
  have hcutPos : 0 < taoOneTermSmallPrimeCutoff x := by
    have hceil : (1 : ℝ) ≤ taoOneTermSmallPrimeCutoff x := by
      have hsqrtOne : 1 ≤ Real.sqrt (taoZ x) := by
        rw [Real.le_sqrt (by norm_num) (taoZ_pos x).le]
        nlinarith
      exact hsqrtOne.trans (Nat.le_ceil _)
    exact_mod_cast lt_of_lt_of_le zero_lt_one hceil
  rw [Nat.cast_pow, Real.log_pow]
  ring

/-- Any positive natural selector bounded by `2z` is subpolynomial on the
ambient `x` scale. -/
theorem tendsto_log_selector_div_log_nat_zero_of_le_two_mul_taoZ
    {P : ℕ → ℕ}
    (hP : ∀ᶠ x : ℕ in atTop,
      1 ≤ P x ∧ (P x : ℝ) ≤ 2 * taoZ x) :
    Tendsto (fun x => Real.log (P x : ℝ) / Real.log x)
      atTop (𝓝 0) := by
  have hlogx : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun x : ℕ =>
      (Real.log 2 + Real.log (taoZ x)) / Real.log x) atTop (𝓝 0) := by
    have hconst : Tendsto (fun x : ℕ => Real.log 2 / Real.log x)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlogx
    have hsum := hconst.add tendsto_log_taoZ_div_log_nat_zero
    convert hsum using 1
    · funext x
      ring
    · norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · filter_upwards [hP,
      tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hp hx
    have hlogxPos : 0 < Real.log x := Real.log_pos hx
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.1)) hlogxPos.le
  · filter_upwards [hP,
      tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hp hx
    have hlogxPos : 0 < Real.log x := Real.log_pos hx
    have hPpos : (0 : ℝ) < P x := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp.1)
    have htwoZPos : 0 < 2 * taoZ x :=
      mul_pos (by norm_num) (taoZ_pos x)
    have hlogLe := Real.strictMonoOn_log.monotoneOn hPpos htwoZPos hp.2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (taoZ_pos x).ne'] at hlogLe
    exact (div_le_div_iff_of_pos_right hlogxPos).2 hlogLe

/-- A positive selector below a fixed rounded `taoZ` power is
subpolynomial on the ambient `x` scale. -/
theorem tendsto_log_selector_div_log_nat_zero_of_le_exponentCutoff
    {P : ℕ → ℕ} {β : ℝ} (hβ : 0 < β)
    (hP : ∀ᶠ x : ℕ in atTop,
      1 ≤ P x ∧ P x ≤ taoOneTermExponentCutoff β x) :
    Tendsto (fun x => Real.log (P x : ℝ) / Real.log x)
      atTop (𝓝 0) := by
  have hlogx : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun x : ℕ =>
      (Real.log 2 + β * Real.log (taoZ x)) / Real.log x)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun x : ℕ => Real.log 2 / Real.log x)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlogx
    have hscale : Tendsto (fun x : ℕ =>
        β * (Real.log (taoZ x) / Real.log x)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul
        tendsto_log_taoZ_div_log_nat_zero : Tendsto (fun x : ℕ =>
          β * (Real.log (taoZ x) / Real.log x)) atTop (𝓝 (β * 0)))
    have hsum := hconst.add hscale
    convert hsum using 1
    · funext x
      ring
    · norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · filter_upwards [hP,
      tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hp hx
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.1))
      (Real.log_pos hx).le
  · filter_upwards [hP,
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
      tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hp hz hx
    have hzPos : 0 < taoZ x := taoZ_pos x
    have hpowPos : 0 < (taoZ x) ^ β :=
      Real.rpow_pos_of_pos hzPos _
    have hpowOne : 1 ≤ (taoZ x) ^ β :=
      Real.one_le_rpow hz.le hβ.le
    have hcutHigh : (taoOneTermExponentCutoff β x : ℝ) <
        (taoZ x) ^ β + 1 := Nat.ceil_lt_add_one hpowPos.le
    have hPReal : (P x : ℝ) ≤ taoOneTermExponentCutoff β x := by
      exact_mod_cast hp.2
    have hPUpper : (P x : ℝ) ≤ 2 * (taoZ x) ^ β := by linarith
    have hPpos : (0 : ℝ) < P x := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp.1)
    have htwoPowPos : 0 < 2 * (taoZ x) ^ β := by positivity
    have hlogLe :=
      Real.strictMonoOn_log.monotoneOn hPpos htwoPowPos hPUpper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpowPos.ne',
      Real.log_rpow hzPos] at hlogLe
    exact (div_le_div_iff_of_pos_right (Real.log_pos hx)).2 hlogLe

/-- Exact critical-regime instantiation for a selector below a fixed rounded
`taoZ` power. -/
theorem isTaoCriticalSmoothRegime_natDiv_sq_exponentCutoffSelector
    {P : ℕ → ℕ} {β : ℝ} (hβ : 0 < β)
    (hP : ∀ᶠ x : ℕ in atTop,
      1 ≤ P x ∧ P x ≤ taoOneTermExponentCutoff β x) :
    IsTaoCriticalSmoothRegime (fun x => x / P x ^ 2)
      (taoOneTermExponentCutoff β) β := by
  exact ⟨tendsto_log_natDiv_sq_div_log_nat_one
      (hP.mono fun _ hp => lt_of_lt_of_le Nat.zero_lt_one hp.1)
      (tendsto_log_selector_div_log_nat_zero_of_le_exponentCutoff hβ hP),
    tendsto_log_exponentCutoff_div_log_taoZ hβ⟩

/-- Prime portion of the exact one-term sum between two rounded fixed
`taoZ` exponents. -/
noncomputable def taoOneTermExponentPrimeBand
    (α β : ℝ) (x : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 x.sqrt).filter Nat.Prime).filter (fun p =>
    taoOneTermExponentCutoff α x < p ∧
      p ≤ taoOneTermExponentCutoff β x)

set_option maxHeartbeats 800000 in
/-- Uniform critical upper estimate throughout a fixed exponent band. -/
theorem eventually_psiNat_exponentPrimeBand_le
    {α β ε : ℝ} (hβ : 0 < β)
    (hne : ∀ᶠ x : ℕ in atTop,
      (taoOneTermExponentPrimeBand α β x).Nonempty)
    (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ taoOneTermExponentPrimeBand α β x,
      (psiNat (x / p ^ 2) p : ℝ) ≤
        (x / p ^ 2 : ℕ) / (taoZ x) ^ (1 / β - ε) := by
  apply eventually_forall_of_forall_selector
    (R := fun x p => p ∈ taoOneTermExponentPrimeBand α β x)
    (P := fun x p =>
      (psiNat (x / p ^ 2) p : ℝ) ≤
        (x / p ^ 2 : ℕ) / (taoZ x) ^ (1 / β - ε))
    hne
  intro P hP
  have hPbound : ∀ᶠ x : ℕ in atTop,
      1 ≤ P x ∧ P x ≤ taoOneTermExponentCutoff β x := by
    filter_upwards [hP] with x hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := (Finset.mem_filter.mp hpData.1).2
    exact ⟨hpPrime.one_le, hpData.2.2⟩
  have hregime :=
    isTaoCriticalSmoothRegime_natDiv_sq_exponentCutoffSelector hβ hPbound
  filter_upwards [hP,
    hregime.eventually_psiNat_cast_le_self_div_taoZ_rpow hβ hε] with
      x hp hupper
  have hpCut : P x ≤ taoOneTermExponentCutoff β x :=
    (Finset.mem_filter.mp hp).2.2
  exact (by
    calc
      (psiNat (x / P x ^ 2) (P x) : ℝ) ≤
          (psiNat (x / P x ^ 2)
            (taoOneTermExponentCutoff β x) : ℝ) := by
        exact_mod_cast psiNat_mono_right hpCut
      _ ≤ (x / P x ^ 2 : ℕ) /
          (taoZ x) ^ (1 / β - ε) := hupper)

/-- Summed exponent-band estimate. The reciprocal-square tail contributes
the lower exponent `α`, while the smooth-number bound contributes `1/β`. -/
theorem eventually_sum_psiNat_exponentPrimeBand_le
    {α β ε : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hne : ∀ᶠ x : ℕ in atTop,
      (taoOneTermExponentPrimeBand α β x).Nonempty)
    (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoOneTermExponentPrimeBand α β x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) / (taoZ x) ^ (α + 1 / β - ε) := by
  have hpowTop : Tendsto (fun z : ℝ => z ^ α) atTop atTop :=
    tendsto_rpow_atTop hα
  filter_upwards [eventually_psiNat_exponentPrimeBand_le hβ hne hε,
    (hpowTop.comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))] with x hpsi hpow
  have hcutLow : (taoZ x) ^ α ≤
      (taoOneTermExponentCutoff α x : ℝ) := Nat.le_ceil _
  have hcut : 2 ≤ taoOneTermExponentCutoff α x := by
    have hpow' : 2 ≤ (taoZ x) ^ α := by
      simpa [Function.comp_def] using hpow
    exact_mod_cast hpow'.trans hcutLow
  have hsubset : taoOneTermExponentPrimeBand α β x ⊆
      Finset.Icc (taoOneTermExponentCutoff α x + 1) x.sqrt := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpBase : p ∈ (Finset.Icc 2 x.sqrt).filter Nat.Prime := hpData.1
    have hpBaseData : p ∈ Finset.Icc 2 x.sqrt ∧ p.Prime :=
      Finset.mem_filter.mp hpBase
    have hpRange : 2 ≤ p ∧ p ≤ x.sqrt :=
      Finset.mem_Icc.mp hpBaseData.1
    exact Finset.mem_Icc.mpr ⟨by omega, hpRange.2⟩
  have hrecip :
      (∑ p ∈ taoOneTermExponentPrimeBand α β x,
          (1 : ℝ) / (p : ℝ) ^ 2) ≤
        1 / (taoOneTermExponentCutoff α x : ℝ) := by
    calc
      (∑ p ∈ taoOneTermExponentPrimeBand α β x,
          (1 : ℝ) / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Finset.Icc (taoOneTermExponentCutoff α x + 1) x.sqrt,
            (1 : ℝ) / (p : ℝ) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun p _hp _hnot => by positivity)
      _ ≤ 1 / ((((taoOneTermExponentCutoff α x + 1) - 1 : ℕ)) : ℝ) :=
        sum_Icc_one_div_nat_sq_le (by omega)
      _ = 1 / (taoOneTermExponentCutoff α x : ℝ) := by
        rw [Nat.add_sub_cancel]
  have hzSavePos : 0 < (taoZ x) ^ (1 / β - ε) :=
    Real.rpow_pos_of_pos (taoZ_pos x) _
  have hcutPos : 0 < (taoOneTermExponentCutoff α x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hcut)
  calc
    (∑ p ∈ taoOneTermExponentPrimeBand α β x,
        (psiNat (x / p ^ 2) p : ℝ)) ≤
        ∑ p ∈ taoOneTermExponentPrimeBand α β x,
          ((x : ℝ) / (taoZ x) ^ (1 / β - ε)) *
            ((1 : ℝ) / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime := (Finset.mem_filter.mp
        (Finset.mem_filter.mp hp).1).2
      calc
        (psiNat (x / p ^ 2) p : ℝ) ≤
            (x / p ^ 2 : ℕ) / (taoZ x) ^ (1 / β - ε) := hpsi p hp
        _ ≤ ((x : ℝ) / (p : ℝ) ^ 2) /
            (taoZ x) ^ (1 / β - ε) := by
          exact div_le_div_of_nonneg_right
            (by
              calc
                (x / p ^ 2 : ℕ) ≤
                    (x : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
                _ = (x : ℝ) / (p : ℝ) ^ 2 := by
                  simp only [Nat.cast_pow])
            hzSavePos.le
        _ = ((x : ℝ) / (taoZ x) ^ (1 / β - ε)) *
            ((1 : ℝ) / (p : ℝ) ^ 2) := by
          field_simp [hpPrime.ne_zero]
    _ = ((x : ℝ) / (taoZ x) ^ (1 / β - ε)) *
        (∑ p ∈ taoOneTermExponentPrimeBand α β x,
          (1 : ℝ) / (p : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ ((x : ℝ) / (taoZ x) ^ (1 / β - ε)) *
        (1 / (taoOneTermExponentCutoff α x : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ ≤ (x : ℝ) / (taoZ x) ^ (α + 1 / β - ε) := by
      have hzAlphaPos : 0 < (taoZ x) ^ α :=
        Real.rpow_pos_of_pos (taoZ_pos x) _
      have hden : (taoZ x) ^ α * (taoZ x) ^ (1 / β - ε) ≤
          (taoOneTermExponentCutoff α x : ℝ) *
            (taoZ x) ^ (1 / β - ε) :=
        mul_le_mul_of_nonneg_right hcutLow hzSavePos.le
      calc
        ((x : ℝ) / (taoZ x) ^ (1 / β - ε)) *
            (1 / (taoOneTermExponentCutoff α x : ℝ)) =
          (x : ℝ) /
            ((taoOneTermExponentCutoff α x : ℝ) *
              (taoZ x) ^ (1 / β - ε)) := by field_simp
        _ ≤ (x : ℝ) /
            ((taoZ x) ^ α * (taoZ x) ^ (1 / β - ε)) :=
          div_le_div_of_nonneg_left (by positivity)
            (mul_pos hzAlphaPos hzSavePos) hden
        _ = (x : ℝ) / (taoZ x) ^ (α + 1 / β - ε) := by
          have hexp : α + 1 / β - ε = α + (1 / β - ε) := by ring
          rw [hexp, Real.rpow_add (taoZ_pos x)]

/-- A fixed rounded `taoZ` power has square below the ambient cutoff
eventually. -/
theorem eventually_exponentCutoff_sq_le
    {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ x : ℕ in atTop,
      taoOneTermExponentCutoff β x ^ 2 ≤ x := by
  have hbound : ∀ᶠ x : ℕ in atTop,
      1 ≤ taoOneTermExponentCutoff β x ∧
        taoOneTermExponentCutoff β x ≤ taoOneTermExponentCutoff β x := by
    filter_upwards [tendsto_taoZ_atTop.eventually
        (eventually_ge_atTop (1 : ℝ))] with x hz
    constructor
    · have hpowOne : 1 ≤ (taoZ x) ^ β :=
        Real.one_le_rpow hz hβ.le
      have hceil := hpowOne.trans (Nat.le_ceil ((taoZ x) ^ β))
      exact_mod_cast hceil
    · exact le_rfl
  have hregime :=
    isTaoCriticalSmoothRegime_natDiv_sq_exponentCutoffSelector hβ hbound
  filter_upwards [hregime.eventually_two_le_X, hbound] with x hx hcut
  have hpos : 0 < x / taoOneTermExponentCutoff β x ^ 2 := by omega
  have hmul := (Nat.le_div_iff_mul_le
    (pow_pos (lt_of_lt_of_le Nat.zero_lt_one hcut.1) 2)).mp hpos
  simpa using hmul

/-- Successive rounded powers whose exponents have a fixed positive gap
eventually differ by at least a factor two. -/
theorem eventually_two_mul_exponentCutoff_le
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∀ᶠ x : ℕ in atTop,
      2 * taoOneTermExponentCutoff α x ≤
        taoOneTermExponentCutoff β x := by
  have hgap : 0 < β - α := sub_pos.mpr hαβ
  have hgapTop : Tendsto (fun z : ℝ => z ^ (β - α)) atTop atTop :=
    tendsto_rpow_atTop hgap
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_ge_atTop (1 : ℝ)),
    (hgapTop.comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop (4 : ℝ))] with x hz hgapPow
  have hzPos : 0 < taoZ x := taoZ_pos x
  have hαPowPos : 0 < (taoZ x) ^ α :=
    Real.rpow_pos_of_pos hzPos _
  have hαPowOne : 1 ≤ (taoZ x) ^ α :=
    Real.one_le_rpow hz hα.le
  have hcutα : (taoOneTermExponentCutoff α x : ℝ) <
      (taoZ x) ^ α + 1 := Nat.ceil_lt_add_one hαPowPos.le
  have hcutβ : (taoZ x) ^ β ≤
      (taoOneTermExponentCutoff β x : ℝ) := Nat.le_ceil _
  have hgapPow' : 4 ≤ (taoZ x) ^ (β - α) := by
    simpa [Function.comp_def] using hgapPow
  have hpowSplit : (taoZ x) ^ β =
      (taoZ x) ^ α * (taoZ x) ^ (β - α) := by
    rw [← Real.rpow_add hzPos]
    congr 1
    ring
  have hreal : (2 * taoOneTermExponentCutoff α x : ℕ) ≤
      (taoOneTermExponentCutoff β x : ℝ) := by
    push_cast
    rw [hpowSplit] at hcutβ
    nlinarith
  exact_mod_cast hreal

/-- Every fixed positive-width exponent band is eventually nonempty. -/
theorem eventually_exponentPrimeBand_nonempty
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∀ᶠ x : ℕ in atTop,
      (taoOneTermExponentPrimeBand α β x).Nonempty := by
  have hβ : 0 < β := hα.trans hαβ
  filter_upwards [eventually_two_mul_exponentCutoff_le hα hαβ,
    eventually_exponentCutoff_sq_le hβ,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hdouble hsq hz
  have hcutPos : 0 < taoOneTermExponentCutoff α x := by
    have hpowOne : 1 ≤ (taoZ x) ^ α :=
      Real.one_le_rpow hz hα.le
    have hceil := hpowOne.trans (Nat.le_ceil ((taoZ x) ^ α))
    exact_mod_cast lt_of_lt_of_le zero_lt_one hceil
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    Nat.bertrand (taoOneTermExponentCutoff α x) hcutPos.ne'
  have hpUpperCut : p ≤ taoOneTermExponentCutoff β x :=
    hpUpper.trans hdouble
  have hpSq : p ^ 2 ≤ x := by
    exact (Nat.pow_le_pow_left hpUpperCut 2).trans hsq
  have hpSqrt : p ≤ x.sqrt := by
    rw [Nat.le_sqrt]
    simpa [pow_two] using hpSq
  refine ⟨p, ?_⟩
  simp only [taoOneTermExponentPrimeBand, Finset.mem_filter,
    Finset.mem_Icc]
  exact ⟨⟨⟨hpPrime.two_le, hpSqrt⟩, hpPrime⟩,
    hpLower, hpUpperCut⟩

/-! ### A finite exponent grid for the middle-prime range -/

/-- Uniform additive grid from exponent `1/2` to exponent `2`. -/
noncomputable def taoOneTermGridExponent (K k : ℕ) : ℝ :=
  1 / 2 + 3 * k / (2 * K)

@[simp]
theorem taoOneTermGridExponent_zero (K : ℕ) :
    taoOneTermGridExponent K 0 = 1 / 2 := by
  simp [taoOneTermGridExponent]

theorem taoOneTermGridExponent_self {K : ℕ} (hK : 0 < K) :
    taoOneTermGridExponent K K = 2 := by
  simp only [taoOneTermGridExponent]
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp [hKR]
  norm_num

theorem taoOneTermGridExponent_pos (K k : ℕ) :
    0 < taoOneTermGridExponent K k := by
  unfold taoOneTermGridExponent
  positivity

theorem taoOneTermGridExponent_strictMono {K : ℕ} (hK : 0 < K) {k l : ℕ}
    (hkl : k < l) :
    taoOneTermGridExponent K k < taoOneTermGridExponent K l := by
  unfold taoOneTermGridExponent
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hklR : (k : ℝ) < l := by exact_mod_cast hkl
  have hnum : (3 : ℝ) * k < 3 * l := by nlinarith
  have hden : (0 : ℝ) < 2 * K := by positivity
  simpa only [add_comm] using
    (add_lt_add_left (div_lt_div_of_pos_right hnum hden) (1 / 2 : ℝ))

theorem taoOneTermGridExponent_succ_sub {K k : ℕ} (hK : 0 < K) :
    taoOneTermGridExponent K (k + 1) - taoOneTermGridExponent K k =
      3 / (2 * K : ℝ) := by
  unfold taoOneTermGridExponent
  push_cast
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp
  ring

/-- Stable form of `a+1/a≥2`: replacing the reciprocal endpoint by
`1/b` loses at most four times the band width on `[1/2,∞)`. -/
theorem two_sub_four_mul_sub_le_add_inv
    {a b : ℝ} (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    2 - 4 * (b - a) ≤ a + 1 / b := by
  have haPos : 0 < a := by linarith
  have hbPos : 0 < b := haPos.trans_le hab
  have habProd : 1 / 4 ≤ a * b := by nlinarith
  have hamgm : 2 ≤ a + 1 / a := by
    rw [show a + 1 / a = (a ^ 2 + 1) / a by field_simp]
    rw [le_div_iff₀ haPos]
    nlinarith [sq_nonneg (a - 1)]
  have hrecip : 1 / a - 1 / b ≤ 4 * (b - a) := by
    rw [show 1 / a - 1 / b = (b - a) / (a * b) by field_simp]
    rw [div_le_iff₀ (mul_pos haPos hbPos)]
    nlinarith
  nlinarith

/-- Every adjacent grid band retains exponent at least `2-6/K`. -/
theorem two_sub_six_div_le_gridExponent_add_inv_succ
    {K k : ℕ} (hK : 0 < K) :
    2 - 6 / (K : ℝ) ≤
      taoOneTermGridExponent K k +
        1 / taoOneTermGridExponent K (k + 1) := by
  have ha : (1 / 2 : ℝ) ≤ taoOneTermGridExponent K k := by
    unfold taoOneTermGridExponent
    have : (0 : ℝ) ≤ 3 * k / (2 * K) := by positivity
    linarith
  have hab : taoOneTermGridExponent K k ≤
      taoOneTermGridExponent K (k + 1) :=
    (taoOneTermGridExponent_strictMono hK (by omega)).le
  have hstable := two_sub_four_mul_sub_le_add_inv ha hab
  rw [taoOneTermGridExponent_succ_sub hK] at hstable
  calc
    2 - 6 / (K : ℝ) = 2 - 4 * (3 / (2 * K : ℝ)) := by
      have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      field_simp [hKR]
      ring
    _ ≤ taoOneTermGridExponent K k +
        1 / taoOneTermGridExponent K (k + 1) := hstable

/-- Direct application of the fixed-band estimate to an adjacent exponent
grid cell. -/
theorem eventually_sum_psiNat_gridPrimeBand_le
    {K k : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoOneTermExponentPrimeBand
          (taoOneTermGridExponent K k)
          (taoOneTermGridExponent K (k + 1)) x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) / (taoZ x) ^
          (taoOneTermGridExponent K k +
            1 / taoOneTermGridExponent K (k + 1) - ε) := by
  have ha := taoOneTermGridExponent_pos K k
  have hab := taoOneTermGridExponent_strictMono hK (by omega : k < k + 1)
  exact eventually_sum_psiNat_exponentPrimeBand_le ha
    (taoOneTermGridExponent_pos K (k + 1))
    (eventually_exponentPrimeBand_nonempty ha hab) hε

/-- Common `2-6/K-ε` envelope for every adjacent grid band. -/
theorem eventually_sum_psiNat_gridPrimeBand_le_common
    {K k : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoOneTermExponentPrimeBand
          (taoOneTermGridExponent K k)
          (taoOneTermGridExponent K (k + 1)) x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) / (taoZ x) ^ (2 - 6 / (K : ℝ) - ε) := by
  filter_upwards [eventually_sum_psiNat_gridPrimeBand_le hK hε,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hband hz
  have hexp : 2 - 6 / (K : ℝ) - ε ≤
      taoOneTermGridExponent K k +
        1 / taoOneTermGridExponent K (k + 1) - ε := by
    exact sub_le_sub_right
      (two_sub_six_div_le_gridExponent_add_inv_succ (K := K) (k := k) hK) ε
  have hpow := Real.rpow_le_rpow_of_exponent_le hz hexp
  exact hband.trans (div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos (taoZ_pos x) _)
    hpow)

/-- The common adjacent-band estimate holds simultaneously on the finite
grid. -/
theorem eventually_forall_sum_psiNat_gridPrimeBand_le_common
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ k ∈ Finset.range K,
      (∑ p ∈ taoOneTermExponentPrimeBand
          (taoOneTermGridExponent K k)
          (taoOneTermGridExponent K (k + 1)) x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) / (taoZ x) ^ (2 - 6 / (K : ℝ) - ε) := by
  rw [Filter.eventually_all_finset]
  intro k hk
  exact eventually_sum_psiNat_gridPrimeBand_le_common hK hε

theorem taoOneTermGridExponent_mono {K : ℕ} (hK : 0 < K) {k l : ℕ}
    (hkl : k ≤ l) :
    taoOneTermGridExponent K k ≤ taoOneTermGridExponent K l := by
  rcases hkl.eq_or_lt with rfl | hkl
  · exact le_rfl
  · exact (taoOneTermGridExponent_strictMono hK hkl).le

theorem taoOneTermExponentCutoff_mono_of_one_le
    {a b : ℝ} {x : ℕ} (hz : 1 ≤ taoZ x) (hab : a ≤ b) :
    taoOneTermExponentCutoff a x ≤ taoOneTermExponentCutoff b x := by
  exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hz hab)

/-- Union of the adjacent exponent bands covering the middle-prime range. -/
noncomputable def taoOneTermGridPrimeUnion (K : ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.range K).biUnion fun k =>
    taoOneTermExponentPrimeBand
      (taoOneTermGridExponent K k)
      (taoOneTermGridExponent K (k + 1)) x

/-- Adjacent grid bands are pairwise disjoint once `taoZ≥1`. -/
theorem disjoint_taoOneTermExponentPrimeBand_grid
    {K i j x : ℕ} (hK : 0 < K) (hz : 1 ≤ taoZ x) (hij : i ≠ j) :
    Disjoint
      (taoOneTermExponentPrimeBand
        (taoOneTermGridExponent K i)
        (taoOneTermGridExponent K (i + 1)) x)
      (taoOneTermExponentPrimeBand
        (taoOneTermGridExponent K j)
        (taoOneTermGridExponent K (j + 1)) x) := by
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hi := (Finset.mem_filter.mp hpi).2
  have hj := (Finset.mem_filter.mp hpj).2
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hsucc : i + 1 ≤ j := by omega
    have hexp := taoOneTermGridExponent_mono hK hsucc
    have hcut := taoOneTermExponentCutoff_mono_of_one_le hz hexp
    omega
  · have hsucc : j + 1 ≤ i := by omega
    have hexp := taoOneTermGridExponent_mono hK hsucc
    have hcut := taoOneTermExponentCutoff_mono_of_one_le hz hexp
    omega

/-- Exact summation over the disjoint finite exponent grid. -/
theorem sum_taoOneTermGridPrimeUnion
    {K x : ℕ} (hK : 0 < K) (hz : 1 ≤ taoZ x) (f : ℕ → ℝ) :
    (∑ p ∈ taoOneTermGridPrimeUnion K x, f p) =
      ∑ k ∈ Finset.range K,
        ∑ p ∈ taoOneTermExponentPrimeBand
          (taoOneTermGridExponent K k)
          (taoOneTermGridExponent K (k + 1)) x, f p := by
  apply Finset.sum_biUnion
  intro i hi j hj hij
  exact disjoint_taoOneTermExponentPrimeBand_grid hK hz hij

/-- Summing the simultaneous common bound over all `K` grid cells. -/
theorem eventually_sum_psiNat_gridPrimeUnion_le
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoOneTermGridPrimeUnion K x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (K : ℝ) *
          ((x : ℝ) / (taoZ x) ^ (2 - 6 / (K : ℝ) - ε)) := by
  filter_upwards [
    eventually_forall_sum_psiNat_gridPrimeBand_le_common hK hε,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hbands hz
  calc
    (∑ p ∈ taoOneTermGridPrimeUnion K x,
        (psiNat (x / p ^ 2) p : ℝ)) =
        ∑ k ∈ Finset.range K,
          ∑ p ∈ taoOneTermExponentPrimeBand
            (taoOneTermGridExponent K k)
            (taoOneTermGridExponent K (k + 1)) x,
            (psiNat (x / p ^ 2) p : ℝ) :=
      sum_taoOneTermGridPrimeUnion hK hz _
    _ ≤ ∑ _k ∈ Finset.range K,
        ((x : ℝ) / (taoZ x) ^ (2 - 6 / (K : ℝ) - ε)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hbands k hk
    _ = (K : ℝ) *
        ((x : ℝ) / (taoZ x) ^ (2 - 6 / (K : ℝ) - ε)) := by
      simp

theorem taoOneTermExponentCutoff_half_eq_smallPrimeCutoff (x : ℕ) :
    taoOneTermExponentCutoff (1 / 2) x =
      taoOneTermSmallPrimeCutoff x := by
  simp only [taoOneTermExponentCutoff, taoOneTermSmallPrimeCutoff]
  rw [Real.sqrt_eq_rpow]

theorem taoOneTermExponentCutoff_two_eq_largePrimeCutoff (x : ℕ) :
    taoOneTermExponentCutoff 2 x = taoOneTermLargePrimeCutoff x := by
  simp only [taoOneTermExponentCutoff, taoOneTermLargePrimeCutoff]
  norm_num [Real.rpow_natCast]

/-- The small range, adjacent grid cells, and large tail cover every prime
in the exact one-term sum. -/
theorem oneTermPrimeRange_subset_small_union_grid_union_large
    {K x : ℕ} (hK : 0 < K) :
    (Finset.Icc 2 x.sqrt).filter Nat.Prime ⊆
      taoOneTermSmallPrimeRange x ∪ taoOneTermGridPrimeUnion K x ∪
        taoOneTermLargePrimeTail x := by
  intro p hp
  by_cases hsmall : p ≤ taoOneTermSmallPrimeCutoff x
  · simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hp, hsmall⟩))
  by_cases hlarge : taoOneTermLargePrimeCutoff x ≤ p
  · simp only [Finset.mem_union]
    exact Or.inr (Finset.mem_filter.mpr ⟨hp, hlarge⟩)
  · have hzero : taoOneTermGridExponent K 0 = 1 / 2 :=
      taoOneTermGridExponent_zero K
    have hself : taoOneTermGridExponent K K = 2 :=
      taoOneTermGridExponent_self hK
    have hlower : taoOneTermExponentCutoff
        (taoOneTermGridExponent K 0) x < p := by
      rw [hzero, taoOneTermExponentCutoff_half_eq_smallPrimeCutoff]
      omega
    have htop : p ≤ taoOneTermExponentCutoff
        (taoOneTermGridExponent K K) x := by
      rw [hself, taoOneTermExponentCutoff_two_eq_largePrimeCutoff]
      omega
    let hexists : ∃ j : ℕ, p ≤ taoOneTermExponentCutoff
        (taoOneTermGridExponent K j) x := ⟨K, htop⟩
    let j := Nat.find hexists
    have hjSpec : p ≤ taoOneTermExponentCutoff
        (taoOneTermGridExponent K j) x := Nat.find_spec hexists
    have hjLe : j ≤ K := Nat.find_min' hexists htop
    have hjPos : 0 < j := by
      have hjNe : j ≠ 0 := by
        intro hj
        rw [hj] at hjSpec
        exact (not_le_of_gt hlower) hjSpec
      omega
    let k := j - 1
    have hkLt : k < K := by
      dsimp only [k]
      omega
    have hkj : k + 1 = j := by
      dsimp only [k]
      omega
    have hkLower : taoOneTermExponentCutoff
        (taoOneTermGridExponent K k) x < p := by
      have hkNot := Nat.find_min hexists (show k < j by
        dsimp only [k]
        omega)
      omega
    have hkUpper : p ≤ taoOneTermExponentCutoff
        (taoOneTermGridExponent K (k + 1)) x := by
      rw [hkj]
      exact hjSpec
    have hpBand : p ∈ taoOneTermExponentPrimeBand
        (taoOneTermGridExponent K k)
        (taoOneTermGridExponent K (k + 1)) x :=
      Finset.mem_filter.mpr ⟨hp, hkLower, hkUpper⟩
    have hpUnion : p ∈ taoOneTermGridPrimeUnion K x := by
      rw [taoOneTermGridPrimeUnion, Finset.mem_biUnion]
      exact ⟨k, Finset.mem_range.mpr hkLt, hpBand⟩
    simp only [Finset.mem_union]
    exact Or.inl (Or.inr hpUnion)

/-- A sum of nonnegative terms over a finite union is at most the sum over
the two constituent finsets, without a disjointness hypothesis. -/
theorem sum_union_le_add_sum_of_nonneg
    {ι : Type*} [DecidableEq ι] (s t : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ s ∪ t, f i) ≤ (∑ i ∈ s, f i) + ∑ i ∈ t, f i := by
  have hunion : s ∪ t = s ∪ (t \ s) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  calc
    (∑ i ∈ s ∪ t, f i) =
        (∑ i ∈ s, f i) + ∑ i ∈ t \ s, f i := by
      rw [hunion, Finset.sum_union Finset.disjoint_sdiff]
    _ ≤ (∑ i ∈ s, f i) + ∑ i ∈ t, f i := by
      simpa only [add_comm] using add_le_add_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun i _hi _hnot => hf i)) (∑ i ∈ s, f i)

/-- Exact one-term count bounded by the three pieces of the finite exponent
decomposition. -/
theorem badOneTermCount_cast_le_small_add_grid_add_large
    {K x : ℕ} (hK : 0 < K) :
    (badOneTermCount x : ℝ) ≤
      (∑ p ∈ taoOneTermSmallPrimeRange x,
        (psiNat (x / p ^ 2) p : ℝ)) +
      (∑ p ∈ taoOneTermGridPrimeUnion K x,
        (psiNat (x / p ^ 2) p : ℝ)) +
      (∑ p ∈ taoOneTermLargePrimeTail x,
        (psiNat (x / p ^ 2) p : ℝ)) := by
  rw [badOneTermCount_eq_sum_psiNat]
  push_cast
  let f : ℕ → ℝ := fun p => (psiNat (x / p ^ 2) p : ℝ)
  have hsubset := oneTermPrimeRange_subset_small_union_grid_union_large
    (K := K) (x := x) hK
  calc
    (∑ p ∈ (Finset.Icc 2 x.sqrt).filter Nat.Prime, f p) ≤
        ∑ p ∈ (taoOneTermSmallPrimeRange x ∪
          taoOneTermGridPrimeUnion K x) ∪ taoOneTermLargePrimeTail x,
          f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _hp _hnot => by positivity)
    _ ≤ (∑ p ∈ taoOneTermSmallPrimeRange x ∪
          taoOneTermGridPrimeUnion K x, f p) +
        ∑ p ∈ taoOneTermLargePrimeTail x, f p :=
      sum_union_le_add_sum_of_nonneg _ _ f (fun _ => by positivity)
    _ ≤ ((∑ p ∈ taoOneTermSmallPrimeRange x, f p) +
          ∑ p ∈ taoOneTermGridPrimeUnion K x, f p) +
        ∑ p ∈ taoOneTermLargePrimeTail x, f p := by
      gcongr
      exact sum_union_le_add_sum_of_nonneg _ _ f (fun _ => by positivity)

/-- A mesh fine enough for `δ` gives the middle grid the common
`z^(-2+δ/4)` envelope, before absorbing the fixed number of cells. -/
theorem eventually_sum_psiNat_gridPrimeUnion_le_quarterSlack
    {K : ℕ} (hK : 0 < K) {δ : ℝ} (hδ : 0 < δ)
    (hmesh : 6 / (K : ℝ) ≤ δ / 8) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoOneTermGridPrimeUnion K x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (K : ℝ) *
          ((x : ℝ) / (taoZ x) ^ (2 - δ / 4)) := by
  have heighth : 0 < δ / 8 := by positivity
  filter_upwards [eventually_sum_psiNat_gridPrimeUnion_le hK heighth,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hmiddle hz
  have hexp : 2 - δ / 4 ≤ 2 - 6 / (K : ℝ) - δ / 8 := by
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hz hexp
  have hdiv : (x : ℝ) /
      (taoZ x) ^ (2 - 6 / (K : ℝ) - δ / 8) ≤
        (x : ℝ) / (taoZ x) ^ (2 - δ / 4) :=
    div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (taoZ_pos x) _) hpow
  exact hmiddle.trans (mul_le_mul_of_nonneg_left hdiv (by positivity))

/-- A selector from the small-prime range yields a critical smooth-number
regime with the fixed rounded square-root smoothness parameter. -/
theorem isTaoCriticalSmoothRegime_natDiv_sq_smallPrimeSelector
    {P : ℕ → ℕ}
    (hP : ∀ᶠ x : ℕ in atTop, P x ∈ taoOneTermSmallPrimeRange x) :
    IsTaoCriticalSmoothRegime (fun x => x / P x ^ 2)
      taoOneTermSmallPrimeCutoff (1 / 2) := by
  have hPbound : ∀ᶠ x : ℕ in atTop,
      1 ≤ P x ∧ (P x : ℝ) ≤ 2 * taoZ x := by
    filter_upwards [hP, tendsto_taoZ_atTop.eventually
        (eventually_ge_atTop (1 : ℝ))] with x hp hz
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := (Finset.mem_filter.mp hpData.1).2
    have hcutHigh : (taoOneTermSmallPrimeCutoff x : ℝ) <
        Real.sqrt (taoZ x) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    have hsqrtLe : Real.sqrt (taoZ x) ≤ taoZ x := by
      rw [Real.sqrt_le_iff]
      exact ⟨(taoZ_pos x).le, by nlinarith⟩
    constructor
    · exact hpPrime.one_le
    · have hpCut : (P x : ℝ) ≤ taoOneTermSmallPrimeCutoff x := by
        exact_mod_cast hpData.2
      have hpSqrt : (P x : ℝ) < Real.sqrt (taoZ x) + 1 :=
        hpCut.trans_lt hcutHigh
      linarith
  exact ⟨tendsto_log_natDiv_sq_div_log_nat_one
      (hPbound.mono fun _ hp => lt_of_lt_of_le Nat.zero_lt_one hp.1)
      (tendsto_log_selector_div_log_nat_zero_of_le_two_mul_taoZ hPbound),
    tendsto_log_smallPrimeCutoff_div_log_taoZ_half⟩

/-- The small-prime range contains the prime `2` for all sufficiently large
ambient cutoffs. -/
theorem eventually_taoOneTermSmallPrimeRange_nonempty :
    ∀ᶠ x : ℕ in atTop, (taoOneTermSmallPrimeRange x).Nonempty := by
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (4 : ℝ))] with x hx hz
  refine ⟨2, ?_⟩
  simp only [taoOneTermSmallPrimeRange, Finset.mem_filter,
    Finset.mem_Icc, Nat.prime_two, and_true]
  constructor
  · constructor
    · omega
    · rw [Nat.le_sqrt]
      omega
  · have hsqrtTwo : (2 : ℝ) ≤ Real.sqrt (taoZ x) := by
      rw [Real.le_sqrt (by norm_num) (taoZ_pos x).le]
      norm_num
      exact hz
    have hceil : Real.sqrt (taoZ x) ≤
        taoOneTermSmallPrimeCutoff x := Nat.le_ceil _
    exact_mod_cast hsqrtTwo.trans hceil

set_option maxHeartbeats 800000 in
/-- Uniform critical upper estimate for all primes up to the rounded
square-root `z` cutoff. -/
theorem eventually_psiNat_smallPrimeRange_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ taoOneTermSmallPrimeRange x,
      (psiNat (x / p ^ 2) p : ℝ) ≤
        (x / p ^ 2 : ℕ) / (taoZ x) ^ (2 - ε) := by
  apply eventually_forall_of_forall_selector
    (R := fun x p => p ∈ taoOneTermSmallPrimeRange x)
    (P := fun x p =>
      (psiNat (x / p ^ 2) p : ℝ) ≤
        (x / p ^ 2 : ℕ) / (taoZ x) ^ (2 - ε))
  · filter_upwards [eventually_taoOneTermSmallPrimeRange_nonempty] with x hx
    exact hx
  · intro P hP
    have hregime :=
      isTaoCriticalSmoothRegime_natDiv_sq_smallPrimeSelector hP
    filter_upwards [hP,
      hregime.eventually_psiNat_cast_le_self_div_taoZ_rpow
        (by norm_num : (0 : ℝ) < 1 / 2) hε] with x hp hupper
    have hpCut : P x ≤ taoOneTermSmallPrimeCutoff x :=
      (Finset.mem_filter.mp hp).2
    calc
      (psiNat (x / P x ^ 2) (P x) : ℝ) ≤
          (psiNat (x / P x ^ 2) (taoOneTermSmallPrimeCutoff x) : ℝ) := by
        exact_mod_cast psiNat_mono_right hpCut
      _ ≤ (x / P x ^ 2 : ℕ) /
          (taoZ x) ^ (1 / (1 / 2 : ℝ) - ε) := hupper
      _ = (x / P x ^ 2 : ℕ) / (taoZ x) ^ (2 - ε) := by norm_num

/-- The complete small-prime contribution has the required
`z^(-2+ε)` saving. -/
theorem eventually_sum_psiNat_smallPrimeRange_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoOneTermSmallPrimeRange x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) / (taoZ x) ^ (2 - ε) := by
  filter_upwards [eventually_psiNat_smallPrimeRange_le hε] with x hpsi
  have hsubset : taoOneTermSmallPrimeRange x ⊆ Finset.Icc 2 x.sqrt := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hrecip :
      (∑ p ∈ taoOneTermSmallPrimeRange x,
          (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 := by
    calc
      (∑ p ∈ taoOneTermSmallPrimeRange x,
          (1 : ℝ) / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Finset.Icc 2 x.sqrt, (1 : ℝ) / (p : ℝ) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun p _hp _hnot => by positivity)
      _ ≤ 1 / (((2 - 1 : ℕ) : ℝ)) :=
        sum_Icc_one_div_nat_sq_le (by norm_num)
      _ = 1 := by norm_num
  have hzPowPos : 0 < (taoZ x) ^ (2 - ε) :=
    Real.rpow_pos_of_pos (taoZ_pos x) _
  calc
    (∑ p ∈ taoOneTermSmallPrimeRange x,
        (psiNat (x / p ^ 2) p : ℝ)) ≤
        ∑ p ∈ taoOneTermSmallPrimeRange x,
          ((x : ℝ) / (taoZ x) ^ (2 - ε)) *
            ((1 : ℝ) / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime := (Finset.mem_filter.mp
        (Finset.mem_filter.mp hp).1).2
      have hpRealPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      calc
        (psiNat (x / p ^ 2) p : ℝ) ≤
            (x / p ^ 2 : ℕ) / (taoZ x) ^ (2 - ε) := hpsi p hp
        _ ≤ ((x : ℝ) / (p : ℝ) ^ 2) /
            (taoZ x) ^ (2 - ε) := by
          exact div_le_div_of_nonneg_right
            (by
              calc
                (x / p ^ 2 : ℕ) ≤
                    (x : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
                _ = (x : ℝ) / (p : ℝ) ^ 2 := by
                  simp only [Nat.cast_pow])
            hzPowPos.le
        _ = ((x : ℝ) / (taoZ x) ^ (2 - ε)) *
            ((1 : ℝ) / (p : ℝ) ^ 2) := by field_simp
    _ = ((x : ℝ) / (taoZ x) ^ (2 - ε)) *
        (∑ p ∈ taoOneTermSmallPrimeRange x,
          (1 : ℝ) / (p : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ ((x : ℝ) / (taoZ x) ^ (2 - ε)) * 1 := by
      exact mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = (x : ℝ) / (taoZ x) ^ (2 - ε) := by ring

/-- The large-prime contribution is bounded by the full reciprocal-square
integer tail beginning at `ceil(z²)`. -/
theorem sum_psiNat_largePrimeTail_le
    {x : ℕ} (hcut : 2 ≤ taoOneTermLargePrimeCutoff x) :
    (∑ p ∈ taoOneTermLargePrimeTail x,
        (psiNat (x / p ^ 2) p : ℝ)) ≤
      (x : ℝ) /
        ((taoOneTermLargePrimeCutoff x - 1 : ℕ) : ℝ) := by
  have hsubset : taoOneTermLargePrimeTail x ⊆
      Finset.Icc (taoOneTermLargePrimeCutoff x) x.sqrt := by
    intro p hp
    simp only [taoOneTermLargePrimeTail, Finset.mem_filter,
      Finset.mem_Icc] at hp ⊢
    exact ⟨hp.2, hp.1.1.2⟩
  calc
    (∑ p ∈ taoOneTermLargePrimeTail x,
        (psiNat (x / p ^ 2) p : ℝ)) ≤
        ∑ p ∈ taoOneTermLargePrimeTail x,
          (x : ℝ) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        (psiNat (x / p ^ 2) p : ℝ) ≤ (x / p ^ 2 : ℕ) := by
          exact_mod_cast psiNat_le_self (x / p ^ 2) p
        _ ≤ (x : ℝ) / ((p ^ 2 : ℕ) : ℝ) :=
          Nat.cast_div_le
        _ = (x : ℝ) / (p : ℝ) ^ 2 := by
          simp only [Nat.cast_pow]
    _ ≤ ∑ p ∈ Finset.Icc (taoOneTermLargePrimeCutoff x) x.sqrt,
          (x : ℝ) / (p : ℝ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _hp _hnot => by positivity)
    _ = (x : ℝ) *
        (∑ p ∈ Finset.Icc (taoOneTermLargePrimeCutoff x) x.sqrt,
          (1 : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ (x : ℝ) *
        (1 / ((taoOneTermLargePrimeCutoff x - 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_one_div_nat_sq_le hcut) (by positivity)
    _ = (x : ℝ) /
        ((taoOneTermLargePrimeCutoff x - 1 : ℕ) : ℝ) := by ring

/-- The large-prime tail already has the required `z^(-2+δ)` saving. -/
theorem eventually_sum_psiNat_largePrimeTail_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoOneTermLargePrimeTail x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) / (taoZ x) ^ (2 - δ) := by
  have hpowTop : Tendsto (fun z : ℝ => z ^ δ) atTop atTop :=
    tendsto_rpow_atTop hδ
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_ge_atTop (2 : ℝ)),
    (hpowTop.comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))] with x hz hpow
  have hzPos : 0 < taoZ x := taoZ_pos x
  have hzSq : 2 ≤ (taoZ x) ^ (2 : ℕ) := by nlinarith
  have hcutReal : (taoZ x) ^ (2 : ℕ) ≤
      (taoOneTermLargePrimeCutoff x : ℝ) := Nat.le_ceil _
  have hcut : 2 ≤ taoOneTermLargePrimeCutoff x := by
    exact_mod_cast hzSq.trans hcutReal
  have hcutSub : (taoZ x) ^ (2 : ℕ) / 2 ≤
      ((taoOneTermLargePrimeCutoff x - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ taoOneTermLargePrimeCutoff x), Nat.cast_one]
    nlinarith
  have hdenPos : 0 <
      ((taoOneTermLargePrimeCutoff x - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < taoOneTermLargePrimeCutoff x - 1)
  have hzSqPos : 0 < (taoZ x) ^ (2 : ℕ) := by positivity
  have htail := sum_psiNat_largePrimeTail_le (x := x) hcut
  calc
    (∑ p ∈ taoOneTermLargePrimeTail x,
        (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) /
          ((taoOneTermLargePrimeCutoff x - 1 : ℕ) : ℝ) := htail
    _ ≤ 2 * (x : ℝ) / (taoZ x) ^ (2 : ℕ) := by
      have hfrac :
          1 / ((taoOneTermLargePrimeCutoff x - 1 : ℕ) : ℝ) ≤
            2 / (taoZ x) ^ (2 : ℕ) := by
        rw [div_le_div_iff₀ hdenPos hzSqPos]
        nlinarith
      calc
        (x : ℝ) /
            ((taoOneTermLargePrimeCutoff x - 1 : ℕ) : ℝ) =
          (x : ℝ) *
            (1 / ((taoOneTermLargePrimeCutoff x - 1 : ℕ) : ℝ)) := by ring
        _ ≤ (x : ℝ) * (2 / (taoZ x) ^ (2 : ℕ)) := by gcongr
        _ = 2 * (x : ℝ) / (taoZ x) ^ (2 : ℕ) := by ring
    _ ≤ (x : ℝ) / (taoZ x) ^ (2 - δ) := by
      have hpow' : 2 ≤ (taoZ x) ^ δ := by
        simpa [Function.comp_def] using hpow
      have hfactor : 2 / (taoZ x) ^ (2 : ℕ) ≤
          1 / (taoZ x) ^ (2 - δ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        rw [one_mul]
        calc
          2 * (taoZ x) ^ (2 - δ) ≤
              (taoZ x) ^ δ * (taoZ x) ^ (2 - δ) :=
            mul_le_mul_of_nonneg_right hpow'
              (Real.rpow_nonneg hzPos.le _)
          _ = (taoZ x) ^ (2 : ℝ) := by
            rw [← Real.rpow_add hzPos]
            congr 1
            ring
          _ = (taoZ x) ^ (2 : ℕ) := by
            norm_num [Real.rpow_natCast]
      calc
        2 * (x : ℝ) / (taoZ x) ^ (2 : ℕ) =
            (x : ℝ) * (2 / (taoZ x) ^ (2 : ℕ)) := by ring
        _ ≤ (x : ℝ) * (1 / (taoZ x) ^ (2 - δ)) := by gcongr
        _ = (x : ℝ) / (taoZ x) ^ (2 - δ) := by ring

/-- Upper half of Tao's Lemma 1.6(i): the one-term bad set has at most
`x / z^(2-δ)` elements for every fixed positive slack `δ`. -/
theorem eventually_badOneTermCount_le_self_div_taoZ_rpow
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      (badOneTermCount x : ℝ) ≤
        (x : ℝ) / (taoZ x) ^ (2 - δ) := by
  obtain ⟨K, hKlarge⟩ := exists_nat_gt (48 / δ : ℝ)
  have hK : 0 < K := by
    have hratio : 0 < 48 / δ := by positivity
    have hKR : (0 : ℝ) < K := hratio.trans hKlarge
    exact_mod_cast hKR
  have hmesh : 6 / (K : ℝ) ≤ δ / 8 := by
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    have hmul : 48 < (K : ℝ) * δ :=
      (div_lt_iff₀ hδ).mp hKlarge
    apply le_of_lt
    rw [div_lt_iff₀ hKR]
    nlinarith
  have hquarter : 0 < δ / 4 := by positivity
  have habsorbTop : Tendsto (fun z : ℝ => z ^ (3 * δ / 4)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  filter_upwards [eventually_sum_psiNat_smallPrimeRange_le hquarter,
    eventually_sum_psiNat_gridPrimeUnion_le_quarterSlack hK hδ hmesh,
    eventually_sum_psiNat_largePrimeTail_le hquarter,
    (habsorbTop.comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop (K + 2 : ℝ))] with
      x hsmall hmiddle hlarge habsorb
  have hdecomp :=
    badOneTermCount_cast_le_small_add_grid_add_large (K := K) (x := x) hK
  have hbaseNonneg : 0 ≤
      (x : ℝ) / (taoZ x) ^ (2 - δ / 4) :=
    div_nonneg (Nat.cast_nonneg _)
      (Real.rpow_nonneg (taoZ_pos x).le _)
  have hthree : (badOneTermCount x : ℝ) ≤
      ((K : ℝ) + 2) *
        ((x : ℝ) / (taoZ x) ^ (2 - δ / 4)) := by
    calc
      (badOneTermCount x : ℝ) ≤
          (∑ p ∈ taoOneTermSmallPrimeRange x,
            (psiNat (x / p ^ 2) p : ℝ)) +
          (∑ p ∈ taoOneTermGridPrimeUnion K x,
            (psiNat (x / p ^ 2) p : ℝ)) +
          (∑ p ∈ taoOneTermLargePrimeTail x,
            (psiNat (x / p ^ 2) p : ℝ)) := hdecomp
      _ ≤ ((x : ℝ) / (taoZ x) ^ (2 - δ / 4)) +
          (K : ℝ) * ((x : ℝ) / (taoZ x) ^ (2 - δ / 4)) +
          ((x : ℝ) / (taoZ x) ^ (2 - δ / 4)) :=
        add_le_add (add_le_add hsmall hmiddle) hlarge
      _ = ((K : ℝ) + 2) *
          ((x : ℝ) / (taoZ x) ^ (2 - δ / 4)) := by ring
  have habsorb' : (K : ℝ) + 2 ≤ (taoZ x) ^ (3 * δ / 4) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using habsorb
  calc
    (badOneTermCount x : ℝ) ≤
        ((K : ℝ) + 2) *
          ((x : ℝ) / (taoZ x) ^ (2 - δ / 4)) := hthree
    _ ≤ (taoZ x) ^ (3 * δ / 4) *
          ((x : ℝ) / (taoZ x) ^ (2 - δ / 4)) :=
      mul_le_mul_of_nonneg_right habsorb' hbaseNonneg
    _ = (x : ℝ) / (taoZ x) ^ (2 - δ) := by
      have hzPos := taoZ_pos x
      rw [show (2 - δ / 4 : ℝ) = (2 - δ) + 3 * δ / 4 by ring,
        Real.rpow_add hzPos]
      field_simp

/-- Exact asymptotic contract for Tao's Lemma 1.6(i). -/
theorem badOneTermCount_quotientPowerScale :
    QuotientPowerScale
      (fun x => (badOneTermCount x : ℝ))
      (fun x => (x : ℝ)) taoZ 2 := by
  intro ε hε
  filter_upwards [eventually_self_div_taoZ_rpow_le_badOneTermCount hε,
    eventually_badOneTermCount_le_self_div_taoZ_rpow hε] with x hlower hupper
  exact ⟨hlower, hupper⟩

/-! ## Exact target and monotone halves of Lemma 1.6(ii) -/

/-- Exact natural-cutoff formulation of Tao's Lemma 1.6(ii).  For every
fixed positive real multiplier, the one-term bad-set count at the floored
dilated endpoint is eventually comparable to the original count.  This is a
definition of the remaining theorem target, not an assumption. -/
def TaoLemma16iiConclusion : Prop :=
  ∀ c : ℝ, 0 < c →
    (fun x => (badOneTermCount (taoNaturalDilation c x) : ℝ)) =Θ[atTop]
      fun x => (badOneTermCount x : ℝ)

/-- The easy monotone half of Lemma 1.6(ii) for a contraction. -/
theorem badOneTermCount_naturalDilation_le_of_le_one
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : ℕ) :
    badOneTermCount (taoNaturalDilation c x) ≤ badOneTermCount x :=
  countUpTo_mono_right (taoNaturalDilation_le_self hc0 hc1 x)

/-- The easy monotone half of Lemma 1.6(ii) for an expansion. -/
theorem badOneTermCount_le_naturalDilation_of_one_le
    {c : ℝ} (hc1 : 1 ≤ c) (x : ℕ) :
    badOneTermCount x ≤ badOneTermCount (taoNaturalDilation c x) :=
  countUpTo_mono_right (self_le_taoNaturalDilation hc1 x)

end Tao2026
