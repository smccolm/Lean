import Tao2026.FactorialShortIntervals
import Tao2026.NonTypicalBadIntervals
import Tao2026.PublicStatements

/-!
# Source scales for typical bad intervals

This module specializes the cutoff-parametrized Section 6 definitions to the
literal scales in Tao's paper.  Natural ceilings make the conditions exact:
`H < ceil((log x)^20)` and `d ≥ ceil(z(x)^3)` imply the corresponding real
inequalities without hidden rounding conventions.
-/

open Filter Asymptotics Topology

namespace Tao2026

/-- Natural cutoff encoding condition (i), `H < log^20 x`. -/
noncomputable def taoTypicalLengthCutoff (x : ℕ) : ℕ :=
  ⌈(Real.log x) ^ (20 : ℕ)⌉₊

/-- Natural cutoff encoding condition (ii), `d ≥ z^3`. -/
noncomputable def taoTypicalSquareThreshold (x : ℕ) : ℕ :=
  ⌈(taoZ x) ^ (3 : ℕ)⌉₊

/-- The explicit exceptional set for condition (ii) at Tao's source scales. -/
noncomputable def taoLargeSquareExceptionalSet (x : ℕ) : Finset ℕ :=
  largeSquareMultipleNeighborhood x (taoTypicalSquareThreshold x)
    (taoTypicalLengthCutoff x)

/-- The actual finite family of comparable-scale normalized intervals which
are short at the source cutoff but fail condition (ii). -/
noncomputable def taoLargeSquareFailureIndices (x : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (scaleNormalizedBadIntervalIndices x).filter fun NH =>
    NH.2 < taoTypicalLengthCutoff x ∧
      ¬AvoidsSquareMultiplesAtLeast NH.1 NH.2
        (taoTypicalSquareThreshold x)

/-- Union of the source-scale normalized intervals in the condition-(ii)
failure branch of Proposition 6.5. -/
noncomputable def taoLargeSquareFailureUnion (x : ℕ) : Finset ℕ := by
  classical
  exact (taoLargeSquareFailureIndices x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

theorem taoZ_pos (x : ℕ) : 0 < taoZ x := by
  rw [taoZ]
  exact Real.exp_pos _

theorem taoTypicalLengthCutoff_spec (x : ℕ) :
    (Real.log x) ^ (20 : ℕ) ≤ (taoTypicalLengthCutoff x : ℝ) := by
  rw [taoTypicalLengthCutoff]
  exact Nat.le_ceil _

theorem taoTypicalSquareThreshold_spec (x : ℕ) :
    (taoZ x) ^ (3 : ℕ) ≤ (taoTypicalSquareThreshold x : ℝ) := by
  rw [taoTypicalSquareThreshold]
  exact Nat.le_ceil _

theorem taoTypicalSquareThreshold_pos (x : ℕ) :
    0 < taoTypicalSquareThreshold x := by
  have hcast : (0 : ℝ) < (taoTypicalSquareThreshold x : ℝ) :=
    (pow_pos (taoZ_pos x) 3).trans_le (taoTypicalSquareThreshold_spec x)
  exact_mod_cast hcast

theorem mem_taoLargeSquareFailureIndices {x N H : ℕ} :
    (N, H) ∈ taoLargeSquareFailureIndices x ↔
      (N, H) ∈ scaleNormalizedBadIntervalIndices x ∧
        H < taoTypicalLengthCutoff x ∧
        ¬AvoidsSquareMultiplesAtLeast N H
          (taoTypicalSquareThreshold x) := by
  classical
  simp [taoLargeSquareFailureIndices]

/-- The entire condition-(ii) failure union lies in the explicit
large-square neighborhood cover. -/
theorem taoLargeSquareFailureUnion_subset_exceptionalSet (x : ℕ) :
    taoLargeSquareFailureUnion x ⊆ taoLargeSquareExceptionalSet x := by
  classical
  intro n hn
  obtain ⟨⟨N, H⟩, hNH, hnInterval⟩ :=
    Finset.mem_biUnion.mp hn
  rw [mem_taoLargeSquareFailureIndices] at hNH
  have hscale := (mem_scaleNormalizedBadIntervalIndices.mp hNH.1).2.2
  exact (hscale.largeSquare_failure_subset
    (taoTypicalSquareThreshold_pos x) hNH.2.1 hNH.2.2) hnInterval

theorem card_taoLargeSquareFailureUnion_le_exceptionalSet (x : ℕ) :
    (taoLargeSquareFailureUnion x).card ≤
      (taoLargeSquareExceptionalSet x).card :=
  Finset.card_le_card (taoLargeSquareFailureUnion_subset_exceptionalSet x)

theorem tendsto_iteratedLog_atTop :
    Tendsto iteratedLog atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Tao's saddle-point smoothness scale tends to infinity. -/
theorem tendsto_taoZ_atTop : Tendsto taoZ atTop atTop := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtLog : Tendsto (fun x : ℕ => Real.sqrt (Real.log x))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hlog
  have hc : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  have hbase : Tendsto
      (fun x : ℕ => (1 / Real.sqrt 2) * Real.sqrt (Real.log x))
      atTop atTop := hsqrtLog.const_mul_atTop hc
  have hsqrtIterOne : ∀ᶠ x : ℕ in atTop,
      1 ≤ Real.sqrt (iteratedLog x) := by
    filter_upwards [tendsto_iteratedLog_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with x hx
    have hsqrtNonneg := Real.sqrt_nonneg (iteratedLog x)
    have hsqrtSq := Real.sq_sqrt (by linarith : 0 ≤ iteratedLog x)
    nlinarith
  have hexponent : Tendsto (fun x : ℕ =>
      (1 / Real.sqrt 2) * Real.sqrt (Real.log x) *
        Real.sqrt (iteratedLog x)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hbase
    filter_upwards [hsqrtIterOne,
      hbase.eventually (eventually_ge_atTop (0 : ℝ))] with x hiter hnonneg
    exact le_mul_of_one_le_right hnonneg hiter
  exact Real.tendsto_exp_atTop.comp hexponent

/-- Exact logarithm of Tao's smoothness scale. -/
theorem log_taoZ (x : ℕ) :
    Real.log (taoZ x) =
      (1 / Real.sqrt 2) * Real.sqrt (Real.log x) *
        Real.sqrt (iteratedLog x) := by
  rw [taoZ, Real.log_exp]

/-- The iterated logarithm is negligible compared with `log z`. -/
theorem tendsto_iteratedLog_div_log_taoZ_zero :
    Tendsto (fun x : ℕ => iteratedLog x / Real.log (taoZ x))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun x : ℕ =>
      (iteratedLog x) ^ (1 / 2 : ℝ) /
        (Real.log x) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa [iteratedLog] using
      ((isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp hlog)
  have hscaled : Tendsto (fun x : ℕ =>
      Real.sqrt 2 * ((iteratedLog x) ^ (1 / 2 : ℝ) /
        (Real.log x) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hbase
  apply hscaled.congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hlogPos hiterPos
  rw [log_taoZ]
  simp_rw [← Real.sqrt_eq_rpow]
  have hsqrtTwoPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtLogPos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlogPos
  have hsqrtIterPos : 0 < Real.sqrt (iteratedLog x) := Real.sqrt_pos.2 hiterPos
  field_simp [hsqrtTwoPos.ne', hsqrtLogPos.ne', hsqrtIterPos.ne']
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hiterPos.le]

/-- Wherever both logarithmic source scales are positive, Tao's `u₀` is
exactly `log x / log z`. -/
theorem log_div_log_taoZ_eq_taoUZero
    {x : ℕ} (hlog : 0 < Real.log x) (hiter : 0 < iteratedLog x) :
    Real.log x / Real.log (taoZ x) = taoUZero x := by
  have hsqrtTwoPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtLogPos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlog
  have hsqrtIterPos : 0 < Real.sqrt (iteratedLog x) := Real.sqrt_pos.2 hiter
  rw [log_taoZ, taoUZero]
  field_simp [hsqrtTwoPos.ne', hsqrtLogPos.ne', hsqrtIterPos.ne']
  exact (Real.sq_sqrt hlog.le).symm

/-- Tao's saddle parameter `u₀` tends to infinity. -/
theorem tendsto_taoUZero_atTop : Tendsto taoUZero atTop atTop := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmallReal := (Real.isLittleO_pow_log_id_atTop (n := 2)).def
    (by norm_num : (0 : ℝ) < 1)
  have hsmall := hlog.eventually hsmallReal
  have hsqrtIter : Tendsto (fun x : ℕ => Real.sqrt (iteratedLog x))
      atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_iteratedLog_atTop
  refine tendsto_atTop_mono' atTop ?_ hsqrtIter
  filter_upwards [hsmall,
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hxsmall hlogOne hiterOne
  have hlogNonneg : 0 ≤ Real.log x := hlogOne.trans' zero_le_one
  have hiterNonneg : 0 ≤ iteratedLog x := hiterOne.trans' zero_le_one
  have hsq : (iteratedLog x) ^ (2 : ℕ) ≤ Real.log x := by
    have habsIter : |Real.log (Real.log (x : ℝ))| =
        Real.log (Real.log (x : ℝ)) := by
      rw [abs_of_nonneg]
      simpa [iteratedLog] using hiterNonneg
    simpa only [Function.id_def, iteratedLog, Real.norm_eq_abs,
      abs_pow, habsIter, abs_of_nonneg hlogNonneg, one_mul] using hxsmall
  have hiterLeSqrt : iteratedLog x ≤ Real.sqrt (Real.log x) := by
    have hsqrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hiterNonneg] at hsqrt
    exact hsqrt
  have hsqrtTwoOne : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg (2 : ℝ)]
  have hsqrtIterPos : 0 < Real.sqrt (iteratedLog x) :=
    Real.sqrt_pos.2 (by linarith)
  rw [taoUZero, le_div_iff₀ hsqrtIterPos]
  calc
    Real.sqrt (iteratedLog x) * Real.sqrt (iteratedLog x) =
        iteratedLog x := Real.mul_self_sqrt hiterNonneg
    _ ≤ Real.sqrt (Real.log x) := hiterLeSqrt
    _ ≤ Real.sqrt 2 * Real.sqrt (Real.log x) :=
      le_mul_of_one_le_left (Real.sqrt_nonneg _) hsqrtTwoOne

/-- The logarithm of the critical Rankin scale is negligible compared with
`log z`, the formal source-scale identity behind `u₀ ^ u₀ = z^(1+o(1))`. -/
theorem tendsto_log_taoUZero_div_log_taoZ_zero :
    Tendsto (fun x : ℕ => Real.log (taoUZero x) / Real.log (taoZ x))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have hconstant : Tendsto (fun x : ℕ =>
      Real.log (Real.sqrt 2) / Real.log (taoZ x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogZ
  have hhalf : Tendsto (fun x : ℕ =>
      (1 / 2 : ℝ) * (iteratedLog x / Real.log (taoZ x)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul tendsto_iteratedLog_div_log_taoZ_zero
  have hupper : Tendsto (fun x : ℕ =>
      (Real.log (Real.sqrt 2) + iteratedLog x / 2) /
        Real.log (taoZ x)) atTop (𝓝 0) := by
    have hadd := hconstant.add hhalf
    have haddZero : Tendsto (fun x : ℕ =>
        Real.log (Real.sqrt 2) / Real.log (taoZ x) +
          (1 / 2 : ℝ) * (iteratedLog x / Real.log (taoZ x)))
        atTop (𝓝 0) := by simpa using hadd
    apply haddZero.congr'
    filter_upwards with x
    ring
  apply squeeze_zero'
  · filter_upwards [tendsto_taoUZero_atTop.eventually
      (eventually_ge_atTop (1 : ℝ)),
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
        x huOne hzOne
    exact div_nonneg (Real.log_nonneg huOne) (Real.log_pos hzOne).le
  · filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_iteratedLog_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      tendsto_taoUZero_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
        x hlogPos hiterOne huZeroPos hzOne
    have hsqrtIterPos : 0 < Real.sqrt (iteratedLog x) :=
      Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hiterOne)
    have hsqrtIterOne : 1 ≤ Real.sqrt (iteratedLog x) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ iteratedLog x by positivity),
        Real.sqrt_nonneg (iteratedLog x)]
    have huZeroBound : taoUZero x ≤
        Real.sqrt 2 * Real.sqrt (Real.log x) := by
      rw [taoUZero, div_le_iff₀ hsqrtIterPos]
      exact le_mul_of_one_le_right (by positivity) hsqrtIterOne
    have hlogUpper : Real.log (taoUZero x) ≤
        Real.log (Real.sqrt 2) + iteratedLog x / 2 := by
      calc
        Real.log (taoUZero x) ≤
            Real.log (Real.sqrt 2 * Real.sqrt (Real.log x)) :=
          Real.log_le_log huZeroPos huZeroBound
        _ = Real.log (Real.sqrt 2) + iteratedLog x / 2 := by
          rw [Real.log_mul (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
            (Real.sqrt_pos.2 hlogPos).ne', Real.log_sqrt hlogPos.le]
          rfl
    exact div_le_div_of_nonneg_right hlogUpper (Real.log_pos hzOne).le
  · exact hupper

/-- Exact quotient between Tao's Rankin scale and the logarithmic smoothness
scale. -/
theorem taoUZero_div_log_taoZ_eq
    {x : ℕ} (hlog : 0 < Real.log x) (hiter : 0 < iteratedLog x) :
    taoUZero x / Real.log (taoZ x) = 2 / iteratedLog x := by
  have hsqrtTwoPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtLogPos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlog
  have hsqrtIterPos : 0 < Real.sqrt (iteratedLog x) := Real.sqrt_pos.2 hiter
  rw [taoUZero, log_taoZ]
  field_simp [hsqrtTwoPos.ne', hsqrtLogPos.ne', hsqrtIterPos.ne']
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hiter.le]

/-- Tao's Rankin scale is negligible compared with `log z`. -/
theorem tendsto_taoUZero_div_log_taoZ_zero :
    Tendsto (fun x : ℕ => taoUZero x / Real.log (taoZ x))
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℕ => 2 / iteratedLog x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_iteratedLog_atTop
  apply hbase.congr'
  filter_upwards [
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hlogPos hiterPos
  exact (taoUZero_div_log_taoZ_eq hlogPos hiterPos).symm

/-- Exact logarithm of Tao's critical Rankin scale. -/
theorem log_taoUZero_eq
    {x : ℕ} (hlog : 0 < Real.log x) (hiter : 0 < iteratedLog x) :
    Real.log (taoUZero x) =
      Real.log (Real.sqrt 2) + iteratedLog x / 2 -
        Real.log (iteratedLog x) / 2 := by
  have hsqrtTwoPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtLogPos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlog
  have hsqrtIterPos : 0 < Real.sqrt (iteratedLog x) := Real.sqrt_pos.2 hiter
  rw [taoUZero, Real.log_div (mul_ne_zero hsqrtTwoPos.ne' hsqrtLogPos.ne')
    hsqrtIterPos.ne', Real.log_mul hsqrtTwoPos.ne' hsqrtLogPos.ne',
    Real.log_sqrt hlog.le, Real.log_sqrt hiter.le]
  rfl

/-- The logarithm of `u₀` is asymptotic to half the iterated logarithm. -/
theorem tendsto_log_taoUZero_div_iteratedLog :
    Tendsto (fun x : ℕ => Real.log (taoUZero x) / iteratedLog x)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hconstant : Tendsto (fun x : ℕ =>
      Real.log (Real.sqrt 2) / iteratedLog x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_iteratedLog_atTop
  have hlogRatio : Tendsto (fun x : ℕ =>
      Real.log (iteratedLog x) / iteratedLog x) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_iteratedLog_atTop
  have honeHalf : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hhalfLog : Tendsto (fun x : ℕ =>
      (1 / 2 : ℝ) * (Real.log (iteratedLog x) / iteratedLog x))
      atTop (𝓝 0) := by
    simpa using honeHalf.mul hlogRatio
  have hcombined := (hconstant.add honeHalf).sub hhalfLog
  have hcombined' : Tendsto (fun x : ℕ =>
      Real.log (Real.sqrt 2) / iteratedLog x + (1 / 2 : ℝ) -
        (1 / 2 : ℝ) * (Real.log (iteratedLog x) / iteratedLog x))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using hcombined
  apply hcombined'.congr'
  filter_upwards [
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hlogPos hiterPos
  rw [log_taoUZero_eq hlogPos hiterPos]
  field_simp [hiterPos.ne']

/-- Formal version of the paper's critical identity
`u₀ ^ u₀ = z^(1+o(1))`. -/
theorem tendsto_taoUZero_mul_log_div_log_taoZ_one :
    Tendsto (fun x : ℕ =>
      taoUZero x * Real.log (taoUZero x) / Real.log (taoZ x))
      atTop (𝓝 1) := by
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hscaled := htwo.mul tendsto_log_taoUZero_div_iteratedLog
  have hscaled' : Tendsto (fun x : ℕ =>
      2 * (Real.log (taoUZero x) / iteratedLog x)) atTop (𝓝 1) := by
    simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hlogPos hiterPos
  have hratio := taoUZero_div_log_taoZ_eq hlogPos hiterPos
  calc
    2 * (Real.log (taoUZero x) / iteratedLog x) =
        (2 / iteratedLog x) * Real.log (taoUZero x) := by ring
    _ = (taoUZero x / Real.log (taoZ x)) * Real.log (taoUZero x) := by
      rw [hratio]
    _ = taoUZero x * Real.log (taoUZero x) / Real.log (taoZ x) := by ring

/-- Exact form of the scale ratio that controls the critical dyadic depth. -/
theorem log_taoZ_div_taoUZero_sq_eq
    {x : ℕ} (hlog : 0 < Real.log x) (hiter : 0 < iteratedLog x) :
    Real.log (taoZ x) / taoUZero x ^ (2 : ℕ) =
      Real.sqrt (iteratedLog x) ^ (3 : ℕ) /
        (2 * Real.sqrt 2 * Real.sqrt (Real.log x)) := by
  have hsqrtTwoPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtLogPos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlog
  have hsqrtIterPos : 0 < Real.sqrt (iteratedLog x) := Real.sqrt_pos.2 hiter
  rw [log_taoZ, taoUZero]
  field_simp [hsqrtTwoPos.ne', hsqrtLogPos.ne', hsqrtIterPos.ne']
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hlog.le, Real.sq_sqrt hiter.le]

/-- The logarithm of `z` is negligible compared with `u₀²`; this is the
source-scale growth fact behind the critical dyadic-prefix absorption. -/
theorem tendsto_log_taoZ_div_taoUZero_sq_zero :
    Tendsto (fun x : ℕ => Real.log (taoZ x) / taoUZero x ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun x : ℕ =>
      (iteratedLog x) ^ (3 / 2 : ℝ) /
        (Real.log x) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa [iteratedLog] using
      ((isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp hlog)
  have hscaled : Tendsto (fun x : ℕ =>
      (1 / (2 * Real.sqrt 2) : ℝ) *
        ((iteratedLog x) ^ (3 / 2 : ℝ) /
          (Real.log x) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hbase)
  apply hscaled.congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hlogPos hiterPos
  rw [log_taoZ_div_taoUZero_sq_eq hlogPos hiterPos]
  simp_rw [Real.sqrt_eq_rpow]
  have hiterNonneg : 0 ≤ iteratedLog x := hiterPos.le
  rw [← Real.rpow_natCast, ← Real.rpow_mul hiterNonneg]
  norm_num
  ring

theorem tendsto_taoZ_cube_atTop :
    Tendsto (fun x : ℕ => (taoZ x) ^ (3 : ℕ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_taoZ_atTop
  filter_upwards [tendsto_taoZ_atTop.eventually
    (eventually_ge_atTop (1 : ℝ))] with x hx
  calc
    taoZ x ≤ taoZ x * taoZ x :=
      le_mul_of_one_le_right (taoZ_pos x).le hx
    _ ≤ taoZ x * taoZ x * taoZ x :=
      le_mul_of_one_le_right (mul_nonneg (taoZ_pos x).le (taoZ_pos x).le) hx
    _ = (taoZ x) ^ (3 : ℕ) := by ring

theorem eventually_two_le_taoTypicalSquareThreshold :
    ∀ᶠ x : ℕ in atTop, 2 ≤ taoTypicalSquareThreshold x := by
  filter_upwards [tendsto_taoZ_cube_atTop.eventually
    (eventually_ge_atTop (2 : ℝ))] with x hx
  have hcast : (2 : ℝ) ≤ (taoTypicalSquareThreshold x : ℝ) :=
    hx.trans (taoTypicalSquareThreshold_spec x)
  exact_mod_cast hcast

/-- The closed reciprocal-square estimate with the source ceilings removed.
The constant `12` is explicit; no asymptotic notation is used. -/
theorem eventually_card_taoLargeSquareExceptionalSet_cast_le_source :
    ∀ᶠ x : ℕ in atTop,
      ((taoLargeSquareExceptionalSet x).card : ℝ) ≤
        12 * (x : ℝ) * ((Real.log x) ^ (20 : ℕ) + 1) /
          (taoZ x) ^ (3 : ℕ) := by
  filter_upwards [eventually_two_le_taoTypicalSquareThreshold,
    tendsto_taoZ_cube_atTop.eventually
      (eventually_ge_atTop (2 : ℝ))] with x hthreshold hzCubeTwo
  let P : ℝ := (Real.log x) ^ (20 : ℕ)
  let Z : ℝ := (taoZ x) ^ (3 : ℕ)
  have hraw := card_largeSquareMultipleNeighborhood_cast_le
    (x := x) (L := taoTypicalLengthCutoff x) hthreshold
  have hPnonneg : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hlengthLt : (taoTypicalLengthCutoff x : ℝ) < P + 1 := by
    simpa only [taoTypicalLengthCutoff, P] using
      Nat.ceil_lt_add_one hPnonneg
  have hlengthFactor :
      ((2 * taoTypicalLengthCutoff x + 1 : ℕ) : ℝ) ≤ 3 * (P + 1) := by
    push_cast
    linarith
  have hnum :
      ((2 * taoTypicalLengthCutoff x + 1 : ℕ) : ℝ) * (2 * x : ℕ) ≤
        6 * (x : ℝ) * (P + 1) := by
    norm_num at hlengthFactor ⊢
    nlinarith [show (0 : ℝ) ≤ (x : ℝ) by positivity]
  have hthresholdOne : 1 ≤ taoTypicalSquareThreshold x := by omega
  have hthresholdSpec : Z ≤ (taoTypicalSquareThreshold x : ℝ) := by
    simpa only [Z] using taoTypicalSquareThreshold_spec x
  have hden : Z / 2 ≤ ((taoTypicalSquareThreshold x - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hthresholdOne]
    norm_num at hthresholdSpec ⊢
    linarith
  have hZpos : 0 < Z := by dsimp only [Z]; positivity
  have hfrac :
      ((2 * taoTypicalLengthCutoff x + 1 : ℕ) : ℝ) * (2 * x : ℕ) /
          ((taoTypicalSquareThreshold x - 1 : ℕ) : ℝ) ≤
        (6 * (x : ℝ) * (P + 1)) / (Z / 2) := by
    exact div_le_div₀ (by positivity) hnum (half_pos hZpos) hden
  calc
    ((taoLargeSquareExceptionalSet x).card : ℝ)
        ≤ ((2 * taoTypicalLengthCutoff x + 1 : ℕ) : ℝ) * (2 * x : ℕ) /
            ((taoTypicalSquareThreshold x - 1 : ℕ) : ℝ) := by
          simpa only [taoLargeSquareExceptionalSet] using hraw
    _ ≤ (6 * (x : ℝ) * (P + 1)) / (Z / 2) := hfrac
    _ = 12 * (x : ℝ) * ((Real.log x) ^ (20 : ℕ) + 1) /
          (taoZ x) ^ (3 : ℕ) := by
          dsimp only [P, Z]
          field_simp [ne_of_gt (taoZ_pos x)]
          ring

/-- A fixed logarithmic power is eventually absorbed by half of Tao's
saddle-point exponential.  This is the quantitative comparison needed to
turn the reciprocal-square estimate into the paper's `z^{-2-δ}` saving. -/
theorem eventually_log_pow_twenty_add_one_le_two_mul_sqrt_taoZ :
    ∀ᶠ x : ℕ in atTop,
      (Real.log x) ^ (20 : ℕ) + 1 ≤ 2 * Real.sqrt (taoZ x) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : (fun x : ℕ => iteratedLog x) =o[atTop]
      (fun x : ℕ => Real.log x) := by
    simpa only [iteratedLog, Function.comp_def] using
      Real.isLittleO_log_id_atTop.comp_tendsto hlog
  filter_upwards [hsmall.bound (show (0 : ℝ) < 1 / 6400 by norm_num),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with x hcomparison hlogOne hiterOne
  have hiterNonneg : 0 ≤ iteratedLog x := zero_le_one.trans hiterOne
  have hlogNonneg : 0 ≤ Real.log x := zero_le_one.trans hlogOne
  rw [Real.norm_of_nonneg hiterNonneg,
    Real.norm_of_nonneg hlogNonneg] at hcomparison
  have hsqrtLogNonneg : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hsqrtIterNonneg : 0 ≤ Real.sqrt (iteratedLog x) := Real.sqrt_nonneg _
  have hsqrtLogSq : (Real.sqrt (Real.log x)) ^ 2 = Real.log x :=
    Real.sq_sqrt hlogNonneg
  have hsqrtIterSq : (Real.sqrt (iteratedLog x)) ^ 2 = iteratedLog x :=
    Real.sq_sqrt hiterNonneg
  have hroot : 80 * Real.sqrt (iteratedLog x) ≤
      Real.sqrt (Real.log x) := by
    norm_num at hcomparison
    nlinarith
  have hquarter : 20 * iteratedLog x ≤
      (1 / 4 : ℝ) * Real.sqrt (Real.log x) *
        Real.sqrt (iteratedLog x) := by
    have hmul := mul_nonneg
      (sub_nonneg.mpr hroot) hsqrtIterNonneg
    nlinarith
  have hsqrtTwoPos : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsqrtTwoSq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtTwoLeTwo : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith
  have hcoeff : (1 / 4 : ℝ) ≤ (1 / Real.sqrt 2) / 2 := by
    rw [show (1 / Real.sqrt 2) / 2 = (1 / 2) / Real.sqrt 2 by ring]
    exact (le_div_iff₀ hsqrtTwoPos).2 (by nlinarith)
  have hcoefficientProduct :
      (1 / 4 : ℝ) * Real.sqrt (Real.log x) *
          Real.sqrt (iteratedLog x) ≤
        ((1 / Real.sqrt 2) * Real.sqrt (Real.log x) *
          Real.sqrt (iteratedLog x)) / 2 := by
    have hproductNonneg : 0 ≤ Real.sqrt (Real.log x) *
        Real.sqrt (iteratedLog x) :=
      mul_nonneg hsqrtLogNonneg hsqrtIterNonneg
    have hmul := mul_nonneg (sub_nonneg.mpr hcoeff) hproductNonneg
    nlinarith
  have hexponent : 20 * iteratedLog x ≤
      ((1 / Real.sqrt 2) * Real.sqrt (Real.log x) *
        Real.sqrt (iteratedLog x)) / 2 :=
    hquarter.trans hcoefficientProduct
  have hlogPos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlogOne
  have hpow : (Real.log x) ^ (20 : ℕ) ≤ Real.sqrt (taoZ x) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hlogPos,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos (taoZ_pos x), taoZ,
      Real.log_exp]
    apply Real.exp_le_exp.mpr
    norm_num
    convert hexponent using 1 <;> simp only [iteratedLog] <;> ring
  have htaoZOne : 1 ≤ taoZ x := by
    rw [taoZ, Real.one_le_exp_iff]
    positivity
  have hsqrtTaoZOne : 1 ≤ Real.sqrt (taoZ x) :=
    Real.one_le_sqrt.mpr htaoZOne
  linarith

/-- The large-square branch has the explicit `z^{-5/2}` saving promised in
the weak alternative of Proposition 6.5. -/
theorem eventually_card_taoLargeSquareExceptionalSet_cast_le :
    ∀ᶠ x : ℕ in atTop,
      ((taoLargeSquareExceptionalSet x).card : ℝ) ≤
        24 * (x : ℝ) / (taoZ x) ^ ((5 : ℝ) / 2) := by
  filter_upwards [eventually_card_taoLargeSquareExceptionalSet_cast_le_source,
    eventually_log_pow_twenty_add_one_le_two_mul_sqrt_taoZ] with x hsource habsorb
  calc
    ((taoLargeSquareExceptionalSet x).card : ℝ)
        ≤ 12 * (x : ℝ) * ((Real.log x) ^ (20 : ℕ) + 1) /
            (taoZ x) ^ (3 : ℕ) := hsource
    _ ≤ 12 * (x : ℝ) * (2 * Real.sqrt (taoZ x)) /
          (taoZ x) ^ (3 : ℕ) := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left habsorb (by positivity)
        · exact pow_nonneg (taoZ_pos x).le 3
    _ = 24 * (x : ℝ) / (taoZ x) ^ ((5 : ℝ) / 2) := by
        have hz := taoZ_pos x
        rw [Real.sqrt_eq_rpow]
        rw [show (5 : ℝ) / 2 = 3 - 1 / 2 by norm_num,
          Real.rpow_sub hz]
        rw [← Real.rpow_natCast (taoZ x) 3]
        field_simp [ne_of_gt hz, ne_of_gt (Real.rpow_pos_of_pos hz (1 / 2))]
        ring_nf

/-- Asymptotic form of the preceding explicit estimate. -/
theorem card_taoLargeSquareExceptionalSet_isBigO :
    (fun x : ℕ => ((taoLargeSquareExceptionalSet x).card : ℝ))
      =O[atTop] fun x : ℕ =>
        (x : ℝ) / (taoZ x) ^ ((5 : ℝ) / 2) := by
  apply IsBigO.of_bound 24
  filter_upwards [eventually_card_taoLargeSquareExceptionalSet_cast_le] with x hx
  rw [Real.norm_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((taoLargeSquareExceptionalSet x).card : ℝ)),
    Real.norm_of_nonneg (div_nonneg (by positivity)
      (Real.rpow_nonneg (taoZ_pos x).le _))]
  simpa only [mul_div_assoc] using hx

/-- Source-shaped weak alternative: an explicit positive `δ` exists, here
`δ = 1/2`, for the condition-(ii) exceptional set. -/
theorem card_taoLargeSquareExceptionalSet_powerSaving :
    ∃ δ : ℝ, 0 < δ ∧
      (fun x : ℕ => ((taoLargeSquareExceptionalSet x).card : ℝ))
        =O[atTop] fun x : ℕ =>
          (x : ℝ) / (taoZ x) ^ (2 + δ) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  simpa only [show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num] using
    card_taoLargeSquareExceptionalSet_isBigO

/-- Direct cardinality estimate for the union named by Proposition 6.5's
condition-(ii) branch. -/
theorem eventually_card_taoLargeSquareFailureUnion_cast_le :
    ∀ᶠ x : ℕ in atTop,
      ((taoLargeSquareFailureUnion x).card : ℝ) ≤
        24 * (x : ℝ) / (taoZ x) ^ ((5 : ℝ) / 2) := by
  filter_upwards [eventually_card_taoLargeSquareExceptionalSet_cast_le] with x hx
  calc
    ((taoLargeSquareFailureUnion x).card : ℝ)
        ≤ ((taoLargeSquareExceptionalSet x).card : ℝ) := by
          exact_mod_cast card_taoLargeSquareFailureUnion_le_exceptionalSet x
    _ ≤ 24 * (x : ℝ) / (taoZ x) ^ ((5 : ℝ) / 2) := hx

/-- Source-shaped weak alternative for the actual interval union, with the
explicit witness `δ = 1/2`. -/
theorem card_taoLargeSquareFailureUnion_powerSaving :
    ∃ δ : ℝ, 0 < δ ∧
      (fun x : ℕ => ((taoLargeSquareFailureUnion x).card : ℝ))
        =O[atTop] fun x : ℕ =>
          (x : ℝ) / (taoZ x) ^ (2 + δ) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  apply IsBigO.of_bound 24
  filter_upwards [eventually_card_taoLargeSquareFailureUnion_cast_le] with x hx
  rw [Real.norm_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((taoLargeSquareFailureUnion x).card : ℝ)),
    Real.norm_of_nonneg (div_nonneg (by positivity)
      (Real.rpow_nonneg (taoZ_pos x).le _))]
  norm_num
  simpa only [mul_div_assoc] using hx

end Tao2026
