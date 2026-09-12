import Tao2026.SmoothNumberHildebrand
import Tao2026.SmoothNumberLowerBound
import PrimeNumberTheoremAnd.Consequences

/-!
# Critical smooth-number lower bound

This module packages the endpoint-refined Hildebrand iteration at the exact
integral depth `Nat.log y X`.  The residual cutoff records the fractional
part of `log X / log y`; retaining its Chebyshev mass prevents the full
`O(log y)` rounding loss of the unrefined depth iteration.
-/

namespace Tao2026

open Filter Asymptotics Topology
open scoped BigOperators Chebyshev

noncomputable section

/-- Residual cutoff after removing the largest integral power of `y` forced
below `X`. -/
def smoothEndpointCutoff (X y : ℕ) : ℕ :=
  X / y ^ smoothLowerDepth X y

/-- The full-depth product with the residual cutoff still lies below `X`. -/
theorem pow_mul_smoothEndpointCutoff_le (X y : ℕ) :
    y ^ smoothLowerDepth X y * smoothEndpointCutoff X y ≤ X := by
  rw [smoothEndpointCutoff, mul_comm]
  exact Nat.div_mul_le_self X (y ^ smoothLowerDepth X y)

/-- The residual cutoff also gives the strict complementary division bound. -/
theorem lt_pow_mul_smoothEndpointCutoff_add_one (X y : ℕ) (hy : 0 < y) :
    X < y ^ smoothLowerDepth X y * (smoothEndpointCutoff X y + 1) := by
  have hpow : 0 < y ^ smoothLowerDepth X y := pow_pos hy _
  have hdiv : X < (X / y ^ smoothLowerDepth X y + 1) *
      y ^ smoothLowerDepth X y :=
    (Nat.div_lt_iff_lt_mul hpow).mp
      (Nat.lt_succ_self (X / y ^ smoothLowerDepth X y))
  simpa only [smoothEndpointCutoff, mul_comm] using hdiv

/-- For nonzero `X` and positive `y`, the residual cutoff is at least one. -/
theorem one_le_smoothEndpointCutoff {X y : ℕ}
    (hX : X ≠ 0) (hy : 0 < y) :
    1 ≤ smoothEndpointCutoff X y := by
  rw [smoothEndpointCutoff]
  apply (Nat.le_div_iff_mul_le (pow_pos hy _)).2
  simpa using pow_smoothLowerDepth_le (y := y) hX

/-- The residual cutoff is strictly below `y`, by maximality of
`Nat.log y X`. -/
theorem smoothEndpointCutoff_lt {X y : ℕ} (hy : 2 ≤ y) :
    smoothEndpointCutoff X y < y := by
  rw [smoothEndpointCutoff]
  apply (Nat.div_lt_iff_lt_mul (pow_pos (by omega : 0 < y) _)).2
  have hmax := Nat.lt_pow_succ_log_self (by omega : 1 < y) X
  simpa only [pow_succ, mul_comm] using hmax

/-- The endpoint is either the harmless bounded value `1` or it supports a
nonempty prime packet. -/
theorem smoothEndpointCutoff_eq_one_or_two_le {X y : ℕ}
    (hX : X ≠ 0) (hy : 2 ≤ y) :
    smoothEndpointCutoff X y = 1 ∨ 2 ≤ smoothEndpointCutoff X y := by
  have hone := one_le_smoothEndpointCutoff hX (by omega : 0 < y)
  omega

/-- Canonical endpoint-refined finite Hildebrand bound. -/
theorem endpointTheta_mul_theta_pow_le_psiNat_mul_log_pow
    {X y : ℕ} (hy : 2 ≤ y)
    (hend : 2 ≤ smoothEndpointCutoff X y) :
    Chebyshev.theta (smoothEndpointCutoff X y) *
        Chebyshev.theta y ^ smoothLowerDepth X y ≤
      (psiNat X y : ℝ) * Real.log X ^ (smoothLowerDepth X y + 1) := by
  exact chebyshevTheta_mul_pow_le_psiNat_mul_log_pow hend hy
    (smoothEndpointCutoff_lt hy).le (pow_mul_smoothEndpointCutoff_le X y)

/-- Quotient form of the canonical endpoint-refined bound. -/
theorem endpointTheta_mul_theta_pow_div_log_pow_le_psiNat
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hend : 2 ≤ smoothEndpointCutoff X y) :
    (Chebyshev.theta (smoothEndpointCutoff X y) *
        Chebyshev.theta y ^ smoothLowerDepth X y) /
        Real.log X ^ (smoothLowerDepth X y + 1) ≤
      (psiNat X y : ℝ) := by
  apply (div_le_iff₀ (pow_pos (Real.log_pos (by exact_mod_cast hX)) _)).2
  simpa only [mul_comm] using
    endpointTheta_mul_theta_pow_le_psiNat_mul_log_pow
      hy hend

/-- Optional endpoint factor.  When the residual cutoff is `1`, its missing
logarithmic mass is exactly zero, so the final packet is omitted rather than
introducing the vanishing value `theta(1)`. -/
def smoothEndpointThetaFactor (X y : ℕ) : ℝ :=
  if 2 ≤ smoothEndpointCutoff X y then
    Chebyshev.theta (smoothEndpointCutoff X y) / Real.log X
  else 1

/-- Uniform endpoint-recovered lower bound, valid without a case assumption
on the residual cutoff. -/
theorem endpointThetaFactor_mul_thetaDivLog_pow_le_psiNat
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothEndpointThetaFactor X y *
        (Chebyshev.theta y / Real.log X) ^ smoothLowerDepth X y ≤
      (psiNat X y : ℝ) := by
  by_cases hend : 2 ≤ smoothEndpointCutoff X y
  · rw [smoothEndpointThetaFactor, if_pos hend, div_pow]
    have hlogNe : Real.log (X : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hX)).ne'
    calc
      (Chebyshev.theta (smoothEndpointCutoff X y) / Real.log X) *
          (Chebyshev.theta y ^ smoothLowerDepth X y /
            Real.log X ^ smoothLowerDepth X y) =
          (Chebyshev.theta (smoothEndpointCutoff X y) *
            Chebyshev.theta y ^ smoothLowerDepth X y) /
              Real.log X ^ (smoothLowerDepth X y + 1) := by
        rw [pow_succ]
        field_simp [hlogNe]
      _ ≤ (psiNat X y : ℝ) :=
        endpointTheta_mul_theta_pow_div_log_pow_le_psiNat hX hy hend
  · rw [smoothEndpointThetaFactor, if_neg hend, one_mul]
    exact chebyshevTheta_div_log_pow_le_psiNat hy hX
      (pow_smoothLowerDepth_le (by omega : X ≠ 0))

/-- The pinned PNT supplies a fixed scale above which Chebyshev theta has at
least half of its main term. -/
theorem eventually_natCast_div_two_le_chebyshevTheta :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) / 2 ≤ Chebyshev.theta n := by
  have herrReal : ∀ᶠ t : ℝ in Filter.atTop,
      |Chebyshev.theta t - t| ≤ (1 / 2 : ℝ) * t := by
    have h := Asymptotics.IsEquivalent.isLittleO chebyshev_asymptotic
    rw [Asymptotics.isLittleO_iff] at h
    have hhalf := h (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℝ)] with t ht htPos
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at ht
    change |Chebyshev.theta t - t| ≤ (1 / 2 : ℝ) * |t| at ht
    rw [abs_of_pos htPos] at ht
    exact ht
  have herrNat : ∀ᶠ n : ℕ in Filter.atTop,
      |Chebyshev.theta (n : ℝ) - n| ≤ (1 / 2 : ℝ) * n :=
    tendsto_natCast_atTop_atTop.eventually herrReal
  filter_upwards [herrNat] with n hn
  rw [abs_le] at hn
  linarith

/-- A fixed natural PNT threshold, chosen large enough to be at least two. -/
theorem exists_chebyshevTheta_half_threshold :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      (b : ℝ) / 2 ≤ Chebyshev.theta b := by
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
    eventually_natCast_div_two_le_chebyshevTheta
  refine ⟨max 2 B, le_max_left _ _, ?_⟩
  intro b hb
  exact hB b ((le_max_right 2 B).trans hb)

/-- The same pinned-PNT threshold can harmlessly be chosen at least four.
This normalization is convenient when absorbing the endpoint division
remainder. -/
theorem exists_chebyshevTheta_half_threshold_four :
    ∃ B : ℕ, 4 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      (b : ℝ) / 2 ≤ Chebyshev.theta b := by
  obtain ⟨B, _hBTwo, hB⟩ := exists_chebyshevTheta_half_threshold
  refine ⟨max 4 B, le_max_left _ _, ?_⟩
  intro b hb
  exact hB b ((le_max_right 4 B).trans hb)

/-- Endpoint factor activated only beyond a fixed threshold.  This form is
uniformly suitable for asymptotics: an inactive endpoint is bounded by the
fixed threshold, while an active endpoint has PNT-scale theta mass. -/
def smoothEndpointThetaFactorAt (B X y : ℕ) : ℝ :=
  if B ≤ smoothEndpointCutoff X y then
    Chebyshev.theta (smoothEndpointCutoff X y) / Real.log X
  else 1

/-- Elementary endpoint mass supplied by the half-PNT estimate. -/
def smoothEndpointResidualAt (B X y : ℕ) : ℝ :=
  if B ≤ smoothEndpointCutoff X y then
    (smoothEndpointCutoff X y : ℝ) / 2
  else 1

/-- Normalized elementary endpoint mass used in the finite Hildebrand
product. -/
def smoothEndpointPNTFactorAt (B X y : ℕ) : ℝ :=
  if B ≤ smoothEndpointCutoff X y then
    ((smoothEndpointCutoff X y : ℝ) / 2) / Real.log X
  else 1

/-- The thresholded residual mass recovers the whole ambient cutoff up to
the fixed factor `B`.  The lower bound `B ≥ 4` absorbs both the division
remainder and the factor `1/2` in the active endpoint. -/
theorem natCast_le_B_mul_endpointResidualAt_mul_pow
    {B X y : ℕ} (hB : 4 ≤ B) (hy : 0 < y) :
    (X : ℝ) ≤ (B : ℝ) * smoothEndpointResidualAt B X y *
      (y : ℝ) ^ smoothLowerDepth X y := by
  have hupper := lt_pow_mul_smoothEndpointCutoff_add_one X y hy
  let b := smoothEndpointCutoff X y
  let q := y ^ smoothLowerDepth X y
  have hupperReal : (X : ℝ) ≤ (q : ℝ) * (b + 1 : ℕ) := by
    exact_mod_cast hupper.le
  by_cases hend : B ≤ b
  · have hfactor : ((b + 1 : ℕ) : ℝ) ≤ (B : ℝ) * ((b : ℝ) / 2) := by
      have hBReal : (4 : ℝ) ≤ B := by exact_mod_cast hB
      have hbReal : (B : ℝ) ≤ b := by exact_mod_cast hend
      push_cast
      nlinarith
    rw [smoothEndpointResidualAt, if_pos hend]
    dsimp only [b, q] at hupperReal hfactor ⊢
    calc
      (X : ℝ) ≤ (y ^ smoothLowerDepth X y : ℕ) *
          (smoothEndpointCutoff X y + 1 : ℕ) := hupperReal
      _ ≤ ((y ^ smoothLowerDepth X y : ℕ) : ℝ) *
          ((B : ℝ) * ((smoothEndpointCutoff X y : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hfactor
          (Nat.cast_nonneg (y ^ smoothLowerDepth X y))
      _ = (B : ℝ) * ((smoothEndpointCutoff X y : ℝ) / 2) *
          (y : ℝ) ^ smoothLowerDepth X y := by push_cast; ring
  · have hbB : b + 1 ≤ B := by omega
    rw [smoothEndpointResidualAt, if_neg hend, mul_one]
    dsimp only [b, q] at hupperReal hbB ⊢
    calc
      (X : ℝ) ≤ (y ^ smoothLowerDepth X y : ℕ) *
          (smoothEndpointCutoff X y + 1 : ℕ) := hupperReal
      _ ≤ ((y ^ smoothLowerDepth X y : ℕ) : ℝ) * (B : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hbB)
          (Nat.cast_nonneg (y ^ smoothLowerDepth X y))
      _ = (B : ℝ) * (y : ℝ) ^ smoothLowerDepth X y := by push_cast; ring

/-- Uniform finite lower bound with a thresholded endpoint packet. -/
theorem endpointThetaFactorAt_mul_thetaDivLog_pow_le_psiNat
    {B X y : ℕ} (hB : 2 ≤ B) (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothEndpointThetaFactorAt B X y *
        (Chebyshev.theta y / Real.log X) ^ smoothLowerDepth X y ≤
      (psiNat X y : ℝ) := by
  by_cases hend : B ≤ smoothEndpointCutoff X y
  · rw [smoothEndpointThetaFactorAt, if_pos hend, div_pow]
    have hendTwo : 2 ≤ smoothEndpointCutoff X y := hB.trans hend
    have hlogNe : Real.log (X : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hX)).ne'
    calc
      (Chebyshev.theta (smoothEndpointCutoff X y) / Real.log X) *
          (Chebyshev.theta y ^ smoothLowerDepth X y /
            Real.log X ^ smoothLowerDepth X y) =
          (Chebyshev.theta (smoothEndpointCutoff X y) *
            Chebyshev.theta y ^ smoothLowerDepth X y) /
              Real.log X ^ (smoothLowerDepth X y + 1) := by
        rw [pow_succ]
        field_simp [hlogNe]
      _ ≤ (psiNat X y : ℝ) :=
        endpointTheta_mul_theta_pow_div_log_pow_le_psiNat hX hy hendTwo
  · rw [smoothEndpointThetaFactorAt, if_neg hend, one_mul]
    exact chebyshevTheta_div_log_pow_le_psiNat hy hX
      (pow_smoothLowerDepth_le (by omega : X ≠ 0))

/-- Replace both Chebyshev factors by their elementary half-PNT lower
bounds.  The endpoint is activated at the same fixed threshold. -/
theorem endpointPNTFactorAt_mul_yHalfDivLog_pow_le_psiNat
    {B X y : ℕ} (hB : 2 ≤ B) (hX : 2 ≤ X) (hy : 2 ≤ y)
    (htheta : ∀ n : ℕ, B ≤ n → (n : ℝ) / 2 ≤ Chebyshev.theta n)
    (hBy : B ≤ y) :
    smoothEndpointPNTFactorAt B X y *
        ((y : ℝ) / 2 / Real.log X) ^ smoothLowerDepth X y ≤
      (psiNat X y : ℝ) := by
  apply le_trans ?_
    (endpointThetaFactorAt_mul_thetaDivLog_pow_le_psiNat hB hX hy)
  have hlogNonneg : 0 ≤ Real.log (X : ℝ) :=
    (Real.log_pos (by exact_mod_cast hX)).le
  have hyHalfNonneg : 0 ≤ (y : ℝ) / 2 := by positivity
  have hbase : (y : ℝ) / 2 / Real.log X ≤
      Chebyshev.theta y / Real.log X :=
    div_le_div_of_nonneg_right (htheta y hBy) hlogNonneg
  have hpow : ((y : ℝ) / 2 / Real.log X) ^ smoothLowerDepth X y ≤
      (Chebyshev.theta y / Real.log X) ^ smoothLowerDepth X y :=
    pow_le_pow_left₀ (div_nonneg hyHalfNonneg hlogNonneg) hbase _
  by_cases hend : B ≤ smoothEndpointCutoff X y
  · rw [smoothEndpointPNTFactorAt, smoothEndpointThetaFactorAt,
      if_pos hend, if_pos hend]
    exact mul_le_mul (div_le_div_of_nonneg_right
        (htheta _ hend) hlogNonneg) hpow
      (pow_nonneg (div_nonneg hyHalfNonneg hlogNonneg) _)
      (div_nonneg (Chebyshev.theta_nonneg _) hlogNonneg)
  · rw [smoothEndpointPNTFactorAt, smoothEndpointThetaFactorAt,
      if_neg hend, if_neg hend, one_mul, one_mul]
    exact hpow

/-- Explicit finite consequence of the endpoint-recovered Hildebrand
iteration.  Its denominator is deliberately displayed: its logarithm has
critical size `(2/α + o(1)) log z`, exposing the extra factor of two that a
sharp de Bruijn lower saddle must remove. -/
theorem self_div_endpointHildebrandDenominator_le_psiNat
    {B X y : ℕ} (hB : 4 ≤ B) (hX : 3 ≤ X) (hy : 2 ≤ y)
    (htheta : ∀ n : ℕ, B ≤ n → (n : ℝ) / 2 ≤ Chebyshev.theta n)
    (hBy : B ≤ y) :
    (X : ℝ) /
        ((B : ℝ) * 2 ^ smoothLowerDepth X y *
          Real.log X ^ (smoothLowerDepth X y + 1)) ≤
      (psiNat X y : ℝ) := by
  let d := smoothLowerDepth X y
  let R := smoothEndpointResidualAt B X y
  have hlogPos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogOne : 1 ≤ Real.log (X : ℝ) := by
    have hthree : (1 : ℝ) ≤ Real.log 3 := by
      linarith [Real.log_three_gt_d9]
    exact hthree.trans (Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3)
      (by show (0 : ℝ) < X; exact_mod_cast (show 0 < X by omega))
      (by exact_mod_cast hX))
  have hBPos : (0 : ℝ) < B := by positivity
  have hdenPos : 0 < (B : ℝ) * 2 ^ d * Real.log X ^ (d + 1) := by
    positivity
  have hambient : (X : ℝ) ≤ (B : ℝ) * R * (y : ℝ) ^ d := by
    simpa only [d, R] using
      natCast_le_B_mul_endpointResidualAt_mul_pow hB (by omega : 0 < y)
  have hquot :
      (X : ℝ) / ((B : ℝ) * 2 ^ d * Real.log X ^ (d + 1)) ≤
        R * (y : ℝ) ^ d / (2 ^ d * Real.log X ^ (d + 1)) := by
    rw [div_le_iff₀ hdenPos]
    have htwoPowPos : (0 : ℝ) < 2 ^ d := by positivity
    have hlogPowPos : 0 < Real.log (X : ℝ) ^ (d + 1) := pow_pos hlogPos _
    field_simp [hBPos.ne', htwoPowPos.ne', hlogPowPos.ne']
    nlinarith
  have hpacket :
      R * (y : ℝ) ^ d / (2 ^ d * Real.log X ^ (d + 1)) ≤
        smoothEndpointPNTFactorAt B X y *
          ((y : ℝ) / 2 / Real.log X) ^ d := by
    dsimp only [d, R]
    by_cases hend : B ≤ smoothEndpointCutoff X y
    · rw [smoothEndpointPNTFactorAt, smoothEndpointResidualAt,
        if_pos hend, if_pos hend]
      rw [div_pow, div_pow, pow_succ]
      field_simp [hlogPos.ne']
      apply le_refl
    · rw [smoothEndpointPNTFactorAt, smoothEndpointResidualAt,
        if_neg hend, if_neg hend, one_mul]
      rw [div_pow, div_pow, one_mul]
      have hnonneg : 0 ≤
          (y : ℝ) ^ smoothLowerDepth X y /
            (2 ^ smoothLowerDepth X y *
              Real.log X ^ smoothLowerDepth X y) := by positivity
      calc
        (y : ℝ) ^ smoothLowerDepth X y /
            (2 ^ smoothLowerDepth X y *
              Real.log X ^ (smoothLowerDepth X y + 1)) =
            ((y : ℝ) ^ smoothLowerDepth X y /
              (2 ^ smoothLowerDepth X y *
                Real.log X ^ smoothLowerDepth X y)) / Real.log X := by
              rw [pow_succ]
              field_simp [hlogPos.ne']
        _ ≤ (y : ℝ) ^ smoothLowerDepth X y /
              (2 ^ smoothLowerDepth X y *
                Real.log X ^ smoothLowerDepth X y) :=
          div_le_self hnonneg hlogOne
        _ = (y : ℝ) ^ smoothLowerDepth X y /
              2 ^ smoothLowerDepth X y /
                Real.log X ^ smoothLowerDepth X y := by
          have htwoNe : (2 : ℝ) ^ smoothLowerDepth X y ≠ 0 := by positivity
          have hlogNe : Real.log (X : ℝ) ^ smoothLowerDepth X y ≠ 0 :=
            pow_ne_zero _ hlogPos.ne'
          field_simp [htwoNe, hlogNe]
  exact hquot.trans (hpacket.trans
    (endpointPNTFactorAt_mul_yHalfDivLog_pow_le_psiNat
      (by omega) (by omega) hy htheta hBy))

/-! ## Asymptotic loss ledger for the finite Hildebrand packet -/

/-- Since `X=x^(1+o(1))`, its secondary logarithm is asymptotic to
`log₂ x`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_log_X_div_iteratedLog
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) :
    Tendsto (fun x => Real.log (Real.log (X x)) / iteratedLog x)
      atTop (𝓝 1) := by
  have hnormalized := hregime.1
  have hlogNormalized : Tendsto (fun x =>
      Real.log (Real.log (X x) / Real.log x)) atTop (𝓝 0) := by
    simpa using (Real.continuousAt_log one_ne_zero).tendsto.comp hnormalized
  have hcorrection := hlogNormalized.div_atTop tendsto_iteratedLog_atTop
  have hsum : Tendsto (fun x =>
      Real.log (Real.log (X x) / Real.log x) / iteratedLog x + 1)
      atTop (𝓝 1) := by
    simpa using hcorrection.add tendsto_const_nhds
  apply hsum.congr'
  filter_upwards [hnormalized.eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x hratioPos hlogxPos hiterPos
  simp only [Function.comp_apply] at hlogxPos
  have hproduct :
      (Real.log (X x) / Real.log x) * Real.log x = Real.log (X x) := by
    exact div_mul_cancel₀ _ hlogxPos.ne'
  have hlogProduct : Real.log (Real.log (X x)) =
      Real.log (Real.log (X x) / Real.log x) + iteratedLog x := by
    calc
      Real.log (Real.log (X x)) =
          Real.log ((Real.log (X x) / Real.log x) * Real.log x) :=
        congrArg Real.log hproduct.symm
      _ = Real.log (Real.log (X x) / Real.log x) +
          Real.log (Real.log x) :=
        Real.log_mul hratioPos.ne' hlogxPos.ne'
      _ = Real.log (Real.log (X x) / Real.log x) + iteratedLog x := rfl
  rw [hlogProduct]
  field_simp [hiterPos.ne']

/-- The secondary logarithm of `X` is twice the logarithm of the canonical
critical depth, to first order. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_log_X_div_log_smoothLowerDepth
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (Real.log (X x)) /
      Real.log (smoothLowerDepth (X x) (y x) : ℝ)) atTop (𝓝 2) := by
  have hquot :=
    (hregime.tendsto_log_log_X_div_iteratedLog).div
      (hregime.tendsto_log_smoothLowerDepth_div_iteratedLog hα)
      (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hquotTwo : Tendsto (fun x =>
      (Real.log (Real.log (X x)) / iteratedLog x) /
        (Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
          iteratedLog x)) atTop (𝓝 2) := by
    simpa using hquot
  apply hquotTwo.congr'
  filter_upwards [tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)),
    (hregime.tendsto_smoothLowerDepth_atTop hα).eventually
      (eventually_ge_atTop 2)] with x hiterPos hdTwo
  have hlogdPos : 0 < Real.log (smoothLowerDepth (X x) (y x) : ℝ) :=
    Real.log_pos (by exact_mod_cast hdTwo)
  field_simp [hiterPos.ne', hlogdPos.ne']

/-- The dominant loss in the finite Hildebrand packet is twice the desired
Dickman loss. -/
theorem IsTaoCriticalSmoothRegime.tendsto_depth_mul_log_log_X_div_log_taoZ
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x =>
      (smoothLowerDepth (X x) (y x) : ℝ) *
          Real.log (Real.log (X x)) / Real.log (taoZ x))
      atTop (𝓝 (2 / α)) := by
  have hproduct :=
    (hregime.tendsto_smoothLowerDepth_mul_log_div_log_taoZ hα).mul
      (hregime.tendsto_log_log_X_div_log_smoothLowerDepth hα)
  have hproduct' : Tendsto (fun x =>
      ((smoothLowerDepth (X x) (y x) : ℝ) *
          Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
            Real.log (taoZ x)) *
        (Real.log (Real.log (X x)) /
          Real.log (smoothLowerDepth (X x) (y x) : ℝ)))
      atTop (𝓝 (2 / α)) := by
    convert hproduct using 1
    all_goals field_simp [hα.ne']
  apply hproduct'.congr'
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ)),
    (hregime.tendsto_smoothLowerDepth_atTop hα).eventually
      (eventually_ge_atTop 2)] with x hzOne hdTwo
  have hlogzNe : Real.log (taoZ x) ≠ 0 := (Real.log_pos hzOne).ne'
  have hlogdNe : Real.log (smoothLowerDepth (X x) (y x) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hdTwo)).ne'
  field_simp [hlogzNe, hlogdNe]

theorem IsTaoCriticalSmoothRegime.tendsto_smoothLowerDepth_div_log_taoZ_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => (smoothLowerDepth (X x) (y x) : ℝ) /
      Real.log (taoZ x)) atTop (𝓝 0) := by
  have hproduct :=
    (hregime.tendsto_smoothLowerDepth_div_taoUZero hα).mul
      tendsto_taoUZero_div_log_taoZ_zero
  have hproductZero : Tendsto (fun x =>
      ((smoothLowerDepth (X x) (y x) : ℝ) / taoUZero x) *
        (taoUZero x / Real.log (taoZ x))) atTop (𝓝 0) := by
    simpa using hproduct
  apply hproductZero.congr'
  filter_upwards [tendsto_taoUZero_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x huPos hzOne
  field_simp [huPos.ne', (Real.log_pos hzOne).ne']

theorem IsTaoCriticalSmoothRegime.tendsto_log_log_X_div_log_taoZ_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) :
    Tendsto (fun x => Real.log (Real.log (X x)) /
      Real.log (taoZ x)) atTop (𝓝 0) := by
  have hproduct := hregime.tendsto_log_log_X_div_iteratedLog.mul
    tendsto_iteratedLog_div_log_taoZ_zero
  have hproductZero : Tendsto (fun x =>
      (Real.log (Real.log (X x)) / iteratedLog x) *
        (iteratedLog x / Real.log (taoZ x))) atTop (𝓝 0) := by
    simpa using hproduct
  apply hproductZero.congr'
  filter_upwards [tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hiterPos hzOne
  field_simp [hiterPos.ne', (Real.log_pos hzOne).ne']

/-- Exact asymptotic audit of the elementary endpoint-Hildebrand
denominator. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_endpointHildebrandDenominator
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    {B : ℕ} (hB : 1 ≤ B) :
    Tendsto (fun x =>
      Real.log ((B : ℝ) * 2 ^ smoothLowerDepth (X x) (y x) *
        Real.log (X x) ^ (smoothLowerDepth (X x) (y x) + 1)) /
          Real.log (taoZ x)) atTop (𝓝 (2 / α)) := by
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have hconst : Tendsto (fun x : ℕ => Real.log (B : ℝ) /
      Real.log (taoZ x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogZ
  have hdepthTwo : Tendsto (fun x =>
      (smoothLowerDepth (X x) (y x) : ℝ) * Real.log 2 /
        Real.log (taoZ x)) atTop (𝓝 0) := by
    have h := (hregime.tendsto_smoothLowerDepth_div_log_taoZ_zero hα).const_mul
      (Real.log 2)
    have hzero : Tendsto (fun x => Real.log 2 *
        ((smoothLowerDepth (X x) (y x) : ℝ) / Real.log (taoZ x)))
        atTop (𝓝 0) := by simpa using h
    apply hzero.congr'
    filter_upwards with x
    ring
  have hlogPower : Tendsto (fun x =>
      ((smoothLowerDepth (X x) (y x) : ℝ) + 1) *
          Real.log (Real.log (X x)) / Real.log (taoZ x))
      atTop (𝓝 (2 / α)) := by
    have h :=
      (hregime.tendsto_depth_mul_log_log_X_div_log_taoZ hα).add
        hregime.tendsto_log_log_X_div_log_taoZ_zero
    have hlimit : Tendsto (fun x =>
        (smoothLowerDepth (X x) (y x) : ℝ) *
            Real.log (Real.log (X x)) / Real.log (taoZ x) +
          Real.log (Real.log (X x)) / Real.log (taoZ x))
        atTop (𝓝 (2 / α)) := by simpa using h
    apply hlimit.congr'
    filter_upwards with x
    ring
  have hsum := (hconst.add hdepthTwo).add hlogPower
  have hsum' : Tendsto (fun x =>
      Real.log (B : ℝ) / Real.log (taoZ x) +
        (smoothLowerDepth (X x) (y x) : ℝ) * Real.log 2 /
          Real.log (taoZ x) +
        ((smoothLowerDepth (X x) (y x) : ℝ) + 1) *
          Real.log (Real.log (X x)) / Real.log (taoZ x))
      atTop (𝓝 (2 / α)) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [hregime.eventually_two_le_X,
    tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hX hzOne
  have hBPos : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have htwoPos : (0 : ℝ) < 2 := by norm_num
  have hlogXPos : 0 < Real.log (X x : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hlogZNe : Real.log (taoZ x) ≠ 0 := (Real.log_pos hzOne).ne'
  rw [Real.log_mul (mul_ne_zero hBPos.ne' (pow_ne_zero _ htwoPos.ne'))
      (pow_ne_zero _ hlogXPos.ne'),
    Real.log_mul hBPos.ne' (pow_ne_zero _ htwoPos.ne'),
    Real.log_pow, Real.log_pow]
  push_cast
  field_simp [hlogZNe]

theorem IsTaoCriticalSmoothRegime.eventually_three_le_X
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) :
    ∀ᶠ x in atTop, 3 ≤ X x := by
  filter_upwards [hregime.tendsto_log_X_atTop.eventually
      (eventually_ge_atTop (Real.log 3))] with x hx
  have hlogXPos : 0 < Real.log (X x : ℝ) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 3)).trans_le hx
  have hXPos : (0 : ℝ) < X x :=
    lt_trans zero_lt_one ((Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogXPos)
  have hreal : (3 : ℝ) ≤ X x :=
    (Real.strictMonoOn_log.le_iff_le (by norm_num) hXPos).mp hx
  exact_mod_cast hreal

/-- Power-form consequence of the exact denominator limit. -/
theorem IsTaoCriticalSmoothRegime.eventually_endpointHildebrandDenominator_le_rpow
    {X y : ℕ → ℕ} {α ε : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hε : 0 < ε) {B : ℕ} (hB : 1 ≤ B) :
    ∀ᶠ x in atTop,
      (B : ℝ) * 2 ^ smoothLowerDepth (X x) (y x) *
          Real.log (X x) ^ (smoothLowerDepth (X x) (y x) + 1) ≤
        (taoZ x) ^ (2 / α + ε) := by
  have hratio :=
    (hregime.tendsto_log_endpointHildebrandDenominator hα hB).eventually
      (Iio_mem_nhds (show 2 / α < 2 / α + ε by linarith))
  filter_upwards [hratio,
    tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hx hzOne
  have hlogBound :
      Real.log ((B : ℝ) * 2 ^ smoothLowerDepth (X x) (y x) *
        Real.log (X x) ^ (smoothLowerDepth (X x) (y x) + 1)) ≤
        (2 / α + ε) * Real.log (taoZ x) :=
    ((div_lt_iff₀ (Real.log_pos hzOne)).mp hx).le
  exact Real.le_rpow_of_log_le (taoZ_pos x) hlogBound

/-- Fully quantified lower consequence of the endpoint-Hildebrand route.
The exponent `2/α` is rigorous but not sharp; Proposition 2.1(i) requires
`1/α`, so this theorem is an explicit diagnostic boundary rather than the
final critical lower bound. -/
theorem IsTaoCriticalSmoothRegime.eventually_self_div_taoZ_rpow_two_div_le_psiNat
    {X y : ℕ → ℕ} {α ε : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      (X x : ℝ) / (taoZ x) ^ (2 / α + ε) ≤
        (psiNat (X x) (y x) : ℝ) := by
  obtain ⟨B, hBFour, htheta⟩ := exists_chebyshevTheta_half_threshold_four
  have hden := hregime.eventually_endpointHildebrandDenominator_le_rpow
    hα hε (show 1 ≤ B by omega)
  filter_upwards [hregime.eventually_three_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_y_atTop hα).eventually (eventually_ge_atTop B),
    hden] with x hX hy hBy hden'
  let D : ℝ := (B : ℝ) * 2 ^ smoothLowerDepth (X x) (y x) *
    Real.log (X x) ^ (smoothLowerDepth (X x) (y x) + 1)
  have hlogXPos : 0 < Real.log (X x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X x by omega))
  have hDPos : 0 < D := by
    dsimp only [D]
    positivity
  have hzPowPos : 0 < (taoZ x) ^ (2 / α + ε) :=
    Real.rpow_pos_of_pos (taoZ_pos x) _
  have hcompare : (X x : ℝ) / (taoZ x) ^ (2 / α + ε) ≤
      (X x : ℝ) / D := by
    rw [div_le_div_iff₀ hzPowPos hDPos]
    exact mul_le_mul_of_nonneg_left (by simpa only [D] using hden')
      (Nat.cast_nonneg _)
  exact hcompare.trans (by
    simpa only [D] using
      self_div_endpointHildebrandDenominator_le_psiNat
        hBFour hX hy htheta hBy)

/-! ## Sharp-saddle consumer -/

/-- A source-facing lower saddle packet.  The main loss is `u log u`; `E`
records any secondary loss that is negligible on the `log z` scale. -/
def HasCriticalSmoothLowerSaddle
    (X y : ℕ → ℕ) (E : ℕ → ℝ) : Prop :=
  ∀ᶠ x in atTop,
    (X x : ℝ) * Real.exp
        (-(smoothRankinRatio (X x) (y x) *
            Real.log (smoothRankinRatio (X x) (y x)) + E x)) ≤
      (psiNat (X x) (y x) : ℝ)

/-- Any lower saddle packet with secondary loss `o(log z)` gives the sharp
critical lower half of Proposition 2.1(i). -/
theorem IsTaoCriticalSmoothRegime.eventually_self_div_taoZ_rpow_le_psiNat_of_saddle
    {X y : ℕ → ℕ} {α ε : ℝ} {E : ℕ → ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hε : 0 < ε) (hE : Tendsto (fun x => E x / Real.log (taoZ x))
      atTop (𝓝 0)) (hsaddle : HasCriticalSmoothLowerSaddle X y E) :
    ∀ᶠ x in atTop,
      (X x : ℝ) / (taoZ x) ^ (1 / α + ε) ≤
        (psiNat (X x) (y x) : ℝ) := by
  have hlossRaw :=
    (hregime.tendsto_rankinRatio_mul_log_div_log_taoZ hα).add hE
  have hloss : Tendsto (fun x =>
      (smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) + E x) /
        Real.log (taoZ x)) atTop (𝓝 (1 / α)) := by
    simpa [add_div] using hlossRaw
  have hlossBound := hloss.eventually
    (Iio_mem_nhds (show 1 / α < 1 / α + ε by linarith))
  filter_upwards [hsaddle, hlossBound,
    tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hsaddle' hloss' hzOne
  have hlossLe :
      smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) + E x ≤
        (1 / α + ε) * Real.log (taoZ x) :=
    ((div_lt_iff₀ (Real.log_pos hzOne)).mp hloss').le
  calc
    (X x : ℝ) / (taoZ x) ^ (1 / α + ε) =
        (X x : ℝ) * Real.exp
          (-(1 / α + ε) * Real.log (taoZ x)) := by
      rw [Real.rpow_def_of_pos (taoZ_pos x)]
      change (X x : ℝ) *
          (Real.exp (Real.log (taoZ x) * (1 / α + ε)))⁻¹ = _
      rw [← Real.exp_neg]
      congr 2
      ring
    _ ≤ (X x : ℝ) * Real.exp
          (-(smoothRankinRatio (X x) (y x) *
              Real.log (smoothRankinRatio (X x) (y x)) + E x)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr (by linarith)
      · exact Nat.cast_nonneg _
    _ ≤ (psiNat (X x) (y x) : ℝ) := hsaddle'

/-- A concrete Canfield--Erdős--Pomerance-sized secondary loss.  Its
`u log log u` scale is negligible beside the main `u log u` loss throughout
Tao's critical regime. -/
def criticalSmoothLowerCEPError
    (C : ℝ) (X y : ℕ → ℕ) (x : ℕ) : ℝ :=
  C * smoothRankinRatio (X x) (y x) *
    Real.log (Real.log (smoothRankinRatio (X x) (y x)))

/-- The standard `O(u log log u)` secondary loss is `o(log z)` in Tao's
critical regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_criticalSmoothLowerCEPError_div_log_taoZ
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (C : ℝ) :
    Tendsto (fun x => criticalSmoothLowerCEPError C X y x /
      Real.log (taoZ x)) atTop (𝓝 0) := by
  have hloglogDiv : Tendsto (fun x =>
      Real.log (Real.log (smoothRankinRatio (X x) (y x))) /
        Real.log (smoothRankinRatio (X x) (y x))) atTop (𝓝 0) := by
    have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (Real.tendsto_log_atTop.comp (hregime.tendsto_rankinRatio_atTop hα))
    simpa [Function.id_def] using h
  have hproduct :=
    ((hregime.tendsto_rankinRatio_mul_log_div_log_taoZ hα).mul
      hloglogDiv).const_mul C
  have hproductZero : Tendsto (fun x => C *
      ((smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) /
            Real.log (taoZ x)) *
        (Real.log (Real.log (smoothRankinRatio (X x) (y x))) /
          Real.log (smoothRankinRatio (X x) (y x)))))
      atTop (𝓝 0) := by
    simpa using hproduct
  apply hproductZero.congr'
  filter_upwards [
    (hregime.tendsto_rankinRatio_atTop hα).eventually
      (eventually_gt_atTop (1 : ℝ)),
    tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x huOne hzOne
  have hloguNe : Real.log (smoothRankinRatio (X x) (y x)) ≠ 0 :=
    (Real.log_pos huOne).ne'
  have hlogzNe : Real.log (taoZ x) ≠ 0 := (Real.log_pos hzOne).ne'
  dsimp only [criticalSmoothLowerCEPError]
  field_simp [hloguNe, hlogzNe]

/-- It remains enough to construct the finite lower saddle packet with a
fixed `C * u log log u` error. -/
theorem IsTaoCriticalSmoothRegime.eventually_self_div_taoZ_rpow_le_psiNat_of_cep
    {X y : ℕ → ℕ} {α ε C : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hε : 0 < ε)
    (hsaddle : HasCriticalSmoothLowerSaddle X y
      (criticalSmoothLowerCEPError C X y)) :
    ∀ᶠ x in atTop,
      (X x : ℝ) / (taoZ x) ^ (1 / α + ε) ≤
        (psiNat (X x) (y x) : ℝ) :=
  hregime.eventually_self_div_taoZ_rpow_le_psiNat_of_saddle hα hε
    (hregime.tendsto_criticalSmoothLowerCEPError_div_log_taoZ hα C) hsaddle

/-! ## Uniform finite CEP interface -/

/-- In the critical regime, `log u` is negligible compared with `log y`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_rankinRatio_div_log_y_zero
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    Tendsto (fun x => Real.log (smoothRankinRatio (X x) (y x)) /
      Real.log (y x)) atTop (𝓝 0) := by
  have hquotient :=
    (hregime.tendsto_log_rankinRatio_div_log_taoZ_zero hα).div
      hregime.2 hα.ne'
  have hquotientZero : Tendsto
      ((fun x => Real.log (smoothRankinRatio (X x) (y x)) /
          Real.log (taoZ x)) /
        (fun x => Real.log (y x) / Real.log (taoZ x)))
      atTop (𝓝 0) := by
    simpa using hquotient
  apply hquotientZero.congr'
  filter_upwards [
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    hregime.tendsto_log_y_atTop hα |>.eventually
      (eventually_gt_atTop (0 : ℝ))] with x hzOne hyLogPos
  change
    (Real.log (smoothRankinRatio (X x) (y x)) / Real.log (taoZ x)) /
        (Real.log (y x) / Real.log (taoZ x)) =
      Real.log (smoothRankinRatio (X x) (y x)) / Real.log (y x)
  field_simp [(Real.log_pos hzOne).ne', hyLogPos.ne']

/-- Tao's critical regime eventually lies in the fixed CEP uniformity range
`u ≤ y^(1/2)`. -/
theorem IsTaoCriticalSmoothRegime.eventually_rankinRatio_le_y_rpow_half
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    ∀ᶠ x in atTop,
      smoothRankinRatio (X x) (y x) ≤ (y x : ℝ) ^ (1 / 2 : ℝ) := by
  have hratio :=
    (hregime.tendsto_log_rankinRatio_div_log_y_zero hα).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hratio, hregime.eventually_two_le_y hα] with x hx hy
  have hyPos : (0 : ℝ) < y x := by exact_mod_cast (show 0 < y x by omega)
  have hlogyPos : 0 < Real.log (y x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y x by omega))
  have hlogBound :
      Real.log (smoothRankinRatio (X x) (y x)) ≤
        (1 / 2 : ℝ) * Real.log (y x) :=
    ((div_lt_iff₀ hlogyPos).mp hx).le
  exact Real.le_rpow_of_log_le hyPos hlogBound

/-- The remaining finite theorem in source-uniform form.  A proof may choose
fixed constants `C,U`; beyond `u ≥ U` and inside the standard CEP range
`u ≤ y^(1/2)`, it must establish the explicit lower saddle inequality. -/
def HasUniformCriticalCEPLowerSaddle (C U : ℝ) : Prop :=
  ∀ X y : ℕ, 2 ≤ X → 2 ≤ y →
    U ≤ smoothRankinRatio X y →
    smoothRankinRatio X y ≤ (y : ℝ) ^ (1 / 2 : ℝ) →
    (X : ℝ) * Real.exp
        (-(smoothRankinRatio X y * Real.log (smoothRankinRatio X y) +
          C * smoothRankinRatio X y *
            Real.log (Real.log (smoothRankinRatio X y)))) ≤
      (psiNat X y : ℝ)

/-- A uniform finite CEP estimate supplies the critical lower saddle packet. -/
theorem IsTaoCriticalSmoothRegime.hasCriticalSmoothLowerSaddle_of_uniformCEP
    {X y : ℕ → ℕ} {α C U : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hfinite : HasUniformCriticalCEPLowerSaddle C U) :
    HasCriticalSmoothLowerSaddle X y
      (criticalSmoothLowerCEPError C X y) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_rankinRatio_atTop hα).eventually
      (eventually_ge_atTop U),
    hregime.eventually_rankinRatio_le_y_rpow_half hα] with
      x hX hy hu hrange
  simpa [criticalSmoothLowerCEPError] using
    hfinite (X x) (y x) hX hy hu hrange

/-- Source-range finite CEP immediately yields Tao's sharp critical lower
estimate. -/
theorem IsTaoCriticalSmoothRegime.eventually_self_div_taoZ_rpow_le_psiNat_of_uniformCEP
    {X y : ℕ → ℕ} {α ε C U : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hε : 0 < ε) (hfinite : HasUniformCriticalCEPLowerSaddle C U) :
    ∀ᶠ x in atTop,
      (X x : ℝ) / (taoZ x) ^ (1 / α + ε) ≤
        (psiNat (X x) (y x) : ℝ) :=
  hregime.eventually_self_div_taoZ_rpow_le_psiNat_of_cep hα hε
    (hregime.hasCriticalSmoothLowerSaddle_of_uniformCEP hα hfinite)

end

end Tao2026
