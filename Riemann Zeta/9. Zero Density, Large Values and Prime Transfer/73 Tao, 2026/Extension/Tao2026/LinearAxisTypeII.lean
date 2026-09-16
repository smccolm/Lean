import Tao2026.CoordinateAxisFourierSourceBlock
import Tao2026.Vinogradov

/-!
# Pure-linear Type II estimates

This module develops the missing coordinate-axis branch in which the
quadratic reciprocal coefficient vanishes but the linear coefficient does
not.  In this chamber the derivative critical sets are empty, so the source
Vinogradov estimate applies on the whole dyadic interval without a critical
deletion or component-counting loss.
-/

open Complex Finset Filter Topology
open scoped BigOperators ContDiff

namespace Tao2026

noncomputable section

/-- A nonzero pure-linear reciprocal phase has no derivative critical
points. -/
theorem reciprocalDerivativeCriticalSet_zero_quadratic_eq_empty
    {N : ℝ} (hN : N ≠ 0) (j r : ℕ) (X Y q : ℝ) :
    reciprocalDerivativeCriticalSet N 0 j r X Y q = ∅ := by
  ext t
  simp [reciprocalDerivativeCriticalSet, reciprocalCriticalSet,
    reciprocalCriticalExpression, reciprocalPhaseHigherCoefficient, hN]

/-- Consequently, every finite union of derivative critical sets is empty
in the pure-linear chamber. -/
theorem reciprocalDerivativeCriticalUnion_zero_quadratic_eq_empty
    {N : ℝ} (hN : N ≠ 0) (j : ℕ) (orders : Finset ℕ) (X Y q : ℝ) :
    reciprocalDerivativeCriticalUnion N 0 j orders X Y q = ∅ := by
  ext t
  simp [reciprocalDerivativeCriticalUnion,
    reciprocalDerivativeCriticalSet_zero_quadratic_eq_empty hN]

/-- The fixed-constant source Vinogradov estimate for a pure-linear
reciprocal phase.  Unlike the mixed-phase consumer, this has no deleted-set
or regular-component loss because all critical sets are empty. -/
theorem norm_reciprocalPhaseSum_zero_quadratic_le_sourceVinogradovAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (N P A X : ℝ) (a b : ℕ)
    (hX : 2 ≤ X) (hN : N ≠ 0)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff X
      (reciprocalPhaseScale N 0 2 X) + 2 : ℕ) : ℝ)) ≤ Real.log P)
    (hFhigh : X ^ 4 ≤ reciprocalPhaseScale N 0 2 X)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale N 0 2 X)) ^ 2 /
        (Real.log X) ^ 3 < (1 / 1000 : ℝ))
    (hXa : X ≤ (a : ℝ)) (hbX : (b : ℝ) ≤ 2 * X) :
    ‖reciprocalPhaseSum N 0 2 a b‖ ≤
      C * (Real.log P) ^ (4 * A) * X * Real.exp
        (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
          (Real.log (reciprocalPhaseScale N 0 2 X)) ^ 2) := by
  obtain ⟨hC, hVinogradov⟩ := hVinogradov
  have hα : 1 ≤ (Real.log P) ^ (4 * A) := by
    obtain ⟨_, _, hα, _, _⟩ :=
      vinogradov_log_power_parameters hlog hA hcutoff hten
    exact hα
  have hI : Set.Icc (a : ℝ) (b : ℝ) ⊆ Set.Icc X (2 * X) := by
    intro t ht
    exact ⟨hXa.trans ht.1, ht.2.trans hbX⟩
  apply hVinogradov X (reciprocalPhaseScale N 0 2 X)
    ((Real.log P) ^ (4 * A)) a b (reciprocalPhase N 0 2)
    hX hFhigh hα hsmall hI
  · intro t ht
    rw [contDiffAt_infty]
    intro r
    apply contDiffAt_reciprocalPhase_of_pos N 0 2 r
    exact (by linarith [hX, hXa, ht.1] : 0 < t)
  · apply reciprocalPhase_vinogradov_derivative_bounds_on_regular_interval_sourceCutoff
      N 0 P A (X := X) (Y := 2 * X) (c := (a : ℝ)) (d := (b : ℝ))
      (by linarith) hlog hA hten hcutoff (by norm_num) hI le_rfl
    intro t ht
    rw [reciprocalDerivativeCriticalUnion_zero_quadratic_eq_empty hN]
    simp

/-- Fixed-constant high-scale Vinogradov estimate for an exact pure-linear
product-restricted Type II correlation. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradovAt_zero_quadratic
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (a b K₀ K₁ q k : ℕ) (N P A K : ℝ) {n n' : ℕ}
    (hKouter : K = ((K₀ + k * q : ℕ) : ℝ))
    (hK : 2 ≤ K) (hq : 0 < q) (hqK : (q : ℝ) ≤ K)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n') (hN : N ≠ 0)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff K
      (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K) + 2 : ℕ) : ℝ)) ≤
          Real.log P)
    (hFhigh : K ^ 4 ≤ reciprocalPhaseScale
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter 0 2 n n') 2 K)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K)) ^ 2 /
          (Real.log K) ^ 3 < (1 / 1000 : ℝ)) :
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
      (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤
      C * (Real.log P) ^ (4 * A) * K * Real.exp
        (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log K) ^ 3 /
          (Real.log (reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter 0 2 n n') 2 K)) ^ 2) := by
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter 0 2 n n'
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  have hN' : N' ≠ 0 := by
    unfold N' typeIICorrelationLinearParameter
    exact typeIICorrelationLinearParameter_ne_zero hN
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hM' : M' = 0 := by simp [M', typeIICorrelationHigherParameter]
  have hloNat : K₀ + k * q ≤ lo := le_max_left _ _
  have hlo : K ≤ (lo : ℝ) := by
    rw [hKouter]
    exact_mod_cast hloNat
  have hhiNat : hi ≤ K₀ + (k + 1) * q :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hhi : (hi : ℝ) ≤ 2 * K := by
    calc
      (hi : ℝ) ≤ ((K₀ + (k + 1) * q : ℕ) : ℝ) := by exact_mod_cast hhiNat
      _ = K + (q : ℝ) := by rw [hKouter]; push_cast; ring
      _ ≤ 2 * K := by linarith
  have hglobal := norm_reciprocalPhaseSum_zero_quadratic_le_sourceVinogradovAt
    C hVinogradov N' P A K lo hi hK hN' hlog hA hten
      (by simpa only [N', M', hM'] using hcutoff)
      (by simpa only [N', M', hM'] using hFhigh)
      (by simpa only [N', M', hM'] using hsmall) hlo hhi
  rw [typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
    a b K₀ K₁ q k N 0 2 hq hn hn']
  simpa only [N', M', lo, hi, typeIICorrelationHigherParameter,
    zero_mul, zero_div] using hglobal

/-- Uniform high-pair logarithmic saving for pure-linear correlations. -/
theorem eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logSaving_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A C₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b K₀ K₁ q k : ℕ) (N K : ℝ) (n n' : ℕ),
        K = ((K₀ + k * q : ℕ) : ℝ) →
        2 ≤ K → 0 < q → (q : ℝ) ≤ K →
        0 < n → 0 < n' → n ≠ n' → N ≠ 0 →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter 0 2 n n') 2 K ≤
          C₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log K →
        K ^ 4 ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K →
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤
            3 * K * (Real.log P) ^ (-T) := by
  obtain ⟨C₁, hVinogradovAt⟩ := hVinogradov
  have hC₁ : 0 < C₁ := hVinogradovAt.1
  have hparameters :=
    eventually_sourceVinogradov_quadraticParameterConditions_of_parameterBound
      hA hC₀ hc hε ha
  have henvelope := eventually_sourceVinogradov_logEnvelope_le
    hC₀ hC₁ hc hε ha hAT
  filter_upwards [hparameters, henvelope] with P hparametersP henvelopeP
  intro a b K₀ K₁ q k N K n n' hKouter hK hq hqK hn hn' hne hN
    hFupper hKlower hFhigh
  let F := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter 0 2 n n') 2 K
  obtain ⟨hlog, hten, hcutoff, hsmall⟩ :=
    hparametersP K F hK (by simpa only [F] using hFhigh)
      (by simpa only [F] using hFupper) hKlower
  have hraw :=
    norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradovAt_zero_quadratic
      C₁ hVinogradovAt a b K₀ K₁ q k N P A K hKouter hK hq hqK
        hn hn' hne hN hlog hA hten
        (by simpa only [F] using hcutoff)
        (by simpa only [F] using hFhigh)
        (by simpa only [F] using hsmall)
  have hmainNonneg : 0 ≤ C₁ * (Real.log P) ^ (4 * A) * K * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log K) ^ 3 / (Real.log F) ^ 2) := by
    positivity
  have hfactor : 1 ≤ 2 * Real.log P + 1 := by linarith
  have hdelete : 0 ≤ Real.log P *
      (16 * K * (Real.log P) ^ (-3 * A) + Real.log P + 1) := by
    positivity
  calc
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤
      C₁ * (Real.log P) ^ (4 * A) * K * Real.exp
        (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log K) ^ 3 / (Real.log F) ^ 2) := by
          simpa only [F] using hraw
    _ ≤ (2 * Real.log P + 1) *
        (C₁ * (Real.log P) ^ (4 * A) * K * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log K) ^ 3 / (Real.log F) ^ 2)) +
        Real.log P *
          (16 * K * (Real.log P) ^ (-3 * A) + Real.log P + 1) := by
            have hmul := mul_le_mul_of_nonneg_right hfactor hmainNonneg
            linarith
    _ ≤ 3 * K * (Real.log P) ^ (-T) :=
      henvelopeP K F hK (by simpa only [F] using hFhigh)
        (by simpa only [F] using hFupper) hKlower

/-- Distance-kernel domination for the low-scale pure-linear Type II
correlation.  The linear source scale controls the transformed scale without
the factor two needed when the source scale has two competing terms. -/
theorem reciprocalPhaseFourStepTwoTermWidth_typeIICorrelation_zero_quadratic_le
    (N K B E : ℝ) {n n' : ℕ}
    (hN : N ≠ 0) (hK : 0 < K) (hB : 0 < B)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hwidthOne :
      reciprocalPhaseFourStepTwoTermWidth
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K ≤ 1)
    (hupper :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K / K ^ 5 ≤ E) :
    reciprocalPhaseFourStepTwoTermWidth
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K ≤
      E ^ (1 / 1024 : ℝ) +
        2 * typeIIDecayKernel B (reciprocalPhaseScale N 0 2 (K * B))
          (1 / 1024 : ℝ) (Nat.dist n' n) := by
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter 0 2 n n'
  let F := reciprocalPhaseScale N 0 2 (K * B)
  let d := Nat.dist n' n
  let x := (d : ℝ) * F / B
  let δ : ℝ := 1 / 1024
  have hδ0 : 0 ≤ δ := by unfold δ; norm_num
  have hδ1 : δ ≤ 1 := by unfold δ; norm_num
  have hN' : N' ≠ 0 := by
    unfold N' typeIICorrelationLinearParameter
    exact typeIICorrelationLinearParameter_ne_zero hN
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hM' : M' = 0 := by
    simp [M', typeIICorrelationHigherParameter]
  have hscale : 0 < reciprocalPhaseScale N' M' 2 K := by
    rw [hM']
    unfold reciprocalPhaseScale
    positivity
  have hF : 0 < F := by
    unfold F reciprocalPhaseScale
    positivity
  have hx0 : 0 ≤ x := by unfold x; positivity
  have hlower : x ≤ reciprocalPhaseScale N' M' 2 K := by
    have hraw := typeIICorrelationScale_lower_of_linear
      N 0 K B 2 n n' hK hB hn hn' hnB hn'B
    calc
      x = (Nat.dist n' n : ℝ) / B * (|N| / (K * B)) := by
        simp only [x, F, d, reciprocalPhaseScale, abs_zero, zero_div,
          add_zero]
        ring
      _ ≤ reciprocalPhaseScale N' M' 2 K := by
        simpa only [N', M'] using hraw
  by_cases hx : 1 ≤ x
  · have hbaseLower : (1 + (d : ℝ) * F / B) / 2 ≤
        reciprocalPhaseScale N' M' 2 K := by
      have hxeq : (d : ℝ) * F / B = x := by rfl
      rw [hxeq]
      exact (by linarith : (1 + x) / 2 ≤ x).trans hlower
    have hgeneric :=
      reciprocalPhaseFourStepTwoTermWidth_le_typeIIDecayKernel_add_error
        N' M' hK hscale hB hF.le (by norm_num : (0 : ℝ) < 2)
          (by simpa only [N', M'] using hupper) hbaseLower
    have htwo : (2 : ℝ) ^ δ ≤ 2 :=
      Real.rpow_le_self_of_one_le (by norm_num) hδ1
    have hkernelNonneg : 0 ≤ typeIIDecayKernel B F δ d :=
      typeIIDecayKernel_nonneg δ d hB hF.le
    calc
      reciprocalPhaseFourStepTwoTermWidth N' M' 2 K ≤
          E ^ δ + 2 ^ δ * typeIIDecayKernel B F δ d := by
        simpa only [δ] using hgeneric
      _ ≤ E ^ δ + 2 * typeIIDecayKernel B F δ d := by gcongr
      _ = E ^ (1 / 1024 : ℝ) +
          2 * typeIIDecayKernel B F (1 / 1024 : ℝ) d := by rfl

  · have hxlt : x < 1 := lt_of_not_ge hx
    have hbasePos : 0 < 1 + (d : ℝ) * F / B := by positivity
    have hbaseTwo : 1 + (d : ℝ) * F / B ≤ 2 := by
      have hxeq : (d : ℝ) * F / B = x := by rfl
      rw [hxeq]
      linarith
    have htwoKernel : (2 : ℝ) ^ (-δ) ≤
        typeIIDecayKernel B F δ d := by
      unfold typeIIDecayKernel
      exact Real.rpow_le_rpow_of_nonpos hbasePos hbaseTwo
        (neg_nonpos.mpr hδ0)
    have hhalfPow : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-δ) := by
      calc
        (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ (-δ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hkernelHalf : (1 / 2 : ℝ) ≤
        typeIIDecayKernel B F δ d := hhalfPow.trans htwoKernel
    have hwidthOne' : reciprocalPhaseFourStepTwoTermWidth N' M' 2 K ≤ 1 := by
      simpa only [N', M'] using hwidthOne
    have hEnonneg : 0 ≤ E := by
      have hu : 0 ≤ reciprocalPhaseScale N' M' 2 K / K ^ 5 := by positivity
      exact hu.trans (by simpa only [N', M'] using hupper)
    calc
      reciprocalPhaseFourStepTwoTermWidth N' M' 2 K ≤ 1 := hwidthOne'
      _ ≤ E ^ δ + 2 * typeIIDecayKernel B F δ d := by
        have hEpow : 0 ≤ E ^ δ := Real.rpow_nonneg hEnonneg δ
        nlinarith
      _ = E ^ (1 / 1024 : ℝ) +
          2 * typeIIDecayKernel B F (1 / 1024 : ℝ) d := by rfl

/-- Off the diagonal, the transformed pure-linear scale has the reciprocal
bound dictated by the source scale and outer dyadic width. -/
theorem one_div_typeIICorrelationScale_le_B_div_sourceScale_zero_quadratic
    (N K B : ℝ) {n n' : ℕ}
    (hN : N ≠ 0) (hK : 0 < K) (hB : 0 < B)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B) :
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K ≤
      B / reciprocalPhaseScale N 0 2 (K * B) := by
  let F := reciprocalPhaseScale N 0 2 (K * B)
  let F' := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter 0 2 n n') 2 K
  have hF : 0 < F := by unfold F reciprocalPhaseScale; positivity
  have hdistNat : 1 ≤ Nat.dist n' n :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hne (Nat.eq_of_dist_eq_zero h).symm)
  have hdist : (1 : ℝ) ≤ (Nat.dist n' n : ℝ) := by exact_mod_cast hdistNat
  have hdiv : 1 / B ≤ (Nat.dist n' n : ℝ) / B :=
    div_le_div_of_nonneg_right hdist hB.le
  have hbaseRaw := mul_le_mul_of_nonneg_right hdiv hF.le
  have hbase : F / B ≤ (Nat.dist n' n : ℝ) / B * F := by
    calc
      F / B = (1 / B) * F := by ring
      _ ≤ (Nat.dist n' n : ℝ) / B * F := hbaseRaw
  have hlower : (Nat.dist n' n : ℝ) / B * F ≤ F' := by
    have hraw := typeIICorrelationScale_lower_of_linear
      N 0 K B 2 n n' hK hB hn hn' hnB hn'B
    simpa only [F, F', reciprocalPhaseScale, abs_zero, zero_div,
      add_zero] using hraw
  have hinv : 1 / F' ≤ 1 / (F / B) :=
    one_div_le_one_div_of_le (div_pos hF hB) (hbase.trans hlower)
  calc
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K = 1 / F' := by rfl
    _ ≤ 1 / (F / B) := hinv
    _ = B / reciprocalPhaseScale N 0 2 (K * B) := by
      unfold F
      field_simp

/-- A source-scaled separation of three forces the transformed pure-linear
scale to be at least three. -/
theorem one_div_typeIICorrelationScale_le_one_third_of_three_le_scaledDistance_zero_quadratic
    (N K B : ℝ) {n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B)
    (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N 0 2 (K * B) / B) :
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K ≤ 1 / 3 := by
  have hlower := typeIICorrelationScale_lower_of_linear
    N 0 K B 2 n n' hK hB hn hn' hnB hn'B
  have hthree : 3 ≤ reciprocalPhaseScale
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter 0 2 n n') 2 K := by
    apply hfar.trans
    calc
      (Nat.dist n' n : ℝ) * reciprocalPhaseScale N 0 2 (K * B) / B =
          (Nat.dist n' n : ℝ) / B * (|N| / (K * B)) := by
            simp only [reciprocalPhaseScale, abs_zero, zero_div, add_zero]
            ring
      _ ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K := hlower
  exact one_div_le_one_div_of_le (by norm_num) hthree

/-- Far pure-linear pairs satisfy the complete four-step effective-error
budget. -/
theorem reciprocalPhaseFourStepEffectiveErrorScale_typeIICorrelation_le_one_of_far_zero_quadratic
    (N K B E : ℝ) {L n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B)
    (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hupper : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K / K ^ 5 ≤ E)
    (hscaleBudget : 240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) * E ≤ 1 / 4)
    (hLength : 1 ≤ L)
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N 0 2 (K * B) / B) :
    reciprocalPhaseFourStepEffectiveErrorScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K L ≤ 1 := by
  have hinv :=
    one_div_typeIICorrelationScale_le_one_third_of_three_le_scaledDistance_zero_quadratic
      N K B hK hB hn hn' hnB hn'B hfar
  have hraw := reciprocalPhaseFourStepEffectiveErrorScale_le_of_scale_bounds
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter 0 2 n n') K E (1 / 3) 2 L
    hupper hinv hLength
  calc
    reciprocalPhaseFourStepEffectiveErrorScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K L ≤
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) * E + 1 / 16 + 1 / 3 := hraw
    _ ≤ 1 := by linarith

/-- Whole-interval four-step Weyl estimate for a pure-linear reciprocal
phase.  There is no component decomposition because its derivative critical
union is empty. -/
theorem norm_reciprocalPhaseSum_zero_quadratic_le_fourStepWeyl_regular
    (N : ℝ) (orders : Finset ℕ) (a b H : ℕ) {X Y q : ℝ}
    (hN : N ≠ 0) (hX : 0 < X) (hq : 0 < q) (hqOne : q ≤ 1)
    (hLength : 1 ≤ b - a)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) * reciprocalPhaseFourStepUpperScale N 0 2 X ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          reciprocalPhaseFourStepLowerScale N 0 2 X q)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ 2 * X)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N 0 2 a b‖ ≤
      (H : ℝ) + weylLagFourSharpRootMajorant H (b - a)
        (reciprocalPhaseFourStepLowerScale N 0 2 X q) := by
  have hF : 0 < reciprocalPhaseScale N 0 2 X := by
    unfold reciprocalPhaseScale
    positivity
  have hscale : 0 < reciprocalPhaseFourStepLowerScale N 0 2 X q := by
    unfold reciprocalPhaseFourStepLowerScale
    positivity
  by_cases hHL : H ≤ b - a
  · have hraw :=
      norm_reciprocalPhaseSum_le_fourStepWeylLagSharpRootMajorant_regularScale
        N 0 orders a b H hX hF hq hqOne (by norm_num) hLength hHL
          haIcc hevalY hevalTop (by
            intro y hy
            rw [reciprocalDerivativeCriticalUnion_zero_quadratic_eq_empty hN]
            simp) hrFive hrSix (by
              simpa [reciprocalPhaseFourStepUpperScale,
                reciprocalPhaseFourStepLowerScale] using hupperSmall)
    exact hraw.trans (le_add_of_nonneg_left (by positivity))
  · have hshort := norm_reciprocalPhaseSum_le_card N 0 2 a b
    rw [Nat.card_Ico] at hshort
    have hcard : ((b - a : ℕ) : ℝ) ≤ H := by
      exact_mod_cast (Nat.lt_of_not_ge hHL).le
    exact hshort.trans (hcard.trans (le_add_of_nonneg_right
      (weylLagFourSharpRootMajorant_nonneg H (b - a) hscale)))

/-- Source-normalized pure-linear Weyl estimate.  The constant is smaller
than the mixed-phase component envelope because no critical interval is
deleted. -/
theorem norm_reciprocalPhaseSum_zero_quadratic_le_fourStepWeyl_source
    (N : ℝ) (orders : Finset ℕ) (a b : ℕ) {X Y : ℝ}
    (hN : N ≠ 0) (hX : 0 < X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N 0 2 X (b - a) ≤ 1)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N 0 2 X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N 0 2 X (b - a) : ℕ) ≤
          2 * X)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let S := ((240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) *
      (reciprocalPhaseScale N 0 2 X / X ^ 5 +
        1 / ((((b - a) + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N 0 2 X)) ^ (1 / 128 : ℝ)
    ‖reciprocalPhaseSum N 0 2 a b‖ ≤
      173 * (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log ((b - a : ℕ) : ℝ)) * X * S := by
  dsimp only
  let L := b - a
  let H := reciprocalPhaseFourStepOptimizedRange N 0 2 X L
  let q := reciprocalPhaseFourStepCriticalWidth N 0 2 X L
  let K : ℝ := ((((5 + 2) ^ 5 : ℕ) : ℝ))
  let R := 1 + Real.log L
  let S := ((240 * K) *
    (reciprocalPhaseScale N 0 2 X / X ^ 5 +
      1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
      1 / reciprocalPhaseScale N 0 2 X)) ^ (1 / 128 : ℝ)
  have hF : 0 < reciprocalPhaseScale N 0 2 X := by
    unfold reciprocalPhaseScale
    positivity
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N 0 hX hF
  have hqOne : q ≤ 1 :=
    reciprocalPhaseFourStepCriticalWidth_le_one N 0 hX hF herrorSmall
  have hR : 1 ≤ R := by
    have hLreal : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLength
    unfold R
    linarith [Real.log_nonneg hLreal]
  have hK : 1 ≤ K := by unfold K; norm_num
  have hLX : (L : ℝ) ≤ X := by
    have htop := hevalTop
    change (a : ℝ) + (L : ℝ) + ((4 * H : ℕ) : ℝ) ≤ 2 * X at htop
    have hmargin : 0 ≤ ((4 * H : ℕ) : ℝ) := by positivity
    linarith [haIcc.1]
  have hbase := norm_reciprocalPhaseSum_zero_quadratic_le_fourStepWeyl_regular
    N orders a b H hN hX hq hqOne hLength
      (reciprocalPhaseFourStepOptimizedRange_upperSmall N 0 hX hF herrorSmall)
      haIcc (by simpa only [H, L] using hevalY)
      (by simpa only [H, L] using hevalTop) hrFive hrSix
  have hsharpLog := weylLagFourSharpRootMajorant_le_logRootMajorant
    H L (scale := reciprocalPhaseFourStepLowerScale N 0 2 X q)
      (by unfold reciprocalPhaseFourStepLowerScale; positivity)
  have hlogEffective := weylLagFourLogRootMajorant_optimized_le_effective
    N 0 (j := 2) (L := L) (X := X)
      (scale := reciprocalPhaseFourStepLowerScale N 0 2 X q)
      hX hF hLength herrorSmall
      (by unfold reciprocalPhaseFourStepLowerScale; positivity)
  have hH : (H : ℝ) ≤ (L : ℝ) * q := by
    simpa only [H, q] using
      (reciprocalPhaseFourStepOptimizedRange_cast_le N 0 hX hF
        (j := 2) (L := L))
  have hmajor := weylLagFourOptimizedEffectiveRootMajorant_le_fixedPower
    N 0 hX hF hLength hLX herrorSmall
  have hfactor : (L : ℝ) ≤ (K + 1) * R * X := by
    have hmult : 1 ≤ (K + 1) * R := by
      have hKplus : 1 ≤ K + 1 := by linarith
      exact hR.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hKplus
          (zero_le_one.trans hR))
    exact hLX.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmult hX.le)
  have hfactorq : (L : ℝ) * q ≤ (K + 1) * R * X * q :=
    mul_le_mul_of_nonneg_right hfactor hq.le
  have hfixed : ‖reciprocalPhaseSum N 0 2 a b‖ ≤
      173 * (K + 1) * R * X * q := by
    calc
      ‖reciprocalPhaseSum N 0 2 a b‖ ≤
          (H : ℝ) + weylLagFourSharpRootMajorant H L
            (reciprocalPhaseFourStepLowerScale N 0 2 X q) := by
              simpa only [H, L, q] using hbase
      _ ≤ (L : ℝ) * q + weylLagFourLogRootMajorant H L
            (reciprocalPhaseFourStepLowerScale N 0 2 X q) :=
          add_le_add hH hsharpLog
      _ ≤ (L : ℝ) * q +
          weylLagFourOptimizedEffectiveRootMajorant N 0 2 X L
            (reciprocalPhaseFourStepLowerScale N 0 2 X q) := by
              exact add_le_add_right (by simpa only [H, q] using hlogEffective) _
      _ ≤ (L : ℝ) * q + 172 * (K + 1) * R * X * q := by
              gcongr
      _ ≤ 173 * (K + 1) * R * X * q := by nlinarith
  have hqS : q ≤ S := by
    simpa only [q, S, K, L] using
      (reciprocalPhaseFourStepCriticalWidth_le_source N 0 2 L hX hF)
  calc
    ‖reciprocalPhaseSum N 0 2 a b‖ ≤
        173 * (K + 1) * R * X * q := hfixed
    _ ≤ 173 * (K + 1) * R * X * S := by gcongr
    _ = 173 * (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log ((b - a : ℕ) : ℝ)) * X *
          ((240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) *
            (reciprocalPhaseScale N 0 2 X / X ^ 5 +
              1 / ((((b - a) + 1 : ℕ) : ℝ) ^ 4) +
              1 / reciprocalPhaseScale N 0 2 X)) ^ (1 / 128 : ℝ) := by rfl

/-- Source-facing low-frequency two-term Weyl estimate in the pure-linear
chamber. -/
theorem norm_reciprocalPhaseSum_zero_quadratic_le_fourStepWeyl_twoTerm
    (N : ℝ) (orders : Finset ℕ) (a b : ℕ) {X Y : ℝ}
    (hN : N ≠ 0) (hX : 0 < X)
    (hFlow : reciprocalPhaseScale N 0 2 X ≤ X ^ 4)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N 0 2 X (b - a) ≤ 1)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N 0 2 X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N 0 2 X (b - a) : ℕ) ≤
          2 * X)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let p := reciprocalPhaseFourStepTwoTermWidth N 0 2 X
    ‖reciprocalPhaseSum N 0 2 a b‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((b - a : ℕ) : ℝ)) * X * p) := by
  dsimp only
  let L := b - a
  let K : ℝ := ((((5 + 2) ^ 5 : ℕ) : ℝ))
  let R := 1 + Real.log L
  let p := reciprocalPhaseFourStepTwoTermWidth N 0 2 X
  let C : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  let S := ((240 * K) *
    (reciprocalPhaseScale N 0 2 X / X ^ 5 +
      1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
      1 / reciprocalPhaseScale N 0 2 X)) ^ (1 / 128 : ℝ)
  have hF : 0 < reciprocalPhaseScale N 0 2 X := by
    unfold reciprocalPhaseScale
    positivity
  have hp : 0 < p := reciprocalPhaseFourStepTwoTermWidth_pos N 0 hX hF
  have hK : 1 ≤ K := by unfold K; norm_num
  have hR : 1 ≤ R := by
    have hLreal : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLength
    unfold R
    linarith [Real.log_nonneg hLreal]
  have hC : 173 ≤ C := by
    unfold C
    exact_mod_cast (by omega : 173 ≤ 370 * orders.card + 173)
  by_cases hlong : X * p ≤ ((L + 1 : ℕ) : ℝ)
  · have hsource := norm_reciprocalPhaseSum_zero_quadratic_le_fourStepWeyl_source
      N orders a b hN hX herrorSmall hLength haIcc hevalY hevalTop hrFive hrSix
    have hwidth := reciprocalPhaseFourStepSourceWidth_le_twoTermWidth
      N 0 2 L hX hF hFlow herrorSmall hlong
    have hinner : (K + 1) * R * X * S ≤
        480 * K * ((K + 1) * R * X * p) := by
      calc
        (K + 1) * R * X * S ≤
          (K + 1) * R * X * (480 * K * p) :=
            mul_le_mul_of_nonneg_left (by simpa only [S, K, L] using hwidth)
              (by positivity)
        _ = 480 * K * ((K + 1) * R * X * p) := by ring
    have hsource' : ‖reciprocalPhaseSum N 0 2 a b‖ ≤
        173 * ((K + 1) * R * X * S) := by
      simpa only [K, R, L, S, mul_assoc] using hsource
    have hscaled := mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : ℝ) ≤ 173)
    have hcoeff : 173 * (480 * K * ((K + 1) * R * X * p)) ≤
        C * (480 * K * ((K + 1) * R * X * p)) := by gcongr
    exact hsource'.trans (hscaled.trans (by
      simpa only [C, K, R, p, L, mul_assoc] using hcoeff))
  · have hshort : ((L + 1 : ℕ) : ℝ) < X * p := lt_of_not_ge hlong
    have hLXp : (L : ℝ) ≤ X * p := by
      have hsucc : (L : ℝ) < ((L + 1 : ℕ) : ℝ) := by norm_num
      exact (hsucc.trans hshort).le
    have htrivial := norm_reciprocalPhaseSum_le_card N 0 2 a b
    rw [Nat.card_Ico] at htrivial
    have h480K : 1 ≤ 480 * K := by nlinarith [hK]
    have hKplus : 1 ≤ K + 1 := by linarith
    have hCOne : 1 ≤ C := by linarith
    have hfactor : 1 ≤ C * (480 * K * ((K + 1) * R)) :=
      one_le_mul_of_one_le_of_one_le hCOne
        (one_le_mul_of_one_le_of_one_le h480K
          (one_le_mul_of_one_le_of_one_le hKplus hR))
    have htarget : X * p ≤
        C * (480 * K * ((K + 1) * R * X * p)) := by
      have hnonneg : 0 ≤ X * p := mul_nonneg hX.le hp.le
      have := mul_le_mul_of_nonneg_right hfactor hnonneg
      nlinarith
    apply htrivial.trans
    apply hLXp.trans
    simpa only [C, K, R, p, L, mul_assoc] using htarget

/-- The pure-linear low-frequency Weyl estimate on the exact
product-restricted Type II correlation interval. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_twoTerm_zero_quadratic
    (a b K₀ K₁ q k : ℕ) (N : ℝ) (orders : Finset ℕ)
    {n n' : ℕ} {X Y : ℝ}
    (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hN : N ≠ 0) (hX : 0 < X)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hanalytic :
      let N' := typeIICorrelationLinearParameter N n n'
      let M' := typeIICorrelationHigherParameter 0 2 n n'
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      1 ≤ hi - lo →
        reciprocalPhaseScale N' M' 2 X ≤ X ^ 4 ∧
        reciprocalPhaseFourStepEffectiveErrorScale N' M' 2 X (hi - lo) ≤ 1 ∧
        (lo : ℝ) ∈ Set.Icc X Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 X (hi - lo) : ℕ) ≤ Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 X (hi - lo) : ℕ) ≤
          2 * X) :
    let N' := typeIICorrelationLinearParameter N n n'
    let M' := typeIICorrelationHigherParameter 0 2 n n'
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    let p := reciprocalPhaseFourStepTwoTermWidth N' M' 2 X
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * X * p) := by
  dsimp only
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter 0 2 n n'
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  have hN' : N' ≠ 0 := by
    unfold N' typeIICorrelationLinearParameter
    exact typeIICorrelationLinearParameter_ne_zero hN
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hM' : M' = 0 := by simp [M', typeIICorrelationHigherParameter]
  rw [typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
    a b K₀ K₁ q k N 0 2 hq hn hn']
  change ‖reciprocalPhaseSum N' M' 2 lo hi‖ ≤ _
  by_cases hLength : 1 ≤ hi - lo
  · rcases hanalytic hLength with
      ⟨hFlow, herrorSmall, haIcc, hevalY, hevalTop⟩
    have hFlow' : reciprocalPhaseScale N' 0 2 X ≤ X ^ 4 := by
      simpa only [N', M', typeIICorrelationHigherParameter, zero_mul,
        zero_div] using hFlow
    have herrorSmall' :
        reciprocalPhaseFourStepEffectiveErrorScale N' 0 2 X (hi - lo) ≤ 1 := by
      simpa only [N', M', lo, hi, typeIICorrelationHigherParameter,
        zero_mul, zero_div] using herrorSmall
    have hevalY' : (lo : ℝ) + (hi - lo : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N' 0 2 X (hi - lo) : ℕ) ≤ Y := by
      simpa only [N', M', lo, hi, typeIICorrelationHigherParameter,
        zero_mul, zero_div] using hevalY
    have hevalTop' : (lo : ℝ) + (hi - lo : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N' 0 2 X (hi - lo) : ℕ) ≤
          2 * X := by
      simpa only [N', M', lo, hi, typeIICorrelationHigherParameter,
        zero_mul, zero_div] using hevalTop
    have hraw :=
      norm_reciprocalPhaseSum_zero_quadratic_le_fourStepWeyl_twoTerm
        N' orders lo hi hN' hX hFlow' herrorSmall' hLength
          (by simpa only [lo] using haIcc) hevalY' hevalTop' hrFive hrSix
    simpa only [N', M', lo, hi, typeIICorrelationHigherParameter,
      zero_mul, zero_div] using hraw
  · have hhi : hi ≤ lo := by omega
    have hzero : hi - lo = 0 := Nat.sub_eq_zero_of_le hhi
    have hIco : Finset.Ico lo hi = ∅ := Finset.Ico_eq_empty_of_le hhi
    rw [reciprocalPhaseSum, hIco, hzero]
    simp only [Finset.sum_empty, norm_zero, Nat.cast_zero, Real.log_zero,
      add_zero]
    have hF' : 0 < reciprocalPhaseScale N' M' 2 X := by
      rw [hM']
      unfold reciprocalPhaseScale
      positivity
    have hp : 0 ≤ reciprocalPhaseFourStepTwoTermWidth N' M' 2 X :=
      (reciprocalPhaseFourStepTwoTermWidth_pos N' M' hX hF').le
    positivity

/-- Pointwise pure-linear Type II Weyl estimate with the same four-kernel
envelope used by the mixed-phase aggregation layer. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_zero_quadratic
    (a b K₀ K₁ q k : ℕ) (N : ℝ) (orders : Finset ℕ)
    {n n' : ℕ} {K B Y E : ℝ}
    (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hN : N ≠ 0) (hK : 0 < K) (hB : 0 < B)
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupper :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K / K ^ 5 ≤ E)
    (hanalytic :
      let N' := typeIICorrelationLinearParameter N n n'
      let M' := typeIICorrelationHigherParameter 0 2 n n'
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      1 ≤ hi - lo →
        reciprocalPhaseScale N' M' 2 K ≤ K ^ 4 ∧
        reciprocalPhaseFourStepEffectiveErrorScale N' M' 2 K (hi - lo) ≤ 1 ∧
        (lo : ℝ) ∈ Set.Icc K Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤ Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
          2 * K) :
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    let F := reciprocalPhaseScale N 0 2 (K * B)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K *
            (E ^ (1 / 1024 : ℝ) +
              4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n))) := by
  dsimp only
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter 0 2 n n'
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  let F := reciprocalPhaseScale N 0 2 (K * B)
  let p := reciprocalPhaseFourStepTwoTermWidth N' M' 2 K
  let δ : ℝ := 1 / 1024
  let J : ℝ := ((((5 + 2) ^ 5 : ℕ) : ℝ))
  let C : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  have hN' : N' ≠ 0 := by
    unfold N' typeIICorrelationLinearParameter
    exact typeIICorrelationLinearParameter_ne_zero hN
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hM' : M' = 0 := by simp [M', typeIICorrelationHigherParameter]
  have hscale : 0 < reciprocalPhaseScale N' M' 2 K := by
    rw [hM']
    unfold reciprocalPhaseScale
    positivity
  have hEnonneg : 0 ≤ E := by
    have hu : 0 ≤ reciprocalPhaseScale N' M' 2 K / K ^ 5 := by positivity
    exact hu.trans (by simpa only [N', M'] using hupper)
  by_cases hLength : 1 ≤ hi - lo
  · rcases hanalytic hLength with
      ⟨hFlow, herrorSmall, haIcc, hevalY, hevalTop⟩
    have hpoint :=
      norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_twoTerm_zero_quadratic
        a b K₀ K₁ q k N orders hq hn hn' hne hN hK hrFive hrSix hanalytic
    have hwidthOne : p ≤ 1 :=
      reciprocalPhaseFourStepTwoTermWidth_le_one N' M' hK hscale
        (by simpa only [N', M', p] using herrorSmall)
    have hwidthTwo : p ≤ E ^ δ +
        2 * typeIIDecayKernel B F δ (Nat.dist n' n) := by
      simpa only [N', M', F, p, δ] using
        (reciprocalPhaseFourStepTwoTermWidth_typeIICorrelation_zero_quadratic_le
          N K B E hN hK hB hn hn' hne hnB hn'B hwidthOne hupper)
    have hkernel : 0 ≤ typeIIDecayKernel B F δ (Nat.dist n' n) :=
      typeIIDecayKernel_nonneg δ _ hB (by unfold F reciprocalPhaseScale; positivity)
    have hwidth : p ≤ E ^ δ +
        4 * typeIIDecayKernel B F δ (Nat.dist n' n) :=
      hwidthTwo.trans (by nlinarith)
    let Q : ℝ := C * (480 * J * ((J + 1) *
      (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K))
    have hlog : 0 ≤ Real.log ((hi - lo : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hLength
    have hQ : 0 ≤ Q := by unfold Q C J; positivity
    have hpoint' :
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤ Q * p := by
      refine hpoint.trans_eq ?_
      unfold Q C J p N' M' lo hi
      ring
    have hfinal := hpoint'.trans (mul_le_mul_of_nonneg_left hwidth hQ)
    convert hfinal using 1
    all_goals
      unfold Q C J F δ lo hi
      ring
  · have hhi : hi ≤ lo := by omega
    have hzero : hi - lo = 0 := Nat.sub_eq_zero_of_le hhi
    have hIco : Finset.Ico lo hi = ∅ := Finset.Ico_eq_empty_of_le hhi
    rw [typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
      a b K₀ K₁ q k N 0 2 hq hn hn', reciprocalPhaseSum, hIco, hzero]
    simp only [Finset.sum_empty, norm_zero, Nat.cast_zero, Real.log_zero,
      add_zero]
    have hkernel : 0 ≤ typeIIDecayKernel B F δ (Nat.dist n' n) :=
      typeIIDecayKernel_nonneg δ _ hB (by unfold F reciprocalPhaseScale; positivity)
    have hEpow : 0 ≤ E ^ δ := Real.rpow_nonneg hEnonneg δ
    have hsum : 0 ≤ E ^ δ + 4 * typeIIDecayKernel B F δ (Nat.dist n' n) := by
      positivity
    positivity

/-- Pointwise low-transformed-scale pure-linear Type II estimate with all
four-step analytic side conditions discharged from the short-block geometry. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_zero_quadratic_lowScale
    (a b K₀ K₁ q k : ℕ) (N : ℝ) (orders : Finset ℕ)
    {n n' : ℕ} {K B E : ℝ}
    (hK₀ : 0 < K₀) (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n')
    (hne : n ≠ n') (hN : N ≠ 0)
    (hKouter : K = ((K₀ + k * q : ℕ) : ℝ)) (hB : 0 < B)
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupper : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K / K ^ 5 ≤ E)
    (hscale : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K ≤ K ^ 4)
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N 0 2 (K * B) / B)
    (hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K)
    (hqK : 5 * (q : ℝ) ≤ K) :
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    let F := reciprocalPhaseScale N 0 2 (K * B)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K *
            (E ^ (1 / 1024 : ℝ) +
              4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n))) := by
  dsimp only
  have hKnat : 0 < K₀ + k * q := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hpairError : reciprocalPhaseScale
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter 0 2 n n') 2 K / K ^ 5 ≤ 1 / K :=
    div_pow_five_le_one_div_of_le_pow_four hK hscale
  have hanalytic :
      let N' := typeIICorrelationLinearParameter N n n'
      let M' := typeIICorrelationHigherParameter 0 2 n n'
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      1 ≤ hi - lo →
        reciprocalPhaseScale N' M' 2 K ≤ K ^ 4 ∧
        reciprocalPhaseFourStepEffectiveErrorScale N' M' 2 K (hi - lo) ≤ 1 ∧
        (lo : ℝ) ∈ Set.Icc K (2 * K) ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
          2 * K ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
          2 * K := by
    dsimp only
    intro hLength
    have herror : reciprocalPhaseFourStepEffectiveErrorScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K
        (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
          typeIIProductRestrictedBlockLower a K₀ q k n n') ≤ 1 := by
      apply reciprocalPhaseFourStepEffectiveErrorScale_typeIICorrelation_le_one_of_far_zero_quadratic
        N K B
        (reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter 0 2 n n') 2 K / K ^ 5)
        hK hB hn hn' hnB hn'B
      · exact le_rfl
      · apply mul_error_le_one_div_four_of_error_le_one_div
        · positivity
        · exact hK
        · exact hpairError
        · exact hKbudget
      · exact hLength
      · exact hfar
    have hN' : typeIICorrelationLinearParameter N n n' ≠ 0 :=
      typeIICorrelationLinearParameter_ne_zero hN
        (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
    have hF' : 0 < reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K := by
      have hzero : typeIICorrelationHigherParameter 0 2 n n' = 0 := by
        simp [typeIICorrelationHigherParameter]
      rw [hzero]
      unfold reciprocalPhaseScale
      positivity
    have hlenNat :
        typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
          typeIIProductRestrictedBlockLower a K₀ q k n n' ≤ q :=
      typeIIProductRestrictedBlock_length_le a b K₀ K₁ q k n n'
    have hlen :
        ((typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
          typeIIProductRestrictedBlockLower a K₀ q k n n' : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hlenNat
    have hrangeRaw := reciprocalPhaseFourStepOptimizedRange_cast_le_of_error_bound
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter 0 2 n n') hK hF' herror
    have hrange :
        (reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n') : ℝ) ≤ (q : ℝ) := by
      calc
        (reciprocalPhaseFourStepOptimizedRange
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter 0 2 n n') 2 K
            (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
              typeIIProductRestrictedBlockLower a K₀ q k n n') : ℝ) ≤
          ((typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n' : ℕ) : ℝ) *
              (1 : ℝ) ^ (1 / 128 : ℝ) := hrangeRaw
        _ = ((typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n' : ℕ) : ℝ) := by
              norm_num
        _ ≤ (q : ℝ) := hlen
    have hmargin : (q : ℝ) +
        (4 * reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n') : ℕ) ≤ K := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      have hfour := mul_le_mul_of_nonneg_left hrange (by norm_num : (0 : ℝ) ≤ 4)
      calc
        (q : ℝ) + 4 *
            (reciprocalPhaseFourStepOptimizedRange
              (typeIICorrelationLinearParameter N n n')
              (typeIICorrelationHigherParameter 0 2 n n') 2 K
              (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
                typeIIProductRestrictedBlockLower a K₀ q k n n') : ℝ) ≤
          (q : ℝ) + 4 * (q : ℝ) := add_le_add le_rfl hfour
        _ = 5 * (q : ℝ) := by ring
        _ ≤ K := hqK
    have hgeom := typeIIProductRestrictedBlock_quadratic_fourStep_geometryAt
      a b K₀ K₁ q k n n'
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter 0 2 n n') K hKouter hLength hmargin
    exact ⟨hscale, herror, hgeom.1, hgeom.2.1, hgeom.2.1⟩
  exact norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_zero_quadratic
    a b K₀ K₁ q k N orders hq hn hn' hne hN hK hB hnB hn'B
      hrFive hrSix hupper hanalytic

/-- Kernel-callback form of the pure-linear high-pair Vinogradov saving. -/
theorem eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_kernelCallback_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A C₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b K₀ K₁ q k : ℕ) (N K : ℝ) (n n' : ℕ)
        (orders : Finset ℕ) (B F : ℝ),
        K = ((K₀ + k * q : ℕ) : ℝ) →
        2 ≤ K → 0 < q → (q : ℝ) ≤ K →
        0 < n → 0 < n' → n ≠ n' → N ≠ 0 →
        0 < B → 0 ≤ F →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter 0 2 n n') 2 K ≤
          C₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log K →
        K ^ 4 ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K →
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (q : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            3 * (Real.log P) ^ (-T)) := by
  have hsaving :=
    eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logSaving_zero_quadratic
      hVinogradov hA hC₀ hc hε ha hAT
  filter_upwards [hsaving,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hsavingP hlog
  intro a b K₀ K₁ q k N K n n' orders B F hKouter hK hq hqK hn hn'
    hne hN hB hF hFupper hKlower hFhigh
  dsimp only
  have hnorm := hsavingP a b K₀ K₁ q k N K n n' hKouter hK hq hqK hn hn'
    hne hN hFupper hKlower hFhigh
  let Ccount : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  let J : ℝ := ((((5 + 2) ^ 5 : ℕ) : ℝ))
  let Q : ℝ := Ccount *
    (480 * J * ((J + 1) * (1 + Real.log (q : ℝ))) * K)
  let V : ℝ := 3 * (Real.log P) ^ (-T)
  have hqOne : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  have hCcount : 1 ≤ Ccount := by
    unfold Ccount
    exact_mod_cast (by omega : 1 ≤ 370 * orders.card + 173)
  have hJ : 1 ≤ J := by unfold J; norm_num
  have h480J : 1 ≤ 480 * J :=
    one_le_mul_of_one_le_of_one_le (by norm_num) hJ
  have hJplus : 1 ≤ J + 1 := by linarith
  have hlogFactor : 1 ≤ 1 + Real.log (q : ℝ) := by linarith
  have htail : 1 ≤ (J + 1) * (1 + Real.log (q : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hJplus hlogFactor
  have hmiddle : 1 ≤ 480 * J *
      ((J + 1) * (1 + Real.log (q : ℝ))) :=
    one_le_mul_of_one_le_of_one_le h480J htail
  have hcoefficient : 1 ≤ Ccount *
      (480 * J * ((J + 1) * (1 + Real.log (q : ℝ)))) :=
    one_le_mul_of_one_le_of_one_le hCcount hmiddle
  have hKQ : K ≤ Q := by
    have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 2).trans hK
    have hmul := mul_le_mul_of_nonneg_right hcoefficient hK0
    calc
      K = 1 * K := by ring
      _ ≤ (Ccount * (480 * J *
          ((J + 1) * (1 + Real.log (q : ℝ))))) * K := hmul
      _ = Q := by unfold Q; ring
  have hV0 : 0 ≤ V := by unfold V; positivity
  have hkernel := typeIIDecayKernel_nonneg
    (1 / 1024 : ℝ) (Nat.dist n' n) hB hF
  calc
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤
        3 * K * (Real.log P) ^ (-T) := hnorm
    _ = K * V := by unfold V; ring
    _ ≤ Q * V := mul_le_mul_of_nonneg_right hKQ hV0
    _ ≤ Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ)
        (Nat.dist n' n) + V) := by
          gcongr
          nlinarith
    _ = ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log (q : ℝ)) * K) *
        (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
          3 * (Real.log P) ^ (-T)) := by
            unfold Q V Ccount J
            ring

/-- Pure-linear Type II Weyl--Vinogradov hybrid on an arbitrary pair of
short blocks.  This is the first aggregation step above the pointwise
correlation estimates. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_zero_quadratic
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B V : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hKouter : K = ((K₀ + kouter * qouter : ℕ) : ℝ))
    (hB : 0 < B) (hS₁ : (S₁ : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N 0 2 (K * B))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K)
    (hqouterK : 5 * (qouter : ℝ) ≤ K) (hV : 0 ≤ V)
    (hhigh : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N 0 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K →
        let F := reciprocalPhaseScale N 0 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter)
            N 0 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V)) :
    let F := reciprocalPhaseScale N 0 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N 0 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) + V)))) := by
  dsimp only
  let F := reciprocalPhaseScale N 0 2 (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hKnat : 0 < K₀ + kouter * qouter := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hInvK : 0 ≤ 1 / K := by positivity
  have hInvKpow : 0 ≤ (1 / K) ^ δ := Real.rpow_nonneg hInvK _
  have hZ : 0 ≤ (1 / K) ^ δ + V := add_nonneg hInvKpow hV
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hfarBound : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N 0 2 (K * B) / B →
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N 0 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            ((1 / K) ^ δ + V)) := by
    intro n hnmem n' hn'mem hne hfar
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hnUpper : n ≤ S₁ := by omega
    have hn'Upper : n' ≤ S₁ := by omega
    have hnB : (n : ℝ) ≤ B :=
      (by exact_mod_cast hnUpper : (n : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    have hn'B : (n' : ℝ) ≤ B :=
      (by exact_mod_cast hn'Upper : (n' : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    by_cases hscale : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter 0 2 n n') 2 K ≤ K ^ 4
    · have hpairError : reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K / K ^ 5 ≤ 1 / K :=
        div_pow_five_le_one_div_of_le_pow_four hK hscale
      have hraw :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_zero_quadratic_lowScale
          a b K₀ K₁ qouter kouter N orders hK₀ hqouter hnpos hn'pos hne
            hN hKouter hB hnB hn'B hrFive hrSix hpairError hscale hfar
            hKbudget hqouterK
      have hlow :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength_unequal
          a b K₀ K₁ qouter kouter N 0 orders hqouter hK.le hB hInvK hraw
      have hadd : 4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
          (1 / K) ^ δ ≤
          4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            ((1 / K) ^ δ + V) := by linarith
      have hlow' : ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N 0 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            (1 / K) ^ δ) := by
        simpa only [F, Q, δ] using hlow
      exact hlow'.trans (mul_le_mul_of_nonneg_left hadd hQ)
    · have hscaleHigh : K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K := lt_of_not_ge hscale
      have hhighPair := hhigh n hnmem n' hn'mem hne hfar hscaleHigh
      have hadd : 4 * typeIIDecayKernel B F δ (Nat.dist n' n) + V ≤
          4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            ((1 / K) ^ δ + V) := by linarith
      have hhighPair' : ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N 0 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + V) := by
        simpa only [F, Q, δ] using hhighPair
      exact hhighPair'.trans (mul_le_mul_of_nonneg_left hadd hQ)
  have hqouterK' : (qouter : ℝ) ≤ K := by nlinarith [hqouterK]
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_nearFar_of_farBound_additiveError_unequal
      a b γ N 0 orders K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hK hB hqinnerB hF hZ hqouterK' hfarBound
  simpa only [F, Q, δ] using hresult

/-- Canonical Vaughan-inner-block specialization of the pure-linear
high-pair callback. -/
theorem eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_vaughanInnerBlockCallback_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b Bcap K₀ K₁ q k : ℕ) (N K : ℝ) (n n' : ℕ)
        (orders : Finset ℕ) (B F : ℝ) (tl : ℕ × ℕ),
        K = ((K₀ + k * q : ℕ) : ℝ) →
        2 ≤ K → 0 < q → (q : ℝ) ≤ K →
        n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl →
        n' ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl →
        0 < n → 0 < n' → n ≠ n' → N ≠ 0 →
        0 < B → 0 ≤ F →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log K →
        K ^ 4 ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K →
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (q : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N 0 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            3 * (Real.log P) ^ (-T)) := by
  have hcallback :=
    eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_kernelCallback_zero_quadratic
      hVinogradov hA (show 0 < 5 * A₀ by positivity) hc hε ha hAT
  filter_upwards [hcallback] with P hcallbackP
  intro a b Bcap K₀ K₁ q k N K n n' orders B F tl hKouter hK hq hqK
    hnBlock hn'Block hn hn' hne hN hB hF hNupper hKlower hFhigh
  have hzeroUpper : |(0 : ℝ)| ≤
      A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) := by
    simpa using mul_nonneg hA₀.le (Real.exp_pos _).le
  have hFupper :=
    reciprocalPhaseScale_typeIICorrelation_le_exp_of_dyadicBlock
      (j := 2) (sk := tl) (n := n) (n' := n')
      N 0 K P A₀ (3 / 2 - ε) (vaughanShortIntervalBudget Bcap)
      (vaughanShortIntervalBudget_pos Bcap) (by norm_num) (by linarith : 1 ≤ K)
        hnBlock hn'Block hA₀.le hNupper hzeroUpper
  norm_num at hFupper
  exact hcallbackP a b K₀ K₁ q k N K n n' orders B F hKouter hK hq hqK
    hn hn' hne hN hB hF hFupper hKlower hFhigh

/-- Canonical Vaughan dyadic-block specialization of the pure-linear
Weyl--Vinogradov hybrid. -/
theorem sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_weylVinogradov_zero_quadratic
    (a b Bcap : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (sk tl : ℕ × ℕ) {L d V : ℝ}
    (hBcap : 0 < Bcap) (hlog : 2 ≤ Real.log Bcap)
    (hDouter : (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ sk.1 : ℕ))
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L) (hN : N ≠ 0)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) (hd : 0 ≤ d)
    (hFhigh : (Real.log Bcap) ^ d ≤ reciprocalPhaseScale N 0 2
      (((dyadicShortIntervalLeftEndpoint (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)))
    (hV : 0 ≤ V)
    (hhigh :
      let qouter := dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget Bcap)
      let K : ℝ := (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget Bcap) sk : ℕ)
      let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
      ∀ n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl,
        ∀ n' ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget Bcap) tl, n ≠ n' →
          3 ≤ (Nat.dist n' n : ℝ) *
            reciprocalPhaseScale N 0 2 (K * B) / B →
          K ^ 4 < reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter 0 2 n n') 2 K →
          let F := reciprocalPhaseScale N 0 2 (K * B)
          let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
            (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
                (1 + Real.log (qouter : ℝ)) * K)
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) sk)
              N 0 2 n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V)) :
    let qouter := dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget Bcap)
    let qinner := dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget Bcap)
    let K : ℝ := (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget Bcap) sk : ℕ)
    let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
    let F := reciprocalPhaseScale N 0 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) sk,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget Bcap) tl)
          γ N 0 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) + V)))) := by
  dsimp only
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget Bcap) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hbudgetLarge : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget Bcap : ℝ) :=
    four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget hBcap hlog
  have hDouterPos : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hDinnerPos : 0 < 2 ^ tl.1 := pow_pos (by omega) tl.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouterPos hbudget
  have hqinner : 0 < qinner := by
    unfold qinner
    exact dyadicShortIntervalLength_pos hDinnerPos hbudget
  have hKouter : K = (((2 ^ sk.1) + sk.2 * qouter : ℕ) : ℝ) := by rfl
  have hlogOne : (1 : ℝ) ≤ Real.log Bcap := by linarith
  have hF : 1 ≤ reciprocalPhaseScale N 0 2 (K * B) := by
    have hpowOne : (1 : ℝ) ≤ (Real.log Bcap) ^ d :=
      Real.one_le_rpow hlogOne hd
    exact hpowOne.trans (by simpa only [K, B] using hFhigh)
  have hB : 0 < B := by unfold B; positivity
  have hS₁ : (((2 * 2 ^ tl.1 : ℕ) : ℝ)) ≤ B := by rfl
  have hqinnerNat : qinner ≤ 2 * 2 ^ tl.1 := by
    have hraw := dyadicShortIntervalLength_le_div_add_one
      (2 ^ tl.1) hbudget
    unfold qinner
    have hdiv : 2 ^ tl.1 / vaughanShortIntervalBudget Bcap ≤ 2 ^ tl.1 :=
      Nat.div_le_self _ _
    omega
  have hqinnerB : (qinner : ℝ) ≤ B := by
    unfold B
    exact_mod_cast hqinnerNat
  have hDouterK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ K := by
    rw [hKouter]
    exact_mod_cast Nat.le_add_right (2 ^ sk.1) (sk.2 * qouter)
  have hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K :=
    hbudgetLarge.trans (hDouter.trans hDouterK)
  have hfive := five_mul_vaughanShortIntervalLength_cast_le
    hBcap hlog hDouter
  have hqouterK : 5 * (qouter : ℝ) ≤ K := by
    have hfiveQ : 5 * (qouter : ℝ) ≤ ((2 ^ sk.1 : ℕ) : ℝ) := by
      simpa only [qouter] using hfive
    exact hfiveQ.trans hDouterK
  have hhigh' : ∀ n ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2,
      ∀ n' ∈ shortIntervalBlock
          (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N 0 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter 0 2 n n') 2 K →
        let F := reciprocalPhaseScale N 0 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock (2 ^ sk.1) (2 * 2 ^ sk.1) qouter sk.2)
            N 0 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V) := by
    simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hhigh
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_zero_quadratic
      a b γ N orders (2 ^ sk.1) (2 * 2 ^ sk.1) (2 ^ tl.1) (2 * 2 ^ tl.1)
      qouter qinner sk.2 tl.2 hDouterPos hDinnerPos hqouter hqinner hL hγ hN
      hKouter hB hS₁ hqinnerB (by simpa only [K, B] using hF)
      hrFive hrSix hKbudget hqouterK hV hhigh'
  simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hresult

/-- Complete conditional pure-linear estimate for one canonical Vaughan Type
II inner double block. -/
theorem eventually_sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_sourceVinogradov_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b Bcap : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
        (sk tl : ℕ × ℕ) (L d : ℝ),
        0 < Bcap → 2 ≤ Real.log Bcap →
        (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ sk.1 : ℕ) →
        0 ≤ L → (∀ n, ‖γ n‖ ≤ L) → N ≠ 0 →
        5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        (Real.log Bcap) ^ d ≤ reciprocalPhaseScale N 0 2
          (((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
            ((2 * 2 ^ tl.1 : ℕ) : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log
          ((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) →
        let qouter := dyadicShortIntervalLength (2 ^ sk.1)
          (vaughanShortIntervalBudget Bcap)
        let qinner := dyadicShortIntervalLength (2 ^ tl.1)
          (vaughanShortIntervalBudget Bcap)
        let K : ℝ := (dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget Bcap) sk : ℕ)
        let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
        let F := reciprocalPhaseScale N 0 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ∑ m ∈ dyadicShortIntervalIndexedBlock
              (vaughanShortIntervalBudget Bcap) sk,
            ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) tl)
              γ N 0 2 m‖ ^ 2 ≤
          (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
            L ^ 2 * ((qinner : ℝ) *
              (Q * (4 *
                  (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                    (1 - (1 / 1024 : ℝ))) * B *
                      F ^ (-(1 / 1024 : ℝ)))) +
                (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) +
                  3 * (Real.log P) ^ (-T))))) := by
  have hcallback :=
    eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_vaughanInnerBlockCallback_zero_quadratic
      hVinogradov hA hA₀ hc hε ha hAT
  filter_upwards [hcallback,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hcallbackP hlogP
  intro a b Bcap γ N orders sk tl L d hBcap hlog hDouter hL hγ hN
    hrFive hrSix hd hFhigh hNupper hKlower
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget Bcap) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N 0 2 (K * B)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hbudgetLarge : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget Bcap : ℝ) :=
    four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget hBcap hlog
  have hDouterPos : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouterPos hbudget
  have hKouter : K = (((2 ^ sk.1) + sk.2 * qouter : ℕ) : ℝ) := by rfl
  have hDouterK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ K := by
    rw [hKouter]
    exact_mod_cast Nat.le_add_right (2 ^ sk.1) (sk.2 * qouter)
  have hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K :=
    hbudgetLarge.trans (hDouter.trans hDouterK)
  have hK : (2 : ℝ) ≤ K :=
    (by norm_num : (2 : ℝ) ≤ 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)))).trans
      hKbudget
  have hfive := five_mul_vaughanShortIntervalLength_cast_le
    hBcap hlog hDouter
  have hqouterK : (qouter : ℝ) ≤ K := by
    have hfiveQ : 5 * (qouter : ℝ) ≤ ((2 ^ sk.1 : ℕ) : ℝ) := by
      simpa only [qouter] using hfive
    linarith
  have hB : 0 < B := by unfold B; positivity
  have hlogOne : (1 : ℝ) ≤ Real.log Bcap := by linarith
  have hFone : 1 ≤ F := by
    have hpowOne : (1 : ℝ) ≤ (Real.log Bcap) ^ d :=
      Real.one_le_rpow hlogOne hd
    exact hpowOne.trans (by simpa only [F, K, B] using hFhigh)
  have hV : 0 ≤ 3 * (Real.log P) ^ (-T) := by positivity
  have hhigh :
      let qouter := dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget Bcap)
      let K : ℝ := (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget Bcap) sk : ℕ)
      let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
      ∀ n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl,
        ∀ n' ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget Bcap) tl, n ≠ n' →
          3 ≤ (Nat.dist n' n : ℝ) *
            reciprocalPhaseScale N 0 2 (K * B) / B →
          K ^ 4 < reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter 0 2 n n') 2 K →
          let F := reciprocalPhaseScale N 0 2 (K * B)
          let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
            (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
                (1 + Real.log (qouter : ℝ)) * K)
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) sk)
              N 0 2 n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
              3 * (Real.log P) ^ (-T)) := by
    dsimp only
    intro n hnBlock n' hn'Block hne _ hpairHigh
    have hnShort : n ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2 := by
      simpa only [dyadicShortIntervalIndexedBlock, qinner] using hnBlock
    have hn'Short : n' ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2 := by
      simpa only [dyadicShortIntervalIndexedBlock, qinner] using hn'Block
    have hnData := mem_shortIntervalBlock.mp hnShort
    have hn'Data := mem_shortIntervalBlock.mp hn'Short
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hraw := hcallbackP a b Bcap (2 ^ sk.1) (2 * 2 ^ sk.1) qouter
      sk.2 N K n n' orders B F tl hKouter hK hqouter hqouterK hnBlock
        hn'Block hnpos hn'pos hne hN hB (zero_le_one.trans hFone) hNupper
        (by simpa only [K] using hKlower) hpairHigh.le
    simpa only [dyadicShortIntervalIndexedBlock, qouter, K, B, F] using hraw
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_weylVinogradov_zero_quadratic
      a b Bcap γ N orders sk tl hBcap hlog hDouter hL hγ hN hrFive hrSix hd
        hFhigh hV hhigh
  simpa only [qouter, qinner, K, B, F] using hresult

/-- Complete conditional estimate for one actual pure-linear source Vaughan
Type II double block. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le_sourceVinogradov_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b U V : ℕ) (N : ℝ) (orders : Finset ℕ) (sk tl : ℕ × ℕ) (d : ℝ),
        0 < b → 2 ≤ Real.log b →
        sk ∈ vaughanShortIntervalIndexBox b →
        tl ∈ vaughanShortIntervalIndexBox b →
        (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ) →
        N ≠ 0 → 5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N 0 2
          (((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
            ((2 * 2 ^ tl.1 : ℕ) : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log
          ((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) →
        let qouter := dyadicShortIntervalLength (2 ^ sk.1)
          (vaughanShortIntervalBudget b)
        let qinner := dyadicShortIntervalLength (2 ^ tl.1)
          (vaughanShortIntervalBudget b)
        let K : ℝ := (dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ)
        let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
        let F := reciprocalPhaseScale N 0 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖weightedConvolutionProductVaughanDoubleBlockSum
            (Finset.Ico a b) b sk tl
            (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient V)‖ ^ 2 ≤
          ((dyadicShortIntervalIndexedBlock
              (vaughanShortIntervalBudget b) sk).card : ℝ) *
            ((qouter : ℝ) * (qinner : ℝ) * (Real.log (2 * b)) ^ 2 +
              (Real.log (2 * b)) ^ 2 * ((qinner : ℝ) *
                (Q * (4 *
                    (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                      (1 - (1 / 1024 : ℝ))) * B *
                        F ^ (-(1 / 1024 : ℝ)))) +
                  (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) +
                    3 * (Real.log P) ^ (-T)))))) := by
  have hinner :=
    eventually_sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_sourceVinogradov_zero_quadratic
      hVinogradov hA hA₀ hc hε ha hAT
  filter_upwards [hinner] with P hinnerP
  intro a b U V N orders sk tl d hb hlog hsk htl hDouter hN
    hrFive hrSix hd hFhigh hNupper hKlower
  let γ : ℕ → ℂ := vaughanShortIntervalCoefficient
    (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) b tl
  let L : ℝ := Real.log (2 * b)
  have hL : 0 ≤ L := by
    unfold L
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * b)
  have hγ : ∀ n, ‖γ n‖ ≤ L := by
    intro n
    exact norm_vaughanShortIntervalTypeIIGammaCoefficient_le_log_two_mul
      V b hb htl n
  have hinnerBound := hinnerP a b b γ N orders sk tl L d hb hlog hDouter
    hL hγ hN hrFive hrSix hd hFhigh hNupper hKlower
  have hI : ∀ x ∈ Finset.Ico a b, x ≤ b := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    omega
  have hbridge :=
    norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le
      (Finset.Ico a b) b U V sk tl N 0 2 hI
  exact hbridge.trans (mul_le_mul_of_nonneg_left
    (by simpa only [γ, L] using hinnerBound) (Nat.cast_nonneg _))

end
end Tao2026
