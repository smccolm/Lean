import Tao2026.Vinogradov

/-!
# Unequal-parameter Type II Vinogradov bridge

The source Type II correlation and its transformed phase are already stated
for independent reciprocal coefficients.  This module keeps those two
coefficients independent through the high-scale Vinogradov callback.  It is
the high-pair input needed to generalize the completed diagonal Type II source
block to arbitrary Fourier modes.
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- Fixed-constant logarithmic-envelope estimate for an unequal-parameter
product-restricted Type II correlation. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logEnvelopeAt_unequal
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (a b K₀ K₁ q k : ℕ) (N M P A K : ℝ)
    {n n' : ℕ}
    (hKouter : K = ((K₀ + k * q : ℕ) : ℝ))
    (hK : 2 ≤ K) (hq : 0 < q) (hqK : (q : ℝ) ≤ K)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n') (hM : M ≠ 0)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff K
      (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K) + 2 : ℕ) : ℝ)) ≤
          Real.log P)
    (hFhigh : K ^ 4 ≤ reciprocalPhaseScale
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter M 2 n n') 2 K)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K)) ^ 2 /
          (Real.log K) ^ 3 < (1 / 1000 : ℝ)) :
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
      (shortIntervalBlock K₀ K₁ q k) N M 2 n n'‖ ≤
      (2 * Real.log P + 1) *
        (C * (Real.log P) ^ (4 * A) * K * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log K) ^ 3 /
            (Real.log (reciprocalPhaseScale
              (typeIICorrelationLinearParameter N n n')
              (typeIICorrelationHigherParameter M 2 n n') 2 K)) ^ 2)) +
      Real.log P *
        (16 * K * (Real.log P) ^ (-3 * A) + Real.log P + 1) := by
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter M 2 n n'
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  have hM' : M' ≠ 0 := by
    exact typeIICorrelationHigherParameter_ne_zero hM (by norm_num)
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hloNat : K₀ + k * q ≤ lo := le_max_left _ _
  have hlo : K ≤ (lo : ℝ) := by
    rw [hKouter]
    exact_mod_cast hloNat
  have hhiNat : hi ≤ K₀ + (k + 1) * q :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hhi : (hi : ℝ) ≤ 2 * K := by
    calc
      (hi : ℝ) ≤ ((K₀ + (k + 1) * q : ℕ) : ℝ) := by exact_mod_cast hhiNat
      _ = K + (q : ℝ) := by
        rw [hKouter]
        push_cast
        ring
      _ ≤ 2 * K := by linarith
  have hpow : ∀ t ∈ Set.Icc K (2 * K),
      t ^ (2 - 1) ≤ 2 * K ^ (2 - 1) := by
    intro t ht
    norm_num
    exact ht.2
  have hglobal := norm_reciprocalPhaseSum_le_sourceVinogradov_logEnvelopeAt
    C hVinogradov N' M' P A 2 lo hi hK hM' (by norm_num) hlog hA hten
      (by simpa only [N', M'] using hcutoff)
      (by simpa only [N', M'] using hFhigh)
      (by simpa only [N', M'] using hsmall)
      hlo hhi le_rfl hpow
  rw [typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
    a b K₀ K₁ q k N M 2 hq hn hn']
  simpa only [N', M', typeIICorrelationLinearParameter,
    typeIICorrelationHigherParameter] using hglobal

/-- Uniform high-pair logarithmic saving with independent linear and
quadratic reciprocal coefficients. -/
theorem eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logSaving_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A C₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b K₀ K₁ q k : ℕ) (N M K : ℝ) (n n' : ℕ),
        K = ((K₀ + k * q : ℕ) : ℝ) →
        2 ≤ K → 0 < q → (q : ℝ) ≤ K →
        0 < n → 0 < n' → n ≠ n' → M ≠ 0 →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter M 2 n n') 2 K ≤
          C₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log K →
        K ^ 4 ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K →
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N M 2 n n'‖ ≤
            3 * K * (Real.log P) ^ (-T) := by
  obtain ⟨C₁, hVinogradovAt⟩ := hVinogradov
  have hC₁ : 0 < C₁ := hVinogradovAt.1
  have hparameters :=
    eventually_sourceVinogradov_quadraticParameterConditions_of_parameterBound
      hA hC₀ hc hε ha
  have henvelope := eventually_sourceVinogradov_logEnvelope_le
    hC₀ hC₁ hc hε ha hAT
  filter_upwards [hparameters, henvelope] with P hparametersP henvelopeP
  intro a b K₀ K₁ q k N M K n n' hKouter hK hq hqK hn hn' hne hM
    hFupper hKlower hFhigh
  let F := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter M 2 n n') 2 K
  obtain ⟨hlog, hten, hcutoff, hsmall⟩ :=
    hparametersP K F hK (by simpa only [F] using hFhigh)
      (by simpa only [F] using hFupper) hKlower
  have hraw :=
    norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logEnvelopeAt_unequal
      C₁ hVinogradovAt a b K₀ K₁ q k N M P A K hKouter hK hq hqK hn hn'
        hne hM hlog hA hten
        (by simpa only [F] using hcutoff)
        (by simpa only [F] using hFhigh)
        (by simpa only [F] using hsmall)
  exact hraw.trans
    (henvelopeP K F hK (by simpa only [F] using hFhigh)
      (by simpa only [F] using hFupper) hKlower)

/-- Kernel-callback form of the unequal-parameter high-pair saving. -/
theorem eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_kernelCallback_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A C₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b K₀ K₁ q k : ℕ) (N M K : ℝ) (n n' : ℕ)
        (orders : Finset ℕ) (B F : ℝ),
        K = ((K₀ + k * q : ℕ) : ℝ) →
        2 ≤ K → 0 < q → (q : ℝ) ≤ K →
        0 < n → 0 < n' → n ≠ n' → M ≠ 0 →
        0 < B → 0 ≤ F →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter M 2 n n') 2 K ≤
          C₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log K →
        K ^ 4 ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K →
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (q : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N M 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            3 * (Real.log P) ^ (-T)) := by
  have hsaving :=
    eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logSaving_unequal
      hVinogradov hA hC₀ hc hε ha hAT
  filter_upwards [hsaving,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hsavingP hlog
  intro a b K₀ K₁ q k N M K n n' orders B F hKouter hK hq hqK hn hn'
    hne hM hB hF hFupper hKlower hFhigh
  dsimp only
  have hnorm := hsavingP a b K₀ K₁ q k N M K n n' hKouter hK hq hqK hn hn'
    hne hM hFupper hKlower hFhigh
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
        (shortIntervalBlock K₀ K₁ q k) N M 2 n n'‖ ≤
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

/-- Canonical Vaughan-inner-block specialization of the unequal-parameter
high-pair callback.  Independent source bounds on `N` and `M` imply the same
factor-five transformed-scale envelope as in the diagonal specialization. -/
theorem eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_vaughanInnerBlockCallback_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b Bcap K₀ K₁ q k : ℕ) (N M K : ℝ) (n n' : ℕ)
        (orders : Finset ℕ) (B F : ℝ) (tl : ℕ × ℕ),
        K = ((K₀ + k * q : ℕ) : ℝ) →
        2 ≤ K → 0 < q → (q : ℝ) ≤ K →
        n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl →
        n' ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl →
        0 < n → 0 < n' → n ≠ n' → M ≠ 0 →
        0 < B → 0 ≤ F →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log K →
        K ^ 4 ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K →
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (q : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N M 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            3 * (Real.log P) ^ (-T)) := by
  have hcallback :=
    eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_kernelCallback_unequal
      hVinogradov hA (show 0 < 5 * A₀ by positivity) hc hε ha hAT
  filter_upwards [hcallback] with P hcallbackP
  intro a b Bcap K₀ K₁ q k N M K n n' orders B F tl hKouter hK hq hqK
    hnBlock hn'Block hn hn' hne hM hB hF hNupper hMupper hKlower hFhigh
  have hFupper :=
    reciprocalPhaseScale_typeIICorrelation_le_exp_of_dyadicBlock
      (j := 2) (sk := tl) (n := n) (n' := n')
      N M K P A₀ (3 / 2 - ε) (vaughanShortIntervalBudget Bcap)
      (vaughanShortIntervalBudget_pos Bcap) (by norm_num) (by linarith : 1 ≤ K)
        hnBlock hn'Block hA₀.le hNupper hMupper
  norm_num at hFupper
  exact hcallbackP a b K₀ K₁ q k N M K n n' orders B F hKouter hK hq hqK
    hn hn' hne hM hB hF hFupper hKlower hFhigh

end

end Tao2026
