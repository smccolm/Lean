import Tao2026.LinearAxisTypeII
import Tao2026.UnequalTypeIISourceBlock

/-!
# Pure-linear Type II source block

This module propagates the zero-quadratic pointwise and double-block estimates
through the complete finite Vaughan Type II block family.  The scalar
majorant algebra is shared with the unequal-coefficient implementation; only
the analytic double-block input is replaced.
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- Complete finite pure-linear Type II source-family assembly. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b U V : ℕ) (N : ℝ) (orders : Finset ℕ) (d : ℝ),
        0 < b → 2 ≤ Real.log b →
        2 * vaughanShortIntervalBudget b ≤ U →
        2 * vaughanShortIntervalBudget b ≤ V →
        N ≠ 0 → 5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N 0 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        2 * Real.exp (c * Real.log P) ≤ (U : ℝ) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient V)‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIISourceBlockMajorantUnequal
                P a b U V N 0 orders sk tl T) := by
  have hblock :=
    eventually_norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le_sourceVinogradov_zero_quadratic
      hVinogradov hA hA₀ hc hε ha hAT
  filter_upwards [hblock] with P hblockP
  intro a b U V N orders d hb hlog hU hV hN hrFive hrSix hd
    hFhigh hNupper hKlower
  apply norm_weightedConvolutionProductSum_le_sum_sqrt_vaughanDoubleBlocks
  intro sk hsk tl htl
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ U
  · have hzero :=
      weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_outerCutoff
        (Finset.Ico a b) b U V sk tl N 0 2 hskCut
    simp [vaughanTypeIISourceBlockMajorantUnequal, hskCut, hzero]
  · have hskLarge : vaughanShortIntervalBudget b ≤ 2 ^ sk.1 := by omega
    by_cases htlCut : 2 * 2 ^ tl.1 ≤ V
    · have hzero :=
        weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_innerCutoff
          (Finset.Ico a b) b U V sk tl N 0 2 htlCut
      simp [vaughanTypeIISourceBlockMajorantUnequal, hskCut, htlCut, hzero]
    · by_cases hsupport :
          vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅
      · have hzero :=
          weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_productSupport_eq_empty_unequal
            a b U V sk tl N 0 hsupport
        simp [vaughanTypeIISourceBlockMajorantUnequal, hskCut, htlCut,
          hsupport, hzero]
      · obtain ⟨mn, hmn⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
        have hskLargeReal :
            (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ) := by
          exact_mod_cast hskLarge
        have hFblock : (Real.log b) ^ d ≤ reciprocalPhaseScale N 0 2
            (((dyadicShortIntervalLeftEndpoint
                (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
              ((2 * 2 ^ tl.1 : ℕ) : ℝ)) :=
          reciprocalPhaseScale_block_lower_of_productSupport_unequal hFhigh hmn
        have hKblock : c * Real.log P ≤ Real.log
            ((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) :=
          log_outerEndpoint_lower_of_not_cutoff hKlower hskCut
        have hlargeBound := hblockP a b U V N orders sk tl d hb hlog hsk htl
          hskLargeReal hN hrFive hrSix hd hFblock hNupper hKblock
        simpa only [vaughanTypeIISourceBlockMajorantUnequal, hskCut, htlCut,
          hsupport, if_false] using hlargeBound

/-- Canonical cutoff and order-set specialization of the pure-linear Type II
family estimate. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonical_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N 0 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIICanonicalSourceBlockMajorantUnequal
                P a b N 0 sk tl T) := by
  have hfamily :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_zero_quadratic
      hVinogradov hA hA₀ (by norm_num : (0 : ℝ) < 1 / 4) hε ha hAT
  obtain ⟨Bbudget, hbudget⟩ := eventually_atTop.1
    eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff
  obtain ⟨Bquarter, hquarter⟩ := eventually_atTop.1
    eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff
  let B₀ := max Bbudget Bquarter
  filter_upwards [hfamily, eventually_ge_atTop (max (B₀ : ℝ) 1)] with
      P hfamilyP hP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  have hB₀Real : (B₀ : ℝ) ≤ b :=
    (le_max_left _ _).trans hP |>.trans hPb
  have hB₀ : B₀ ≤ b := by exact_mod_cast hB₀Real
  have hbudgetB :
      2 * vaughanShortIntervalBudget b ≤ vaughanSourceTailCutoff b :=
    hbudget b ((le_max_left _ _).trans hB₀)
  have hquarterB : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ) :=
    hquarter b ((le_max_right _ _).trans hB₀)
  have hPone : (1 : ℝ) ≤ P := (le_max_right _ _).trans hP
  have hPpow : P ^ (1 / 4 : ℝ) ≤ (b : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hPb (by norm_num)
  have hexp : Real.exp ((1 / 4 : ℝ) * Real.log P) =
      P ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hPone)]
    congr 1
    ring
  have hcutoffLower : 2 * Real.exp ((1 / 4 : ℝ) * Real.log P) ≤
      (vaughanSourceTailCutoff b : ℝ) := by
    rw [hexp]
    exact (mul_le_mul_of_nonneg_left hPpow (by norm_num)).trans hquarterB
  simpa only [vaughanTypeIICanonicalSourceBlockMajorantUnequal] using
    hfamilyP a b (vaughanSourceTailCutoff b) (vaughanSourceTailCutoff b)
      N vaughanTypeIICanonicalOrders d hb hlog hbudgetB hbudgetB hN
      five_mem_vaughanTypeIICanonicalOrders six_mem_vaughanTypeIICanonicalOrders
      hd hFhigh hNupper hcutoffLower

/-- Pure-linear complete Type II family after uniform absorption of phase and
outer-endpoint decay. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_decayAbsorbed_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N 0 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ((Nat.log 2 b + 1 : ℕ) : ℝ) ^ 204 *
            Real.sqrt
              (vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T) := by
  have hcanonical :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonical_zero_quadratic
      hVinogradov hA hA₀ hε ha hAT
  obtain ⟨Bbudget, hbudget⟩ := eventually_atTop.1
    eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff
  obtain ⟨Bquarter, hquarter⟩ := eventually_atTop.1
    eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff
  let B₀ := max Bbudget Bquarter
  filter_upwards [hcanonical,
      eventually_ge_atTop (max (B₀ : ℝ) 1)] with P hcanonicalP hP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  have hPone : (1 : ℝ) ≤ P := (le_max_right _ _).trans hP
  have hB₀Real : (B₀ : ℝ) ≤ b :=
    (le_max_left _ _).trans hP |>.trans hPb
  have hB₀ : B₀ ≤ b := by exact_mod_cast hB₀Real
  have hbudgetB :
      2 * vaughanShortIntervalBudget b ≤ vaughanSourceTailCutoff b :=
    hbudget b ((le_max_left _ _).trans hB₀)
  have hquarterB : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ) :=
    hquarter b ((le_max_right _ _).trans hB₀)
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalSourceBlockMajorantUnequal
              P a b N 0 sk tl T) :=
      hcanonicalP a b N d hPb hb hlog hN hd hFhigh hNupper
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt
              (vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T) := by
      apply Finset.sum_le_sum
      intro sk hsk
      apply Finset.sum_le_sum
      intro tl htl
      exact Real.sqrt_le_sqrt
        (vaughanTypeIICanonicalSourceBlockMajorantUnequal_le_decayAbsorbed
          hPone hb hlog hbudgetB hquarterB hFhigh hsk)
    _ = ((vaughanShortIntervalIndexBox b).card : ℝ) ^ 2 *
          Real.sqrt
            (vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ((Nat.log 2 b + 1 : ℕ) : ℝ) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T) := by
      rw [card_vaughanShortIntervalIndexBox, Nat.cast_pow]
      ring

/-- Flattened source-facing form of the pure-linear complete Type II
estimate. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_explicitDecay_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N 0 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          (3 * Real.log b) ^ 204 *
            Real.sqrt
              (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) := by
  have habsorbed :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_decayAbsorbed_zero_quadratic
      hVinogradov hA hA₀ hε ha hAT
  filter_upwards [habsorbed] with P habsorbedP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  have hbound := habsorbedP a b N d hPb hb hlog hN hd hFhigh hNupper
  rw [vaughanTypeIICanonicalDecayAbsorbedBlockMajorant_eq_explicit
    hb hlog] at hbound
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ((Nat.log 2 b + 1 : ℕ) : ℝ) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) := hbound
    _ ≤ (3 * Real.log b) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) := by
      gcongr
      exact source_natLogTwo_add_one_cast_le_three_mul_log hb hlog

/-- Pure-linear complete Type II estimate with arbitrary logarithmic saving. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T S d : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A)
    (hS : 0 ≤ S)
    (hd : 2 * S + 408 ≤ d / 1024 + 197)
    (hTdecay : 2 * S + 408 ≤ T + 297) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ),
        P ≤ (b : ℝ) → (b : ℝ) ≤ 2 * P → 0 < b →
        2 ≤ Real.log b → N ≠ 0 →
        0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N 0 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          vaughanTypeIICanonicalFamilyDecayConstant * (b : ℝ) *
            (Real.log P) ^ (-S) := by
  have hfamily :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_explicitDecay_zero_quadratic
      hVinogradov hA hA₀ hε ha hAT
  have hledger :=
    eventually_vaughanTypeIICanonicalExplicitDecayBlockMajorant_le
      (E := 2 * S + 408) (by linarith) hd hTdecay
  filter_upwards [hfamily, hledger,
      eventually_ge_atTop (Real.exp 1)] with P hfamilyP hledgerP hPlarge
  intro a b N hPb hbP hb hlog hN hd0 hFhigh hNupper
  have hPpos : 0 < P := (Real.exp_pos 1).trans_le hPlarge
  have hbpos : (0 : ℝ) < b := hPpos.trans_le hPb
  have hlogPone : 1 ≤ Real.log P :=
    (Real.le_log_iff_exp_le hPpos).2 hPlarge
  have hlogbUpper : Real.log b ≤ 2 * Real.log P := by
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      Real.log b ≤ Real.log (2 * P) := Real.log_le_log hbpos hbP
      _ = Real.log 2 + Real.log P := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPpos.ne']
      _ ≤ 2 * Real.log P := by linarith
  have hC0 : 0 ≤ vaughanTypeIICanonicalDecayConstant := by
    unfold vaughanTypeIICanonicalDecayConstant
      vaughanTypeIICanonicalQConstant
    positivity
  have hraw := hfamilyP a b N d hPb hb hlog hN hd0 hFhigh hNupper
  have hblock := hledgerP b hPb
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        (3 * Real.log b) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) := hraw
    _ ≤ (3 * Real.log b) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalDecayConstant * (b : ℝ) ^ 2 *
              (Real.log P) ^ (-(2 * S + 408))) := by
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hblock)
        (pow_nonneg (by linarith : 0 ≤ 3 * Real.log b) _)
    _ ≤ 6 ^ (204 : ℕ) * Real.sqrt vaughanTypeIICanonicalDecayConstant *
          (b : ℝ) * (Real.log P) ^ (-S) :=
      three_mul_log_pow_mul_sqrt_decay_le hlogPone hlogbUpper hC0 rfl
    _ = vaughanTypeIICanonicalFamilyDecayConstant * (b : ℝ) *
          (Real.log P) ^ (-S) := by rfl

/-- Fully explicit pure-linear Type II logarithmic-saving theorem. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_explicit_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (ha : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ),
        P ≤ (b : ℝ) → (b : ℝ) ≤ 2 * P → 0 < b →
        2 ≤ Real.log b → N ≠ 0 →
        (Real.log b) ^ (vaughanTypeIILogSavingPhaseExponent S) ≤
          reciprocalPhaseScale N 0 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          vaughanTypeIICanonicalFamilyDecayConstant * (b : ℝ) /
            (Real.log P) ^ S := by
  have hA : (1 / 4 : ℝ) ≤ vaughanTypeIILogSavingVinogradovExponent S := by
    unfold vaughanTypeIILogSavingVinogradovExponent
    linarith
  have hAT : vaughanTypeIILogSavingSourceExponent S + 2 ≤
      3 * vaughanTypeIILogSavingVinogradovExponent S := by
    unfold vaughanTypeIILogSavingSourceExponent
      vaughanTypeIILogSavingVinogradovExponent
    linarith
  have hd : 2 * S + 408 ≤
      vaughanTypeIILogSavingPhaseExponent S / 1024 + 197 := by
    unfold vaughanTypeIILogSavingPhaseExponent
    ring_nf
    exact le_rfl
  have hTdecay : 2 * S + 408 ≤
      vaughanTypeIILogSavingSourceExponent S + 297 := by
    unfold vaughanTypeIILogSavingSourceExponent
    linarith
  have hd0 : 0 ≤ vaughanTypeIILogSavingPhaseExponent S := by
    unfold vaughanTypeIILogSavingPhaseExponent
    positivity
  have hgeneral :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_zero_quadratic
      hVinogradov hA hA₀ hε ha hAT hS hd hTdecay
  filter_upwards [hgeneral,
      eventually_ge_atTop (Real.exp 1)] with P hgeneralP hPlarge
  intro a b N hPb hbP hb hlog hN hFhigh hNupper
  have hPpos : 0 < P := (Real.exp_pos 1).trans_le hPlarge
  have hlogPpos : 0 < Real.log P :=
    (Real.log_exp 1 ▸ show (0 : ℝ) < 1 by norm_num) |>.trans_le
      (Real.log_le_log (Real.exp_pos 1) hPlarge)
  have hbound := hgeneralP a b N hPb hbP hb hlog hN hd0 hFhigh hNupper
  rw [Real.rpow_neg hlogPpos.le] at hbound
  simpa only [div_eq_mul_inv, mul_assoc] using hbound

end

end Tao2026
