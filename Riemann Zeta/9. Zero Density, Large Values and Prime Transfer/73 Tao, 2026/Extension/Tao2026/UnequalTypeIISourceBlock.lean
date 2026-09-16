import Tao2026.UnequalTypeIIWeyl
import Tao2026.TypeIISourceBlock
import Tao2026.TypeIWeylBridge

open Complex Finset Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- A nonnegative diagonal coefficient whose diagonal quadratic phase scale at
`X` is exactly the scale of the unequal pair `(N,M)` at `X`. -/
noncomputable def reciprocalPhaseScaleDiagonalCoefficient
    (N M X : ℝ) : ℝ :=
  reciprocalPhaseScale N M 2 X * X ^ 2 / (X + 1)

theorem reciprocalPhaseScale_diagonalCoefficient
    (N M X : ℝ) (hX : 0 < X) :
    reciprocalPhaseScale
        (reciprocalPhaseScaleDiagonalCoefficient N M X)
        (reciprocalPhaseScaleDiagonalCoefficient N M X) 2 X =
      reciprocalPhaseScale N M 2 X := by
  have hF : 0 ≤ reciprocalPhaseScale N M 2 X := by
    unfold reciprocalPhaseScale
    positivity
  have hD : 0 ≤ reciprocalPhaseScaleDiagonalCoefficient N M X := by
    unfold reciprocalPhaseScaleDiagonalCoefficient
    positivity
  unfold reciprocalPhaseScale
  rw [abs_of_nonneg hD]
  unfold reciprocalPhaseScaleDiagonalCoefficient reciprocalPhaseScale
  field_simp [hX.ne', (by linarith : X + 1 ≠ 0)]

/-- The exact source block ledger with independent linear and quadratic
reciprocal-phase coefficients. -/
noncomputable def vaughanTypeIISourceBlockMajorantUnequal
    (P : ℝ) (a b U V : ℕ) (N M : ℝ) (orders : Finset ℕ)
    (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget b)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget b)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N M 2 (K * B)
  let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  if 2 * 2 ^ sk.1 ≤ U then 0
  else if 2 * 2 ^ tl.1 ≤ V then 0
  else if vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅ then 0
  else
    ((dyadicShortIntervalIndexedBlock
        (vaughanShortIntervalBudget b) sk).card : ℝ) *
      ((qouter : ℝ) * (qinner : ℝ) * (Real.log (2 * b)) ^ 2 +
        (Real.log (2 * b)) ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B *
                  F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) +
              3 * (Real.log P) ^ (-T))))))

/-- Canonical cutoffs and derivative orders substituted into the unequal
source block ledger. -/
noncomputable def vaughanTypeIICanonicalSourceBlockMajorantUnequal
    (P : ℝ) (a b : ℕ) (N M : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  vaughanTypeIISourceBlockMajorantUnequal P a b
    (vaughanSourceTailCutoff b) (vaughanSourceTailCutoff b) N M
    vaughanTypeIICanonicalOrders sk tl T

/-- Empty product support annihilates a Vaughan Type II double block for
arbitrary phase coefficients. -/
theorem weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_productSupport_eq_empty_unequal
    (a b U V : ℕ) (sk tl : ℕ × ℕ) (N M : ℝ)
    (hsupport : vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅) :
    weightedConvolutionProductVaughanDoubleBlockSum
        (Finset.Ico a b) b sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeIIBetaCoefficient U) (vaughanTypeIIGammaCoefficient V) = 0 := by
  classical
  unfold weightedConvolutionProductVaughanDoubleBlockSum
  apply Finset.sum_eq_zero
  intro mn hmn
  by_cases hβ : vaughanShortIntervalCoefficient
      (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) b sk mn.1 = 0
  · simp [hβ]
  by_cases hγ : vaughanShortIntervalCoefficient
      (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) b tl mn.2 = 0
  · simp [hγ]
  have hmnData := Finset.mem_filter.mp hmn
  have hbox := Finset.mem_product.mp hmnData.1
  have hmpos := (Finset.mem_Ioc.mp hbox.1).1
  have hnpos := (Finset.mem_Ioc.mp hbox.2).1
  have hmblock := mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
    (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) hmpos hβ
  have hnblock := mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
    (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) hnpos hγ
  have hcanonical : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmblock, hnblock⟩, hmnData.2⟩
  rw [hsupport] at hcanonical
  simp at hcanonical

/-- Product support transfers a single lower bound at scale `2b` to every
active unequal Type II double block. -/
theorem reciprocalPhaseScale_block_lower_of_productSupport_unequal
    {a b : ℕ} {N M d : ℝ} {sk tl : ℕ × ℕ} {mn : ℕ × ℕ}
    (hglobal : (Real.log b) ^ d ≤
      reciprocalPhaseScale N M 2 (2 * (b : ℝ)))
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2
      (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)) := by
  let X : ℝ := ((dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
      ((2 * 2 ^ tl.1 : ℕ) : ℝ)
  have hXpos : 0 < X := by
    unfold X
    have hleft : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk := by
      unfold dyadicShortIntervalLeftEndpoint
      exact (pow_pos (by omega : 0 < (2 : ℕ)) sk.1).trans_le
        (Nat.le_add_right _ _)
    have hright : 0 < 2 * 2 ^ tl.1 := by positivity
    exact mul_pos (by exact_mod_cast hleft) (by exact_mod_cast hright)
  have hXupper : X ≤ 2 * (b : ℝ) := by
    simpa only [X] using vaughanTypeIIDoubleBlockProductScale_le_two_mul hmn
  exact hglobal.trans (by
    simpa only [X] using reciprocalPhaseScale_anti N M 2 hXpos hXupper)

/-- Complete finite Type II source-family assembly with independent phase
coefficients. The high-frequency premise is expressed invariantly as a lower
bound for the source scale at the maximal active product scale `2b`. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b U V : ℕ) (N M : ℝ) (orders : Finset ℕ) (d : ℝ),
        0 < b → 2 ≤ Real.log b →
        2 * vaughanShortIntervalBudget b ≤ U →
        2 * vaughanShortIntervalBudget b ≤ V →
        M ≠ 0 → 5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        2 * Real.exp (c * Real.log P) ≤ (U : ℝ) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient V)‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIISourceBlockMajorantUnequal
                P a b U V N M orders sk tl T) := by
  have hblock :=
    eventually_norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le_sourceVinogradov_unequal
      hVinogradov hA hA₀ hc hε ha hAT
  filter_upwards [hblock] with P hblockP
  intro a b U V N M orders d hb hlog hU hV hM hrFive hrSix hd
    hFhigh hNupper hMupper hKlower
  apply norm_weightedConvolutionProductSum_le_sum_sqrt_vaughanDoubleBlocks
  intro sk hsk tl htl
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ U
  · have hzero :=
      weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_outerCutoff
        (Finset.Ico a b) b U V sk tl N M 2 hskCut
    simp [vaughanTypeIISourceBlockMajorantUnequal, hskCut, hzero]
  · have hskLarge : vaughanShortIntervalBudget b ≤ 2 ^ sk.1 := by omega
    by_cases htlCut : 2 * 2 ^ tl.1 ≤ V
    · have hzero :=
        weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_innerCutoff
          (Finset.Ico a b) b U V sk tl N M 2 htlCut
      simp [vaughanTypeIISourceBlockMajorantUnequal, hskCut, htlCut, hzero]
    · by_cases hsupport :
          vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅
      · have hzero :=
          weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_productSupport_eq_empty_unequal
            a b U V sk tl N M hsupport
        simp [vaughanTypeIISourceBlockMajorantUnequal, hskCut, htlCut,
          hsupport, hzero]
      · obtain ⟨mn, hmn⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
        have hskLargeReal :
            (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ) := by
          exact_mod_cast hskLarge
        have hFblock : (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2
            (((dyadicShortIntervalLeftEndpoint
                (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
              ((2 * 2 ^ tl.1 : ℕ) : ℝ)) :=
          reciprocalPhaseScale_block_lower_of_productSupport_unequal hFhigh hmn
        have hKblock : c * Real.log P ≤ Real.log
            ((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) :=
          log_outerEndpoint_lower_of_not_cutoff hKlower hskCut
        have hlargeBound := hblockP a b U V N M orders sk tl d hb hlog hsk htl
          hskLargeReal hM hrFive hrSix hd hFblock hNupper hMupper hKblock
        simpa only [vaughanTypeIISourceBlockMajorantUnequal, hskCut, htlCut,
          hsupport, if_false] using hlargeBound

/-- Canonical cube-root cutoff specialization of the complete unequal Type II
family estimate. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonicalCutoff_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N M : ℝ) (orders : Finset ℕ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        M ≠ 0 → 5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIISourceBlockMajorantUnequal
                P a b (vaughanSourceTailCutoff b)
                  (vaughanSourceTailCutoff b) N M orders sk tl T) := by
  have hfamily :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_unequal
      hVinogradov hA hA₀ (by norm_num : (0 : ℝ) < 1 / 4) hε ha hAT
  obtain ⟨Bbudget, hbudget⟩ := eventually_atTop.1
    eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff
  obtain ⟨Bquarter, hquarter⟩ := eventually_atTop.1
    eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff
  let B₀ := max Bbudget Bquarter
  filter_upwards [hfamily, eventually_ge_atTop (max (B₀ : ℝ) 1)] with
      P hfamilyP hP
  intro a b N M orders d hPb hb hlog hM hrFive hrSix hd hFhigh
    hNupper hMupper
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
  exact hfamilyP a b (vaughanSourceTailCutoff b)
    (vaughanSourceTailCutoff b) N M orders d hb hlog hbudgetB hbudgetB
      hM hrFive hrSix hd hFhigh hNupper hMupper hcutoffLower

/-- Fully canonical unequal Type II family estimate with the order set
`{5,6}` fixed. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonical_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N M : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        M ≠ 0 → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIICanonicalSourceBlockMajorantUnequal
                P a b N M sk tl T) := by
  have hcanonical :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonicalCutoff_unequal
      hVinogradov hA hA₀ hε ha hAT
  filter_upwards [hcanonical] with P hcanonicalP
  intro a b N M d hPb hb hlog hM hd hFhigh hNupper hMupper
  simpa only [vaughanTypeIICanonicalSourceBlockMajorantUnequal] using
    hcanonicalP a b N M vaughanTypeIICanonicalOrders d hPb hb hlog hM
      five_mem_vaughanTypeIICanonicalOrders
      six_mem_vaughanTypeIICanonicalOrders hd hFhigh hNupper hMupper

/-- The synthetic diagonal coefficient attached to one unequal Type II block.
It lets the already-audited scalar majorant algebra be reused exactly. -/
noncomputable def vaughanTypeIIUnequalDiagonalCoefficient
    (b : ℕ) (N M : ℝ) (sk tl : ℕ × ℕ) : ℝ :=
  reciprocalPhaseScaleDiagonalCoefficient N M
    (((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
      ((2 * 2 ^ tl.1 : ℕ) : ℝ))

theorem vaughanTypeIIBlockProductScale_pos
    (b : ℕ) (sk tl : ℕ × ℕ) :
    0 < (((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
      ((2 * 2 ^ tl.1 : ℕ) : ℝ)) := by
  have hleft : 0 < dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk := by
    unfold dyadicShortIntervalLeftEndpoint
    exact (pow_pos (by omega : 0 < (2 : ℕ)) sk.1).trans_le
      (Nat.le_add_right _ _)
  have hright : 0 < 2 * 2 ^ tl.1 := by positivity
  exact mul_pos (by exact_mod_cast hleft) (by exact_mod_cast hright)

theorem reciprocalPhaseScale_vaughanTypeIIUnequalDiagonalCoefficient
    (b : ℕ) (N M : ℝ) (sk tl : ℕ × ℕ) :
    reciprocalPhaseScale
        (vaughanTypeIIUnequalDiagonalCoefficient b N M sk tl)
        (vaughanTypeIIUnequalDiagonalCoefficient b N M sk tl) 2
        (((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
          ((2 * 2 ^ tl.1 : ℕ) : ℝ)) =
      reciprocalPhaseScale N M 2
        (((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
          ((2 * 2 ^ tl.1 : ℕ) : ℝ)) := by
  unfold vaughanTypeIIUnequalDiagonalCoefficient
  exact reciprocalPhaseScale_diagonalCoefficient N M _
    (vaughanTypeIIBlockProductScale_pos b sk tl)

theorem vaughanTypeIISourceBlockMajorantUnequal_eq_diagonalized
    (P : ℝ) (a b U V : ℕ) (N M : ℝ) (orders : Finset ℕ)
    (sk tl : ℕ × ℕ) (T : ℝ) :
    vaughanTypeIISourceBlockMajorantUnequal
        P a b U V N M orders sk tl T =
      vaughanTypeIISourceBlockMajorant P a b U V
        (vaughanTypeIIUnequalDiagonalCoefficient b N M sk tl)
        orders sk tl T := by
  unfold vaughanTypeIISourceBlockMajorantUnequal
    vaughanTypeIISourceBlockMajorant
  dsimp only
  rw [reciprocalPhaseScale_vaughanTypeIIUnequalDiagonalCoefficient]

theorem vaughanTypeIICanonicalSourceBlockMajorantUnequal_eq_diagonalized
    (P : ℝ) (a b : ℕ) (N M : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) :
    vaughanTypeIICanonicalSourceBlockMajorantUnequal P a b N M sk tl T =
      vaughanTypeIICanonicalSourceBlockMajorant P a b
        (vaughanTypeIIUnequalDiagonalCoefficient b N M sk tl) sk tl T := by
  unfold vaughanTypeIICanonicalSourceBlockMajorantUnequal
    vaughanTypeIICanonicalSourceBlockMajorant
  exact vaughanTypeIISourceBlockMajorantUnequal_eq_diagonalized
    P a b (vaughanSourceTailCutoff b) (vaughanSourceTailCutoff b)
      N M vaughanTypeIICanonicalOrders sk tl T

/-- Unequal version of the power-saved block ledger, represented through the
exact synthetic diagonal coefficient. -/
noncomputable def vaughanTypeIICanonicalPowerSavedBlockMajorantUnequal
    (P : ℝ) (b : ℕ) (N M : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  vaughanTypeIICanonicalPowerSavedBlockMajorant P b
    (vaughanTypeIIUnequalDiagonalCoefficient b N M sk tl) sk tl T

theorem vaughanTypeIICanonicalSourceBlockMajorantUnequal_le_powerSaved
    {P N M T : ℝ} {a b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hbudget : 2 * vaughanShortIntervalBudget b ≤
      vaughanSourceTailCutoff b)
    (hquarter : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ))
    (hsk : sk ∈ vaughanShortIntervalIndexBox b) :
    vaughanTypeIICanonicalSourceBlockMajorantUnequal P a b N M sk tl T ≤
      vaughanTypeIICanonicalPowerSavedBlockMajorantUnequal
        P b N M sk tl T := by
  rw [vaughanTypeIICanonicalSourceBlockMajorantUnequal_eq_diagonalized]
  exact vaughanTypeIICanonicalSourceBlockMajorant_le_powerSaved
    hP hb hlog hbudget hquarter hsk

theorem vaughanTypeIICanonicalPowerSavedBlockMajorantUnequal_le_decayAbsorbed
    {P N M d T : ℝ} {b : ℕ} {sk tl : ℕ × ℕ}
    (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hF : (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2
      (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)))
    (hK : (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) :
    vaughanTypeIICanonicalPowerSavedBlockMajorantUnequal P b N M sk tl T ≤
      vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T := by
  unfold vaughanTypeIICanonicalPowerSavedBlockMajorantUnequal
  apply vaughanTypeIICanonicalPowerSavedBlockMajorant_le_decayAbsorbed
    hb hlog
  · simpa only [reciprocalPhaseScale_vaughanTypeIIUnequalDiagonalCoefficient]
      using hF
  · exact hK

/-- Every exact unequal canonical source block is bounded by the common
block-independent decay ledger. -/
theorem vaughanTypeIICanonicalSourceBlockMajorantUnequal_le_decayAbsorbed
    {P N M d T : ℝ} {a b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hbudget : 2 * vaughanShortIntervalBudget b ≤
      vaughanSourceTailCutoff b)
    (hquarter : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ))
    (hglobal : (Real.log b) ^ d ≤
      reciprocalPhaseScale N M 2 (2 * (b : ℝ)))
    (hsk : sk ∈ vaughanShortIntervalIndexBox b) :
    vaughanTypeIICanonicalSourceBlockMajorantUnequal P a b N M sk tl T ≤
      vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T := by
  have hdecay0 := vaughanTypeIICanonicalDecayAbsorbedBlockMajorant_nonneg
    (P := P) (d := d) (T := T) (b := b) hP hb hlog
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorantUnequal,
      vaughanTypeIISourceBlockMajorantUnequal, hskCut] using hdecay0
  by_cases htlCut : 2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorantUnequal,
      vaughanTypeIISourceBlockMajorantUnequal, hskCut, htlCut] using hdecay0
  by_cases hsupport : vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅
  · simpa [vaughanTypeIICanonicalSourceBlockMajorantUnequal,
      vaughanTypeIISourceBlockMajorantUnequal, hskCut, htlCut, hsupport] using
      hdecay0
  obtain ⟨mn, hmn⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
  have hFblock : (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2
      (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)) :=
    reciprocalPhaseScale_block_lower_of_productSupport_unequal hglobal hmn
  have hKblock : (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) :=
    (quarter_rpow_lt_outerEndpoint_of_not_vaughanSourceTailCutoff
      hquarter hskCut).le
  exact (vaughanTypeIICanonicalSourceBlockMajorantUnequal_le_powerSaved
      hP hb hlog hbudget hquarter hsk).trans
    (vaughanTypeIICanonicalPowerSavedBlockMajorantUnequal_le_decayAbsorbed
      hb hlog hFblock hKblock)

/-- Complete unequal Type II family after uniform absorption of the phase and
outer-endpoint decay. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_decayAbsorbed_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N M : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        M ≠ 0 → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ((Nat.log 2 b + 1 : ℕ) : ℝ) ^ 204 *
            Real.sqrt
              (vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T) := by
  have hcanonical :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonical_unequal
      hVinogradov hA hA₀ hε ha hAT
  obtain ⟨Bbudget, hbudget⟩ := eventually_atTop.1
    eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff
  obtain ⟨Bquarter, hquarter⟩ := eventually_atTop.1
    eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff
  let B₀ := max Bbudget Bquarter
  filter_upwards [hcanonical,
      eventually_ge_atTop (max (B₀ : ℝ) 1)] with P hcanonicalP hP
  intro a b N M d hPb hb hlog hM hd hFhigh hNupper hMupper
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
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalSourceBlockMajorantUnequal
              P a b N M sk tl T) :=
      hcanonicalP a b N M d hPb hb hlog hM hd hFhigh hNupper hMupper
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

/-- Flattened source-facing form of the unequal complete Type II estimate. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_explicitDecay_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N M : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        M ≠ 0 → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          (3 * Real.log b) ^ 204 *
            Real.sqrt
              (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) := by
  have habsorbed :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_decayAbsorbed_unequal
      hVinogradov hA hA₀ hε ha hAT
  filter_upwards [habsorbed] with P habsorbedP
  intro a b N M d hPb hb hlog hM hd hFhigh hNupper hMupper
  have hbound := habsorbedP a b N M d hPb hb hlog hM hd hFhigh
    hNupper hMupper
  rw [vaughanTypeIICanonicalDecayAbsorbedBlockMajorant_eq_explicit
    hb hlog] at hbound
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ((Nat.log 2 b + 1 : ℕ) : ℝ) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) :=
      hbound
    _ ≤ (3 * Real.log b) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) := by
      gcongr
      exact source_natLogTwo_add_one_cast_le_three_mul_log hb hlog

/-- Unequal complete Type II estimate with arbitrary logarithmic saving. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T S d : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A)
    (hS : 0 ≤ S)
    (hd : 2 * S + 408 ≤ d / 1024 + 197)
    (hTdecay : 2 * S + 408 ≤ T + 297) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N M : ℝ),
        P ≤ (b : ℝ) → (b : ℝ) ≤ 2 * P → 0 < b →
        2 ≤ Real.log b → M ≠ 0 →
        0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          vaughanTypeIICanonicalFamilyDecayConstant * (b : ℝ) *
            (Real.log P) ^ (-S) := by
  have hfamily :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_explicitDecay_unequal
      hVinogradov hA hA₀ hε ha hAT
  have hledger :=
    eventually_vaughanTypeIICanonicalExplicitDecayBlockMajorant_le
      (E := 2 * S + 408) (by linarith) hd hTdecay
  filter_upwards [hfamily, hledger,
      eventually_ge_atTop (Real.exp 1)] with P hfamilyP hledgerP hPlarge
  intro a b N M hPb hbP hb hlog hM hd0 hFhigh hNupper hMupper
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
  have hraw := hfamilyP a b N M d hPb hb hlog hM hd0 hFhigh
    hNupper hMupper
  have hblock := hledgerP b hPb
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        (3 * Real.log b) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) :=
      hraw
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
          (Real.log P) ^ (-S) := by
      rfl

/-- Fully explicit unequal Type II logarithmic-saving theorem. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_explicit_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (ha : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N M : ℝ),
        P ≤ (b : ℝ) → (b : ℝ) ≤ 2 * P → 0 < b →
        2 ≤ Real.log b → M ≠ 0 →
        (Real.log b) ^ (vaughanTypeIILogSavingPhaseExponent S) ≤
          reciprocalPhaseScale N M 2 (2 * (b : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
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
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_unequal
      hVinogradov hA hA₀ hε ha hAT hS hd hTdecay
  filter_upwards [hgeneral,
      eventually_ge_atTop (Real.exp 1)] with P hgeneralP hPlarge
  intro a b N M hPb hbP hb hlog hM hFhigh hNupper hMupper
  have hPpos : 0 < P := (Real.exp_pos 1).trans_le hPlarge
  have hlogPpos : 0 < Real.log P :=
    (Real.log_exp 1 ▸ show (0 : ℝ) < 1 by norm_num) |>.trans_le
      (Real.log_le_log (Real.exp_pos 1) hPlarge)
  have hbound := hgeneralP a b N M hPb hbP hb hlog hM hd0 hFhigh
    hNupper hMupper
  rw [Real.rpow_neg hlogPpos.le] at hbound
  simpa only [div_eq_mul_inv, mul_assoc] using hbound

end

end Tao2026
