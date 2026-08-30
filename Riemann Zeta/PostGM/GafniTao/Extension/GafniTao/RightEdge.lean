import GafniTao.NearOneInputs
import GafniTao.ExplicitFormulaSetup

/-!
# Right-edge zero sums

This module formalizes the first inequality in Gafni--Tao Lemma 2.1.  It
reduces the actual multiplicity-weighted short zero sum to the weighted zero
count `sum X^(beta-1)`.  The subsequent Stieltjes/partial-summation estimate
will consume the quantitative predicates from `NearOneInputs`.
-/

open Complex Finset MeasureTheory Set
open scoped BigOperators

namespace GafniTao

/-- The literal multiplicity-weighted right-edge quantity occurring after the
fundamental-theorem-of-calculus estimate in Lemma 2.1. -/
noncomputable def rightEdgeZeroWeight (eta₀ T X : ℝ) : ℝ :=
  ∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T,
    (zeroMultiplicity rho : ℝ) * X ^ (rho.re - 1)

/-- The cumulative multiplicity in the fixed right-edge rectangle whose
deficit `1-beta` is strictly below `eta`.  The strict inequality matches the
`Ioc` convention in the interval integral; changing it at finitely many
endpoints does not alter that integral. -/
noncomputable def rightEdgeCumulativeCount (eta₀ T eta : ℝ) : ℕ :=
  ∑ rho ∈
      (RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T).filter
        (fun rho => 1 - rho.re < eta),
    zeroMultiplicity rho

/-- Real-part bounds carried by membership in the actual frozen zero
rectangle. -/
theorem re_bounds_of_mem_rightEdgeZeros
    {eta₀ T : ℝ} {rho : ℂ}
    (hrho : rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      (1 - eta₀) 1 (-T) T) :
    1 - eta₀ ≤ rho.re ∧ rho.re ≤ 1 := by
  rw [RiemannZeta.GuthMaynard.zerosInRect, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, RiemannZeta.GuthMaynard.mem_ZeroRectangle] at hrho
  exact ⟨hrho.1.1, hrho.1.2.1⟩

/-- The cumulative right-edge count is bounded by the actual source count
`N(1-eta,T)`, with the same analytic multiplicities. -/
theorem rightEdgeCumulativeCount_le_zeroCount
    {eta₀ T eta : ℝ} :
    rightEdgeCumulativeCount eta₀ T eta ≤ zeroCount (1 - eta) T := by
  classical
  rw [rightEdgeCumulativeCount, zeroCount_eq_weighted_sum]
  apply Finset.sum_le_sum_of_subset
  intro rho hrho
  rw [Finset.mem_filter] at hrho
  change rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta) 1 (-T) T
  rw [RiemannZeta.GuthMaynard.zerosInRect, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, RiemannZeta.GuthMaynard.mem_ZeroRectangle] at hrho ⊢
  exact ⟨⟨by linarith, hrho.1.1.2.1, hrho.1.1.2.2.1,
    hrho.1.1.2.2.2⟩, hrho.1.2⟩

/-- Vanishing of the actual source count forces vanishing of the cumulative
right-edge subcount. -/
theorem rightEdgeCumulativeCount_eq_zero_of_zeroCount_eq_zero
    {eta₀ T eta : ℝ} (hzero : zeroCount (1 - eta) T = 0) :
    rightEdgeCumulativeCount eta₀ T eta = 0 := by
  exact Nat.eq_zero_of_le_zero
    ((rightEdgeCumulativeCount_le_zeroCount (eta₀ := eta₀) (T := T)
      (eta := eta)).trans_eq hzero)

/-- On `[X,2X]`, a critical-strip power is bounded by the source weight with
an explicit harmless factor `2`. -/
theorem rpow_le_two_mul_rightEdgeWeight
    {X x beta : ℝ} (hX : 1 ≤ X) (hxLower : X ≤ x) (hxUpper : x ≤ 2 * X)
    (hbetaLower : 0 ≤ beta) (hbetaUpper : beta ≤ 1) :
    x ^ beta ≤ 2 * X * X ^ (beta - 1) := by
  have hxNonneg : 0 ≤ x := (zero_le_one.trans hX).trans hxLower
  have htwoXNonneg : 0 ≤ 2 * X := by positivity
  have hbase : x ^ beta ≤ (2 * X) ^ beta :=
    Real.rpow_le_rpow hxNonneg hxUpper hbetaLower
  have hsplit : (2 * X) ^ beta = 2 ^ beta * X ^ beta := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (zero_le_one.trans hX)]
  have htwo : 2 ^ beta ≤ (2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      hbetaUpper
  have hXpowNonneg : 0 ≤ X ^ beta := Real.rpow_nonneg (zero_le_one.trans hX) beta
  have hXsplit : X ^ beta = X * X ^ (beta - 1) := by
    calc
      X ^ beta = X ^ (1 + (beta - 1)) := by congr 1; ring
      _ = X * X ^ (beta - 1) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hX), Real.rpow_one]
  calc
    x ^ beta ≤ (2 * X) ^ beta := hbase
    _ = 2 ^ beta * X ^ beta := hsplit
    _ ≤ 2 * X ^ beta := mul_le_mul_of_nonneg_right htwo hXpowNonneg
    _ = 2 * X * X ^ (beta - 1) := by
      rw [hXsplit]
      exact (mul_assoc 2 X (X ^ (beta - 1))).symm

/-- Exact layer-cake identity behind the paper's partial summation in the
real-part variable.  Here `d = 1-beta`; summing this identity over zeros and
interchanging the finite sum with the integral produces the cumulative counts
`N(1-eta,T)`. -/
theorem rpow_neg_eq_endpoint_add_integral
    {X d eta₀ : ℝ} (hX : 1 < X) :
    X ^ (-d) = X ^ (-eta₀) +
      ∫ eta : ℝ in d..eta₀, Real.log X * X ^ (-eta) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hderiv : ∀ eta : ℝ,
      HasDerivAt (fun u : ℝ => -X ^ (-u))
        (Real.log X * X ^ (-eta)) eta := by
    intro eta
    have hpow := (Real.hasStrictDerivAt_const_rpow hXpos (-eta)).hasDerivAt
      |>.comp eta (hasDerivAt_neg eta)
      |>.neg
    convert hpow using 1
    all_goals ring
  have hint : IntervalIntegrable
      (fun eta : ℝ => Real.log X * X ^ (-eta)) volume d eta₀ := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((Real.continuous_const_rpow hXpos.ne').comp continuous_neg)
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := d) (b := eta₀) (f := fun u : ℝ => -X ^ (-u))
    (f' := fun eta : ℝ => Real.log X * X ^ (-eta))
    (fun eta _ => hderiv eta) hint
  rw [hInt]
  ring

/-- An upper subinterval integral represented on one common interval.  This
is the measure-theoretic normalization needed before finite-sum/integral
interchange in the zero layer-cake formula. -/
theorem intervalIntegral_indicator_Ioc_upper
    {f : ℝ → ℝ} {d eta₀ : ℝ} (hd : d ∈ Icc 0 eta₀) :
    (∫ eta : ℝ in 0..eta₀, (Ioc d eta₀).indicator f eta) =
      ∫ eta : ℝ in d..eta₀, f eta := by
  rw [intervalIntegral.integral_of_le (hd.1.trans hd.2),
    intervalIntegral.integral_of_le hd.2,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  rw [show Ioc d eta₀ ∩ Ioc 0 eta₀ = Ioc d eta₀ by
    ext eta
    simp only [Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hdLower, hetaUpper⟩, _, _⟩
      exact ⟨hdLower, hetaUpper⟩
    · rintro ⟨hdLower, hetaUpper⟩
      exact ⟨⟨hdLower, hetaUpper⟩, hd.1.trans_lt hdLower, hetaUpper⟩]

/-- Exact finite layer-cake expansion of the right-edge weight.  This is the
pre-interchange version of the partial-summation line in Lemma 2.1 and already
identifies the endpoint term with the actual multiplicity-weighted zero
count. -/
theorem rightEdgeZeroWeight_eq_endpoint_add_sum_integrals
    {eta₀ T X : ℝ} (hX : 1 < X) :
    rightEdgeZeroWeight eta₀ T X =
      (zeroCount (1 - eta₀) T : ℝ) * X ^ (-eta₀) +
        ∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T,
          (zeroMultiplicity rho : ℝ) *
            (∫ eta : ℝ in (1 - rho.re)..eta₀,
              Real.log X * X ^ (-eta)) := by
  classical
  let Z := RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T
  have hcount :
      (zeroCount (1 - eta₀) T : ℝ) =
        ∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) := by
    rw [zeroCount_eq_weighted_sum]
    change (↑(∑ rho ∈ Z, zeroMultiplicity rho) : ℝ) = _
    norm_cast
  rw [rightEdgeZeroWeight]
  change (∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) * X ^ (rho.re - 1)) = _
  calc
    (∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) * X ^ (rho.re - 1)) =
        ∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) *
          (X ^ (-eta₀) +
            ∫ eta : ℝ in (1 - rho.re)..eta₀,
              Real.log X * X ^ (-eta)) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [show rho.re - 1 = -(1 - rho.re) by ring,
        rpow_neg_eq_endpoint_add_integral hX]
    _ = (∑ rho ∈ Z, (zeroMultiplicity rho : ℝ)) * X ^ (-eta₀) +
        ∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) *
          (∫ eta : ℝ in (1 - rho.re)..eta₀,
            Real.log X * X ^ (-eta)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ = (zeroCount (1 - eta₀) T : ℝ) * X ^ (-eta₀) +
        ∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) *
          (∫ eta : ℝ in (1 - rho.re)..eta₀,
            Real.log X * X ^ (-eta)) := by rw [hcount]

/-- The finite sum of upper-interval integrals is exactly the single
cumulative-count integral in Gafni--Tao's partial summation argument. -/
theorem rightEdge_sum_integrals_eq_cumulative_integral
    {eta₀ T X : ℝ} (heta₀Nonneg : 0 ≤ eta₀) (hX : 1 < X) :
    (∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T,
        (zeroMultiplicity rho : ℝ) *
          (∫ eta : ℝ in (1 - rho.re)..eta₀,
            Real.log X * X ^ (-eta))) =
      ∫ eta : ℝ in 0..eta₀,
        Real.log X * X ^ (-eta) *
          (rightEdgeCumulativeCount eta₀ T eta : ℝ) := by
  classical
  let Z := RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T
  let f : ℝ → ℝ := fun eta => Real.log X * X ^ (-eta)
  have hf : IntervalIntegrable f volume 0 eta₀ := by
    apply Continuous.intervalIntegrable
    dsimp [f]
    exact continuous_const.mul
      ((Real.continuous_const_rpow (zero_lt_one.trans hX).ne').comp continuous_neg)
  have hd (rho : ℂ) (hrho : rho ∈ Z) : 1 - rho.re ∈ Icc 0 eta₀ := by
    have hre := re_bounds_of_mem_rightEdgeZeros hrho
    exact ⟨by linarith, by linarith⟩
  have hIndicatorIntegrable (rho : ℂ) (hrho : rho ∈ Z) :
      IntervalIntegrable
        (fun eta => (zeroMultiplicity rho : ℝ) *
          (Ioc (1 - rho.re) eta₀).indicator f eta) volume 0 eta₀ := by
    apply IntervalIntegrable.const_mul _ (zeroMultiplicity rho : ℝ)
    constructor
    · exact hf.1.indicator measurableSet_Ioc
    · exact hf.2.indicator measurableSet_Ioc
  change (∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) *
      (∫ eta : ℝ in (1 - rho.re)..eta₀, f eta)) = _
  calc
    (∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) *
        (∫ eta : ℝ in (1 - rho.re)..eta₀, f eta)) =
      ∑ rho ∈ Z, ∫ eta : ℝ in 0..eta₀,
        (zeroMultiplicity rho : ℝ) *
          (Ioc (1 - rho.re) eta₀).indicator f eta := by
      apply Finset.sum_congr rfl
      intro rho hrho
      calc
        (zeroMultiplicity rho : ℝ) *
            (∫ eta : ℝ in (1 - rho.re)..eta₀, f eta) =
          (zeroMultiplicity rho : ℝ) *
            (∫ eta : ℝ in 0..eta₀,
              (Ioc (1 - rho.re) eta₀).indicator f eta) := by
                rw [intervalIntegral_indicator_Ioc_upper (hd rho hrho)]
        _ = ∫ eta : ℝ in 0..eta₀,
              (zeroMultiplicity rho : ℝ) *
                (Ioc (1 - rho.re) eta₀).indicator f eta := by
                rw [intervalIntegral.integral_const_mul]
    _ = ∫ eta : ℝ in 0..eta₀,
        ∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) *
          (Ioc (1 - rho.re) eta₀).indicator f eta := by
      rw [intervalIntegral.integral_finsetSum]
      exact fun rho hrho => hIndicatorIntegrable rho hrho
    _ = ∫ eta : ℝ in 0..eta₀,
        f eta * (rightEdgeCumulativeCount eta₀ T eta : ℝ) := by
      apply intervalIntegral.integral_congr
      intro eta heta
      rw [uIcc_of_le heta₀Nonneg] at heta
      change (∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) *
        (Ioc (1 - rho.re) eta₀).indicator f eta) =
        f eta * ↑(∑ rho ∈ Z.filter (fun rho => 1 - rho.re < eta),
          zeroMultiplicity rho)
      simp only [Nat.cast_sum, Finset.sum_filter]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      by_cases hdeficit : 1 - rho.re < eta
      · simp [Set.indicator, hdeficit, heta.2, mul_comm]
      · simp [Set.indicator, hdeficit]

/-- The literal cumulative-count integrand in the right-edge partial
summation formula is interval integrable.  This is recorded independently so
that subsequent estimates can use `intervalIntegral.integral_mono_on` without
silently assuming regularity of the step function. -/
theorem intervalIntegrable_rightEdgeCumulativeIntegrand
    {eta₀ T X : ℝ} (heta₀Nonneg : 0 ≤ eta₀) (hX : 1 < X) :
    IntervalIntegrable
      (fun eta : ℝ => Real.log X * X ^ (-eta) *
        (rightEdgeCumulativeCount eta₀ T eta : ℝ)) volume 0 eta₀ := by
  classical
  let Z := RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T
  let f : ℝ → ℝ := fun eta => Real.log X * X ^ (-eta)
  have hf : IntervalIntegrable f volume 0 eta₀ := by
    apply Continuous.intervalIntegrable
    dsimp [f]
    exact continuous_const.mul
      ((Real.continuous_const_rpow (zero_lt_one.trans hX).ne').comp continuous_neg)
  have hterm (rho : ℂ) : IntervalIntegrable
      (fun eta => (zeroMultiplicity rho : ℝ) *
        (Ioc (1 - rho.re) eta₀).indicator f eta) volume 0 eta₀ := by
    apply IntervalIntegrable.const_mul _ (zeroMultiplicity rho : ℝ)
    constructor
    · exact hf.1.indicator measurableSet_Ioc
    · exact hf.2.indicator measurableSet_Ioc
  have hsum : IntervalIntegrable
      (fun eta => ∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) *
        (Ioc (1 - rho.re) eta₀).indicator f eta) volume 0 eta₀ := by
    induction Z using Finset.induction_on with
    | empty =>
        simp
    | @insert rho Z hrho ih =>
        simp_rw [Finset.sum_insert hrho]
        exact (hterm rho).add ih
  apply hsum.congr
  intro eta heta
  rw [uIoc_of_le heta₀Nonneg] at heta
  change (∑ rho ∈ Z, (zeroMultiplicity rho : ℝ) *
      (Ioc (1 - rho.re) eta₀).indicator f eta) =
    f eta * ↑(∑ rho ∈ Z.filter (fun rho => 1 - rho.re < eta),
      zeroMultiplicity rho)
  simp only [Nat.cast_sum, Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hdeficit : 1 - rho.re < eta
  · simp [Set.indicator, hdeficit, heta.2, mul_comm]
  · simp [Set.indicator, hdeficit]

/-- There are no members of the cumulative right-edge set at a nonpositive
deficit.  This handles the endpoint `eta = 0`, where the source near-one
estimates are stated only for positive `eta`. -/
theorem rightEdgeCumulativeCount_eq_zero_of_nonpos
    {eta₀ T eta : ℝ} (heta : eta ≤ 0) :
    rightEdgeCumulativeCount eta₀ T eta = 0 := by
  classical
  rw [rightEdgeCumulativeCount]
  apply Finset.sum_eq_zero
  intro rho hrho
  rw [Finset.mem_filter] at hrho
  have hre := re_bounds_of_mem_rightEdgeZeros hrho.1
  exfalso
  linarith

/-- Pointwise half-saving for the actual cumulative right-edge count.  This
consumes both published near-one inputs through their exact count-level
interfaces and preserves analytic multiplicity. -/
theorem rightEdgeCumulativeCount_mul_rpow_neg_le
    {C B T₀ c T₁ q eta₀ eta T X : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hq : 0 < q)
    (hetaPos : 0 < eta) (hetaUpper : eta ≤ 1 / 2)
    (hetaSmall : eta ≤ (1 / (2 * q * C)) ^ (2 : ℕ))
    (hT₀ : T₀ ≤ T) (hT₁ : T₁ ≤ T) (hTone : 1 ≤ T)
    (hX : 1 ≤ X) (hTscale : T ≤ X ^ q) :
    (rightEdgeCumulativeCount eta₀ T eta : ℝ) * X ^ (-eta) ≤
      Real.log T ^ B * X ^ (-eta / 2) := by
  rcases nearOne_count_zero_or_half_decay hDensity hZeroFree hC hq
      hetaPos hetaUpper hetaSmall hT₀ hT₁ hTone hX hTscale with hzero | hdecay
  · rw [rightEdgeCumulativeCount_eq_zero_of_zeroCount_eq_zero
      (eta₀ := eta₀) hzero]
    simpa using mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hTone) B)
      (Real.rpow_nonneg (zero_le_one.trans hX) (-eta / 2))
  · calc
      (rightEdgeCumulativeCount eta₀ T eta : ℝ) * X ^ (-eta) ≤
          (zeroCount (1 - eta) T : ℝ) * X ^ (-eta) := by
        gcongr
        exact_mod_cast rightEdgeCumulativeCount_le_zeroCount
          (eta₀ := eta₀) (T := T) (eta := eta)
      _ ≤ Real.log T ^ B * X ^ (-eta / 2) := hdecay

/-- Below the literal Vinogradov--Korobov cutoff, the cumulative right-edge
count vanishes. -/
theorem rightEdgeCumulativeCount_eq_zero_of_vinogradovKorobov
    {c T₁ eta₀ eta T : ℝ}
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hetaPos : 0 < eta) (hT₁ : T₁ ≤ T)
    (hetaVK : eta ≤ c /
      (Real.log T ^ (2 / 3 : ℝ) *
        Real.log (Real.log T) ^ (1 / 3 : ℝ))) :
    rightEdgeCumulativeCount eta₀ T eta = 0 := by
  apply rightEdgeCumulativeCount_eq_zero_of_zeroCount_eq_zero
  exact hZeroFree hetaPos hT₁ hetaVK

/-- Closed form for the decaying comparison integral used after the
Vinogradov--Korobov split. -/
theorem integral_log_mul_rpow_neg_half
    {X L a b : ℝ} (hX : 1 < X) :
    (∫ eta : ℝ in a..b, Real.log X * (L * X ^ (-eta / 2))) =
      2 * L * (X ^ (-a / 2) - X ^ (-b / 2)) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hderiv : ∀ eta : ℝ,
      HasDerivAt (fun u : ℝ => -2 * L * X ^ (-u / 2))
        (Real.log X * (L * X ^ (-eta / 2))) eta := by
    intro eta
    have hinner : HasDerivAt (fun u : ℝ => -u / 2) (-1 / 2) eta := by
      exact (hasDerivAt_neg eta).div_const 2
    have hpow := (Real.hasStrictDerivAt_const_rpow hXpos (-eta / 2)).hasDerivAt
      |>.comp eta hinner
      |>.const_mul (-2 * L)
    convert hpow using 1
    ring
  have hint : IntervalIntegrable
      (fun eta : ℝ => Real.log X * (L * X ^ (-eta / 2))) volume a b := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (continuous_const.mul
      ((Real.continuous_const_rpow hXpos.ne').comp
        (continuous_neg.div_const 2)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun eta _ => hderiv eta) hint]
  ring

/-- The cumulative integral in the exact layer-cake formula has the
Vinogradov--Korobov subexponential cutoff and the near-one half-saving.  The
cut point `d` is required to be the literal source cutoff, not an unspecified
positive parameter. -/
theorem rightEdgeCumulativeIntegral_le_vinogradovKorobov_decay
    {C B T₀ c T₁ q eta₀ d T X : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hq : 0 < q)
    (hdPos : 0 < d) (hdUpper : d ≤ eta₀)
    (hdVK : d = c /
      (Real.log T ^ (2 / 3 : ℝ) *
        Real.log (Real.log T) ^ (1 / 3 : ℝ)))
    (heta₀Upper : eta₀ ≤ 1 / 2)
    (heta₀Small : eta₀ ≤ (1 / (2 * q * C)) ^ (2 : ℕ))
    (hT₀ : T₀ ≤ T) (hT₁ : T₁ ≤ T) (hTone : 1 ≤ T)
    (hX : 1 < X) (hTscale : T ≤ X ^ q) :
    (∫ eta : ℝ in 0..eta₀,
        Real.log X * X ^ (-eta) *
          (rightEdgeCumulativeCount eta₀ T eta : ℝ)) ≤
      2 * Real.log T ^ B * X ^ (-d / 2) := by
  let f : ℝ → ℝ := fun eta => Real.log X * X ^ (-eta) *
    (rightEdgeCumulativeCount eta₀ T eta : ℝ)
  let g : ℝ → ℝ := fun eta =>
    Real.log X * (Real.log T ^ B * X ^ (-eta / 2))
  have heta₀Nonneg : 0 ≤ eta₀ := hdPos.le.trans hdUpper
  have hdMem : d ∈ Icc 0 eta₀ := ⟨hdPos.le, hdUpper⟩
  have hf : IntervalIntegrable f volume 0 eta₀ := by
    exact intervalIntegrable_rightEdgeCumulativeIntegrand heta₀Nonneg hX
  have hf0d : IntervalIntegrable f volume 0 d :=
    hf.mono_set (uIcc_subset_uIcc_left (by
      rwa [uIcc_of_le heta₀Nonneg]))
  have hfdet : IntervalIntegrable f volume d eta₀ :=
    hf.mono_set (uIcc_subset_uIcc_right (by
      rwa [uIcc_of_le heta₀Nonneg]))
  have hgdet : IntervalIntegrable g volume d eta₀ := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    exact continuous_const.mul (continuous_const.mul
      ((Real.continuous_const_rpow (zero_lt_one.trans hX).ne').comp
        (continuous_neg.div_const 2)))
  have hzero : (∫ eta : ℝ in 0..d, f eta) = 0 := by
    calc
      (∫ eta : ℝ in 0..d, f eta) = ∫ _eta : ℝ in 0..d, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro eta heta
        rw [uIcc_of_le hdPos.le] at heta
        dsimp [f]
        by_cases hetaZero : eta = 0
        · rw [hetaZero, rightEdgeCumulativeCount_eq_zero_of_nonpos
            (eta₀ := eta₀) (T := T) (eta := 0) (by norm_num)]
          ring
        · have hetaPos : 0 < eta := lt_of_le_of_ne heta.1 (Ne.symm hetaZero)
          have hetaVK : eta ≤ c /
              (Real.log T ^ (2 / 3 : ℝ) *
                Real.log (Real.log T) ^ (1 / 3 : ℝ)) := by
            rw [← hdVK]
            exact heta.2
          rw [rightEdgeCumulativeCount_eq_zero_of_vinogradovKorobov
            hZeroFree hetaPos hT₁ hetaVK]
          ring
      _ = 0 := intervalIntegral.integral_zero
  have hmono : (∫ eta : ℝ in d..eta₀, f eta) ≤
      ∫ eta : ℝ in d..eta₀, g eta := by
    apply intervalIntegral.integral_mono_on hdUpper hfdet hgdet
    intro eta heta
    have hetaPos : 0 < eta := hdPos.trans_le heta.1
    have hetaUpper : eta ≤ 1 / 2 := heta.2.trans heta₀Upper
    have hetaSmall : eta ≤ (1 / (2 * q * C)) ^ (2 : ℕ) :=
      heta.2.trans heta₀Small
    have hdecay := rightEdgeCumulativeCount_mul_rpow_neg_le (eta₀ := eta₀)
      hDensity hZeroFree hC hq hetaPos hetaUpper hetaSmall hT₀ hT₁ hTone
        hX.le hTscale
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX.le
    dsimp [f, g]
    calc
      Real.log X * X ^ (-eta) *
          (rightEdgeCumulativeCount eta₀ T eta : ℝ) =
          Real.log X *
            ((rightEdgeCumulativeCount eta₀ T eta : ℝ) * X ^ (-eta)) := by
              ring
      _ ≤ Real.log X * (Real.log T ^ B * X ^ (-eta / 2)) := by
        gcongr
  have hcompare : (∫ eta : ℝ in d..eta₀, g eta) =
      2 * Real.log T ^ B *
        (X ^ (-d / 2) - X ^ (-eta₀ / 2)) := by
    dsimp [g]
    exact integral_log_mul_rpow_neg_half hX
  have htail : 2 * Real.log T ^ B *
      (X ^ (-d / 2) - X ^ (-eta₀ / 2)) ≤
      2 * Real.log T ^ B * X ^ (-d / 2) := by
    have hL : 0 ≤ Real.log T ^ B :=
      Real.rpow_nonneg (Real.log_nonneg hTone) B
    have hpow : 0 ≤ X ^ (-eta₀ / 2) :=
      Real.rpow_nonneg (zero_le_one.trans hX.le) (-eta₀ / 2)
    nlinarith
  calc
    (∫ eta : ℝ in 0..eta₀, f eta) =
        (∫ eta : ℝ in 0..d, f eta) + ∫ eta : ℝ in d..eta₀, f eta := by
      rw [intervalIntegral.integral_add_adjacent_intervals hf0d hfdet]
    _ = ∫ eta : ℝ in d..eta₀, f eta := by rw [hzero, zero_add]
    _ ≤ ∫ eta : ℝ in d..eta₀, g eta := hmono
    _ = 2 * Real.log T ^ B *
        (X ^ (-d / 2) - X ^ (-eta₀ / 2)) := hcompare
    _ ≤ 2 * Real.log T ^ B * X ^ (-d / 2) := htail

/-- Complete count-level partial-summation estimate for the right-edge zero
weight.  The factor `3` consists of one endpoint contribution and the exact
integrated factor `2`. -/
theorem rightEdgeZeroWeight_le_vinogradovKorobov_decay
    {C B T₀ c T₁ q eta₀ d T X : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hq : 0 < q)
    (hdPos : 0 < d) (hdUpper : d ≤ eta₀)
    (hdVK : d = c /
      (Real.log T ^ (2 / 3 : ℝ) *
        Real.log (Real.log T) ^ (1 / 3 : ℝ)))
    (heta₀Upper : eta₀ ≤ 1 / 2)
    (heta₀Small : eta₀ ≤ (1 / (2 * q * C)) ^ (2 : ℕ))
    (hT₀ : T₀ ≤ T) (hT₁ : T₁ ≤ T) (hTone : 1 ≤ T)
    (hX : 1 < X) (hTscale : T ≤ X ^ q) :
    rightEdgeZeroWeight eta₀ T X ≤
      3 * Real.log T ^ B * X ^ (-d / 2) := by
  have heta₀Pos : 0 < eta₀ := hdPos.trans_le hdUpper
  have hendpoint : (zeroCount (1 - eta₀) T : ℝ) * X ^ (-eta₀) ≤
      Real.log T ^ B * X ^ (-eta₀ / 2) := by
    rcases nearOne_count_zero_or_half_decay hDensity hZeroFree hC hq
        heta₀Pos heta₀Upper heta₀Small hT₀ hT₁ hTone hX.le hTscale with
      hzero | hdecay
    · rw [hzero]
      simpa using mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hTone) B)
        (Real.rpow_nonneg (zero_le_one.trans hX.le) (-eta₀ / 2))
    · exact hdecay
  have hintegral := rightEdgeCumulativeIntegral_le_vinogradovKorobov_decay
    hDensity hZeroFree hC hq hdPos hdUpper hdVK heta₀Upper heta₀Small
      hT₀ hT₁ hTone hX hTscale
  have hpow : X ^ (-eta₀ / 2) ≤ X ^ (-d / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    linarith
  have hL : 0 ≤ Real.log T ^ B :=
    Real.rpow_nonneg (Real.log_nonneg hTone) B
  rw [rightEdgeZeroWeight_eq_endpoint_add_sum_integrals hX,
    rightEdge_sum_integrals_eq_cumulative_integral heta₀Pos.le hX]
  calc
    (zeroCount (1 - eta₀) T : ℝ) * X ^ (-eta₀) +
        (∫ eta : ℝ in 0..eta₀,
          Real.log X * X ^ (-eta) *
            (rightEdgeCumulativeCount eta₀ T eta : ℝ)) ≤
      Real.log T ^ B * X ^ (-eta₀ / 2) +
        2 * Real.log T ^ B * X ^ (-d / 2) :=
          add_le_add hendpoint hintegral
    _ ≤ Real.log T ^ B * X ^ (-d / 2) +
        2 * Real.log T ^ B * X ^ (-d / 2) := by gcongr
    _ = 3 * Real.log T ^ B * X ^ (-d / 2) := by ring

/-- Complete exact partial-summation identity for the fixed right-edge
rectangle. -/
theorem rightEdgeZeroWeight_eq_endpoint_add_cumulative_integral
    {eta₀ T X : ℝ} (heta₀Nonneg : 0 ≤ eta₀) (hX : 1 < X) :
    rightEdgeZeroWeight eta₀ T X =
      (zeroCount (1 - eta₀) T : ℝ) * X ^ (-eta₀) +
        ∫ eta : ℝ in 0..eta₀,
          Real.log X * X ^ (-eta) *
            (rightEdgeCumulativeCount eta₀ T eta : ℝ) := by
  rw [rightEdgeZeroWeight_eq_endpoint_add_sum_integrals hX,
    rightEdge_sum_integrals_eq_cumulative_integral heta₀Nonneg hX]

/-- The exact first reduction in Lemma 2.1, including analytic
multiplicities, the physical interval, and the short-increment coefficient.
No zero-density input is used at this stage. -/
theorem norm_rightEdgeZeroSum_le_weight
    {eta₀ T tau X x : ℝ}
    (heta₀ : eta₀ < 1) (htau : 0 < tau)
    (hX : 1 ≤ X) (hxLower : X ≤ x) (hxUpper : x ≤ 2 * X) :
    ‖zeroStripIncrementSum (1 - eta₀) 1 T tau x‖ ≤
      (2 * X / tau) * rightEdgeZeroWeight eta₀ T X := by
  classical
  rw [zeroStripIncrementSum, rightEdgeZeroWeight]
  calc
    ‖∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T,
        (zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho‖ ≤
        ∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T,
          ‖(zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T,
          (zeroMultiplicity rho : ℝ) *
            ((2 * X / tau) * X ^ (rho.re - 1)) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hre := re_bounds_of_mem_rightEdgeZeros hrho
      have hreNonneg : 0 ≤ rho.re := by linarith
      have hrhoNe : rho ≠ 0 :=
        ne_zero_of_mem_zerosInRect_of_pos (by linarith) hrho
      have hxPos : 0 < x :=
        lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hX) hxLower
      rw [norm_mul, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        ‖zeroIncrementTerm tau x rho‖ ≤ x ^ rho.re / tau :=
          norm_zeroIncrementTerm_le htau hxPos hrhoNe hre.2
        _ ≤ (2 * X * X ^ (rho.re - 1)) / tau := by
          exact div_le_div_of_nonneg_right
            (rpow_le_two_mul_rightEdgeWeight hX hxLower hxUpper hreNonneg hre.2)
            htau.le
        _ = (2 * X / tau) * X ^ (rho.re - 1) := by ring
    _ = (2 * X / tau) *
        ∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta₀) 1 (-T) T,
          (zeroMultiplicity rho : ℝ) * X ^ (rho.re - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      ring

/-- Quantitative right-edge zero-sum bound in the exact variables of Lemma
2.1, prior only to the paper's physical `T=J log(X)^2 tau` scale comparison.
-/
theorem norm_rightEdgeZeroSum_le_vinogradovKorobov_decay
    {C B T₀ c T₁ q eta₀ d T tau X x : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hq : 0 < q)
    (hdPos : 0 < d) (hdUpper : d ≤ eta₀)
    (hdVK : d = c /
      (Real.log T ^ (2 / 3 : ℝ) *
        Real.log (Real.log T) ^ (1 / 3 : ℝ)))
    (heta₀Upper : eta₀ ≤ 1 / 2)
    (heta₀Small : eta₀ ≤ (1 / (2 * q * C)) ^ (2 : ℕ))
    (hT₀ : T₀ ≤ T) (hT₁ : T₁ ≤ T) (hTone : 1 ≤ T)
    (htau : 0 < tau) (hX : 1 < X) (hTscale : T ≤ X ^ q)
    (hxLower : X ≤ x) (hxUpper : x ≤ 2 * X) :
    ‖zeroStripIncrementSum (1 - eta₀) 1 T tau x‖ ≤
      (6 * X / tau) * Real.log T ^ B * X ^ (-d / 2) := by
  have hweight := rightEdgeZeroWeight_le_vinogradovKorobov_decay
    hDensity hZeroFree hC hq hdPos hdUpper hdVK heta₀Upper heta₀Small
      hT₀ hT₁ hTone hX hTscale
  have hfirst := norm_rightEdgeZeroSum_le_weight (T := T)
    (lt_of_le_of_lt heta₀Upper (by norm_num)) htau hX.le hxLower hxUpper
  have hcoef : 0 ≤ 2 * X / tau := by positivity
  calc
    ‖zeroStripIncrementSum (1 - eta₀) 1 T tau x‖ ≤
        (2 * X / tau) * rightEdgeZeroWeight eta₀ T X := hfirst
    _ ≤ (2 * X / tau) *
        (3 * Real.log T ^ B * X ^ (-d / 2)) := by gcongr
    _ = (6 * X / tau) * Real.log T ^ B * X ^ (-d / 2) := by ring

end GafniTao
