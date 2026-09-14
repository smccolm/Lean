import Tao2026.SmallPrimeExceptionalConductors
import Tao2026.BadIntervalLargePrimeAdaptiveUniform

/-!
# Probability normalization for the Proposition 6.6 anti-sieve

This module converts the completed small-prime fiftieth moment and
large-prime variance estimates into literal tail-probability inequalities on
the finite independent-prime model.
-/

namespace Tao2026

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

/-- The fiftieth power of the small-prime contribution is integrable. -/
theorem integrable_taoSmallPrimeContribution_pow_fifty
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    Integrable (fun ω : TaoPrimeTuple =>
      (taoSmallPrimeContribution x H m' ω) ^ (50 : ℕ))
      (taoPrimeTupleMeasure P hP) := by
  rw [show (fun ω : TaoPrimeTuple =>
      (taoSmallPrimeContribution x H m' ω) ^ (50 : ℕ)) =
      fun ω => ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ j, Real.log (t j).2) *
          if TaoSmallPrimeJointDivisibilityEvent m' t ω then 1 else 0 by
    funext ω
    exact taoSmallPrimeContribution_pow_fifty x H m' ω]
  apply integrable_finsetSum
  intro t ht
  have hm : MeasurableSet {ω : TaoPrimeTuple |
      TaoSmallPrimeJointDivisibilityEvent m' t ω} :=
    (Set.to_countable _).measurableSet
  have hi : Integrable
      ({ω : TaoPrimeTuple |
        TaoSmallPrimeJointDivisibilityEvent m' t ω}.indicator
          (fun _ => (1 : ℝ))) (taoPrimeTupleMeasure P hP) :=
    (integrable_const (1 : ℝ)).indicator hm
  simpa only [Set.indicator, Set.mem_setOf_eq] using
    hi.const_mul (∏ j, Real.log (t j).2)

/-- Exact Markov inequality for the source small-prime contribution. -/
theorem taoSmallPrimeContribution_large_measureReal_mul_pow_fifty_le
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    T ^ (50 : ℕ) *
        (taoPrimeTupleMeasure P hP).real
          {ω | T < taoSmallPrimeContribution x H m' ω} ≤
      taoSmallPrimeFiftiethMoment P hP x H m' := by
  let μ := taoPrimeTupleMeasure P hP
  let X : TaoPrimeTuple → ℝ := fun ω =>
    taoSmallPrimeContribution x H m' ω
  have hnonneg : ∀ ω, 0 ≤ X ω := fun ω =>
    taoSmallPrimeContribution_nonneg x H m' ω
  have hsubset : {ω | T < X ω} ⊆ {ω | T ^ (50 : ℕ) ≤ (X ω) ^ (50 : ℕ)} := by
    intro ω hω
    exact pow_le_pow_left₀ hT (le_of_lt hω) 50
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => (X ω) ^ (50 : ℕ))
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hnonneg ω) 50)
      (by
        simpa only [μ, X] using
          integrable_taoSmallPrimeContribution_pow_fifty P hP x H m')
      (T ^ (50 : ℕ))
  calc
    T ^ (50 : ℕ) * μ.real {ω | T < X ω} ≤
        T ^ (50 : ℕ) * μ.real
          {ω | T ^ (50 : ℕ) ≤ (X ω) ^ (50 : ℕ)} := by
      exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
        (pow_nonneg hT 50)
    _ ≤ ∫ ω, (X ω) ^ (50 : ℕ) ∂μ := hmarkov
    _ = taoSmallPrimeFiftiethMoment P hP x H m' := by
      rfl

theorem taoLargePrimeContribution_nonneg
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    0 ≤ taoLargePrimeContribution lowerPrime upperPrime H m' ω := by
  exact Finset.sum_nonneg fun lp hlp =>
    taoPrimeDivisibilityIndicator_nonneg m' lp.1 lp.2 ω

theorem taoLargePrimeContribution_le_card
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    taoLargePrimeContribution lowerPrime upperPrime H m' ω ≤
      (taoLargeAntiSieveIndices lowerPrime upperPrime H).card := by
  unfold taoLargePrimeContribution
  calc
    (∑ lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        taoPrimeDivisibilityIndicator m' lp.1 lp.2 ω) ≤
      ∑ _lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro lp hlp
        exact taoPrimeDivisibilityIndicator_le_one m' lp.1 lp.2 ω
    _ = (taoLargeAntiSieveIndices lowerPrime upperPrime H).card := by simp

/-- The finite large-prime contribution belongs to every finite `L^p`. -/
theorem memLp_taoLargePrimeContribution
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) (p : ENNReal) :
    MemLp (taoLargePrimeContribution lowerPrime upperPrime H m') p
      (taoPrimeTupleMeasure P hP) := by
  apply MemLp.of_bound
    (measurable_of_countable
      (taoLargePrimeContribution lowerPrime upperPrime H m')).aestronglyMeasurable
    ((taoLargeAntiSieveIndices lowerPrime upperPrime H).card : ℝ)
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (taoLargePrimeContribution_nonneg lowerPrime upperPrime H m' ω)]
    exact_mod_cast
      taoLargePrimeContribution_le_card lowerPrime upperPrime H m' ω

/-- The project variance is exactly Mathlib's variance of the literal
large-prime contribution. -/
theorem variance_taoLargePrimeContribution_eq
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) :
    variance (taoLargePrimeContribution lowerPrime upperPrime H m')
        (taoPrimeTupleMeasure P hP) =
      taoLargePrimeVariance P hP lowerPrime upperPrime H m' := by
  rw [variance_eq_sub
    (memLp_taoLargePrimeContribution P hP lowerPrime upperPrime H m' 2)]
  rfl

/-- One-sided Chebyshev inequality centered at the exact large-prime mean. -/
theorem taoLargePrimeContribution_upperTail_measureReal_mul_sq_le_variance
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    T ^ (2 : ℕ) *
        (taoPrimeTupleMeasure P hP).real
          {ω | taoLargePrimeMean P hP lowerPrime upperPrime H m' + T ≤
            taoLargePrimeContribution lowerPrime upperPrime H m' ω} ≤
      taoLargePrimeVariance P hP lowerPrime upperPrime H m' := by
  let μ := taoPrimeTupleMeasure P hP
  let X : TaoPrimeTuple → ℝ :=
    taoLargePrimeContribution lowerPrime upperPrime H m'
  let M : ℝ := taoLargePrimeMean P hP lowerPrime upperPrime H m'
  have hX := memLp_taoLargePrimeContribution
    P hP lowerPrime upperPrime H m' 2
  have hcenterInt : Integrable (fun ω => (X ω - M) ^ (2 : ℕ)) μ := by
    have hcenter : MemLp (fun ω => X ω - M) 2 μ :=
      hX.sub (memLp_const M)
    exact hcenter.integrable_sq
  have hsubset : {ω | M + T ≤ X ω} ⊆
      {ω | T ^ (2 : ℕ) ≤ (X ω - M) ^ (2 : ℕ)} := by
    intro ω hω
    change M + T ≤ X ω at hω
    exact pow_le_pow_left₀ hT (by linarith) 2
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => (X ω - M) ^ (2 : ℕ))
      (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω - M))
      hcenterInt (T ^ (2 : ℕ))
  have hvarianceIntegral :
      (∫ ω, (X ω - M) ^ (2 : ℕ) ∂μ) =
        taoLargePrimeVariance P hP lowerPrime upperPrime H m' := by
    calc
      (∫ ω, (X ω - M) ^ (2 : ℕ) ∂μ) =
          variance X μ := by
        exact (variance_eq_integral hX.aemeasurable).symm
      _ = taoLargePrimeVariance P hP lowerPrime upperPrime H m' := by
        simpa only [X, μ] using variance_taoLargePrimeContribution_eq
          P hP lowerPrime upperPrime H m'
  calc
    T ^ (2 : ℕ) * μ.real {ω | M + T ≤ X ω} ≤
        T ^ (2 : ℕ) * μ.real
          {ω | T ^ (2 : ℕ) ≤ (X ω - M) ^ (2 : ℕ)} := by
      exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
        (sq_nonneg T)
    _ ≤ ∫ ω, (X ω - M) ^ (2 : ℕ) ∂μ := hmarkov
    _ = taoLargePrimeVariance P hP lowerPrime upperPrime H m' :=
      hvarianceIntegral

/-! ## Source logarithmic specializations -/

/-- Absolute constant in the elementary `H^50 log(z)^50` normalization of
the small-prime principal majorant. -/
def taoSmallPrimePrincipalLogPowerConstant : ℝ :=
  (2 : ℝ) ^ (50 : ℕ) * (50 : ℝ) ^ (51 : ℕ) * (10 : ℝ) ^ (50 : ℕ)

theorem taoSmallPrimePrincipalLogPowerConstant_pos :
    0 < taoSmallPrimePrincipalLogPowerConstant := by
  unfold taoSmallPrimePrincipalLogPowerConstant
  positivity

/-- The explicit Mertens majorant has precisely the source size
`O(H^50 log(z)^50)`. -/
theorem eventually_taoSmallPrimePrincipalMertensMajorant_le_logPower
    (H : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      taoSmallPrimePrincipalMertensMajorant x (H x) ≤
        taoSmallPrimePrincipalLogPowerConstant *
          (H x : ℝ) ^ (50 : ℕ) * Real.log (taoZ x) ^ (50 : ℕ) := by
  have hcutoff : ∀ᶠ x : ℕ in atTop,
      1 ≤ taoSmallAntiSievePrimeCutoff x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_ge_atTop 1)
  filter_upwards [hcutoff,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with
      x hcut hz
  let L : ℝ := Real.log (taoZ x)
  have hLone : 1 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hcutReal : (0 : ℝ) < taoSmallAntiSievePrimeCutoff x := by
    exact_mod_cast (zero_lt_one.trans_le hcut)
  have hcutLe : (taoSmallAntiSievePrimeCutoff x : ℝ) ≤ taoZ x := by
    calc
      (taoSmallAntiSievePrimeCutoff x : ℝ) ≤
          (taoZ x) ^ (1 / 100 : ℝ) :=
        Nat.floor_le (Real.rpow_nonneg (taoZ_pos x).le _)
      _ ≤ (taoZ x) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          ((Real.one_le_exp (by norm_num)).trans hz) (by norm_num)
      _ = taoZ x := Real.rpow_one _
  have hlogCut : Real.log (taoSmallAntiSievePrimeCutoff x : ℝ) ≤ L := by
    exact Real.log_le_log hcutReal hcutLe
  have hlogCutNonneg :
      0 ≤ Real.log (taoSmallAntiSievePrimeCutoff x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hcut)
  have hlogFour : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    exact h
  have hbracket :
      Real.log 4 *
            (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
          Real.log (taoSmallAntiSievePrimeCutoff x) ≤ 10 * L := by
    calc
      _ ≤ 3 * (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
          Real.log (taoSmallAntiSievePrimeCutoff x) := by
        gcongr
      _ ≤ 10 * L := by linarith
  have hbracketNonneg : 0 ≤
      Real.log 4 *
            (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
          Real.log (taoSmallAntiSievePrimeCutoff x) := by positivity
  rw [taoSmallPrimePrincipalMertensMajorant,
    taoSmallPrimePrincipalLogPowerConstant]
  calc
    (2 : ℝ) ^ (50 : ℕ) *
        ((H x : ℝ) ^ (50 : ℕ) *
          ((50 : ℝ) ^ (50 : ℕ) * 50 *
            (Real.log 4 *
                (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
              Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ))) ≤
      (2 : ℝ) ^ (50 : ℕ) *
        ((H x : ℝ) ^ (50 : ℕ) *
          ((50 : ℝ) ^ (50 : ℕ) * 50 *
            (10 * L) ^ (50 : ℕ))) := by
      gcongr
    _ = ((2 : ℝ) ^ (50 : ℕ) * (50 : ℝ) ^ (51 : ℕ) *
          (10 : ℝ) ^ (50 : ℕ)) *
        (H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ) := by ring

/-- The completed small-prime moment has source size
`O(H^50 log(z)^50)`, conditional only on explicit Burgess. -/
theorem exists_eventually_taoSmallPrimeFiftiethMoment_le_logPower_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop,
      taoSmallPrimeFiftiethMoment (P x) (hP x) x (H x) (m' x) ≤
        A * (H x : ℝ) ^ (50 : ℕ) *
          Real.log (taoZ x) ^ (50 : ℕ) := by
  have hscaleNat : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j := by
    filter_upwards
      [eventually_taoPrimeTupleSourceScale_lower_nine_tenths hscale] with
        x hx j
    have hfloor : (taoZPowerFloor (9 / 10 : ℝ) x : ℝ) ≤
        (taoZ x) ^ (9 / 10 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (taoZ_pos x).le _)
    exact_mod_cast hfloor.trans (hx j)
  obtain ⟨K, hK, hmoment⟩ :=
    exists_eventually_taoSmallPrimeFiftiethMoment_le_principalMajorant_of_explicitBurgess
      hC hburgess P hP H m' hscaleNat
  let A : ℝ := 1000 * (2 + K) * taoSmallPrimePrincipalLogPowerConstant
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos (by norm_num) (by linarith))
      taoSmallPrimePrincipalLogPowerConstant_pos
  refine ⟨A, hA, ?_⟩
  filter_upwards [hmoment,
    eventually_taoSmallPrimePrincipalMertensMajorant_le_logPower H] with
      x hmomentX hmajorantX
  calc
    taoSmallPrimeFiftiethMoment (P x) (hP x) x (H x) (m' x) ≤
        1000 * (2 + K) *
          taoSmallPrimePrincipalMertensMajorant x (H x) := hmomentX
    _ ≤ 1000 * (2 + K) *
        (taoSmallPrimePrincipalLogPowerConstant *
          (H x : ℝ) ^ (50 : ℕ) * Real.log (taoZ x) ^ (50 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hmajorantX (by positivity)
    _ = A * (H x : ℝ) ^ (50 : ℕ) *
        Real.log (taoZ x) ^ (50 : ℕ) := by
      dsimp only [A]
      ring

/-- Markov's inequality at the source threshold `H log(z)^2`: the
small-prime large-deviation probability is `O(log(z)^-50)`. -/
theorem exists_eventually_taoSmallPrimeContribution_large_measureReal_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | (H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) <
            taoSmallPrimeContribution x (H x) (m' x) ω} ≤
        A / Real.log (taoZ x) ^ (50 : ℕ) := by
  obtain ⟨A, hA, hmoment⟩ :=
    exists_eventually_taoSmallPrimeFiftiethMoment_le_logPower_of_explicitBurgess
      hC hburgess hscale hP H m'
  refine ⟨A, hA, ?_⟩
  filter_upwards [hmoment, hHpos,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with
      x hmomentX hHx hz
  let L : ℝ := Real.log (taoZ x)
  let T : ℝ := (H x : ℝ) * L ^ (2 : ℕ)
  let Q : ℝ := (taoPrimeTupleMeasure (P x) (hP x)).real
    {ω | T < taoSmallPrimeContribution x (H x) (m' x) ω}
  have hLone : 1 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hHrealPos : (0 : ℝ) < H x := by exact_mod_cast hHx
  have hmarkov :=
    taoSmallPrimeContribution_large_measureReal_mul_pow_fifty_le
      (P x) (hP x) x (H x) (m' x) (T := T) (by
        dsimp only [T]
        positivity)
  have htail : T ^ (50 : ℕ) * Q ≤
      A * (H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ) := by
    exact hmarkov.trans (by simpa only [Q, T, L] using hmomentX)
  have hfactorPos : 0 < (H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ) := by
    positivity
  have hcancel :
      ((H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ)) *
          (Q * L ^ (50 : ℕ)) ≤
        ((H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ)) * A := by
    calc
      _ = T ^ (50 : ℕ) * Q := by
        dsimp only [T]
        ring
      _ ≤ A * (H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ) := htail
      _ = ((H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ)) * A := by ring
  have hQ : Q * L ^ (50 : ℕ) ≤ A :=
    (mul_le_mul_iff_right₀ hfactorPos).mp hcancel
  change Q ≤ A / L ^ (50 : ℕ)
  exact (le_div_iff₀ (pow_pos hLpos 50)).2 hQ

/-- Chebyshev's inequality at distance `H log(z)` from the source mean: the
large-prime upper tail is `O(1/(H log(z)^2))`. -/
theorem eventually_taoLargePrimeContribution_large_measureReal_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | 2000000 * (H x : ℝ) +
              (H x : ℝ) * Real.log (taoZ x) <
            taoLargePrimeContribution
              (taoLargePrimeSourceLowerCutoff x)
              (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) ω} ≤
        2000001 /
          ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  have hmean := eventually_taoLargePrimeMean_sourceCutoffs_le
    hC hburgess hscale H m' hH
  have hvariance := eventually_taoLargePrimeVariance_sourceCutoffs_le
    hC hburgess hscale H m' hH
  filter_upwards [hmean, hvariance, hHpos,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with
      x hmeanX hvarianceX hHx hz
  let μ := taoPrimeTupleMeasure (P x) (hP x)
  let X : TaoPrimeTuple → ℝ := taoLargePrimeContribution
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) (H x) (m' x)
  let M : ℝ := taoLargePrimeMean (P x) (hP x)
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) (H x) (m' x)
  let L : ℝ := Real.log (taoZ x)
  let T : ℝ := (H x : ℝ) * L
  let Q : ℝ := μ.real
    {ω | 2000000 * (H x : ℝ) + T < X ω}
  have hLone : 1 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hHrealPos : (0 : ℝ) < H x := by exact_mod_cast hHx
  have hTnonneg : 0 ≤ T := by dsimp only [T]; positivity
  have hsubset :
      {ω | 2000000 * (H x : ℝ) + T < X ω} ⊆
        {ω | M + T ≤ X ω} := by
    intro ω hω
    change 2000000 * (H x : ℝ) + T < X ω at hω
    have hm := hmeanX (hP x)
    change M ≤ 2000000 * (H x : ℝ) at hm
    change M + T ≤ X ω
    linarith
  have hchebyshev :=
    taoLargePrimeContribution_upperTail_measureReal_mul_sq_le_variance
      (P x) (hP x) (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) (H x) (m' x)
          (T := T) hTnonneg
  have htail : T ^ (2 : ℕ) * Q ≤ 2000001 * (H x : ℝ) := by
    calc
      T ^ (2 : ℕ) * Q ≤
          T ^ (2 : ℕ) * μ.real {ω | M + T ≤ X ω} := by
        exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
          (sq_nonneg T)
      _ ≤ taoLargePrimeVariance (P x) (hP x)
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) := by
        simpa only [μ, X, M] using hchebyshev
      _ ≤ 2000001 * (H x : ℝ) := hvarianceX (hP x)
  have hdenomPos : 0 < (H x : ℝ) * L ^ (2 : ℕ) := by positivity
  have hcancel :
      (H x : ℝ) *
          (Q * ((H x : ℝ) * L ^ (2 : ℕ))) ≤
        (H x : ℝ) * 2000001 := by
    calc
      _ = T ^ (2 : ℕ) * Q := by
        dsimp only [T]
        ring
      _ ≤ 2000001 * (H x : ℝ) := htail
      _ = (H x : ℝ) * 2000001 := by ring
  have hQ : Q * ((H x : ℝ) * L ^ (2 : ℕ)) ≤ 2000001 :=
    (mul_le_mul_iff_right₀ hHrealPos).mp hcancel
  change Q ≤ 2000001 / ((H x : ℝ) * L ^ (2 : ℕ))
  exact (le_div_iff₀ hdenomPos).2 hQ

/-! ## Literal `log^(2-o(1))` thresholds -/

/-- At the source threshold `H log(z)^2 / (8 log₂(x))`, the small-prime tail is
bounded by the literal slowly varying loss
`log₂(x)^50 / log(z)^50`. -/
theorem exists_eventually_taoSmallPrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | (H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
                (8 * iteratedLog x) <
            taoSmallPrimeContribution x (H x) (m' x) ω} ≤
        A * (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (50 : ℕ) := by
  obtain ⟨A, hA, hmoment⟩ :=
    exists_eventually_taoSmallPrimeFiftiethMoment_le_logPower_of_explicitBurgess
      hC hburgess hscale hP H m'
  refine ⟨A, hA, ?_⟩
  filter_upwards [hmoment, hHpos,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hmomentX hHx hz hiter
  let L : ℝ := Real.log (taoZ x)
  let I : ℝ := iteratedLog x
  let T : ℝ := (H x : ℝ) * L ^ (2 : ℕ) / (8 * I)
  let Q : ℝ := (taoPrimeTupleMeasure (P x) (hP x)).real
    {ω | T < taoSmallPrimeContribution x (H x) (m' x) ω}
  have hLpos : 0 < L := by
    dsimp only [L]
    exact Real.log_pos hz
  have hHrealPos : (0 : ℝ) < H x := by exact_mod_cast hHx
  have hIpos : 0 < I := by simpa only [I] using hiter
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hmarkov :=
    taoSmallPrimeContribution_large_measureReal_mul_pow_fifty_le
      (P x) (hP x) x (H x) (m' x) (T := T) hTpos.le
  have htail : T ^ (50 : ℕ) * Q ≤
      A * (H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ) := by
    exact hmarkov.trans (by simpa only [Q, T, L] using hmomentX)
  have hQ : Q ≤
      (A * (H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ)) /
        T ^ (50 : ℕ) := by
    rw [le_div_iff₀ (pow_pos hTpos 50)]
    simpa only [mul_comm] using htail
  change Q ≤ A * (8 * I) ^ (50 : ℕ) / L ^ (50 : ℕ)
  calc
    Q ≤ (A * (H x : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ)) /
        T ^ (50 : ℕ) := hQ
    _ = A * (8 * I) ^ (50 : ℕ) / L ^ (50 : ℕ) := by
      dsimp only [T]
      field_simp [hHrealPos.ne', hLpos.ne', hIpos.ne']

/-- At distance `H log(z) / (8 log₂(x))` above the completed source mean, the
large-prime tail has the literal source shape
`log₂(x)^2 / (H log(z)^2)`. -/
theorem eventually_taoLargePrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | 2000000 * (H x : ℝ) +
                (H x : ℝ) * Real.log (taoZ x) /
                  (8 * iteratedLog x) <
            taoLargePrimeContribution
              (taoLargePrimeSourceLowerCutoff x)
              (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) ω} ≤
        2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
          ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  have hmean := eventually_taoLargePrimeMean_sourceCutoffs_le
    hC hburgess hscale H m' hH
  have hvariance := eventually_taoLargePrimeVariance_sourceCutoffs_le
    hC hburgess hscale H m' hH
  filter_upwards [hmean, hvariance, hHpos,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hmeanX hvarianceX hHx hz hiter
  let μ := taoPrimeTupleMeasure (P x) (hP x)
  let X : TaoPrimeTuple → ℝ := taoLargePrimeContribution
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) (H x) (m' x)
  let M : ℝ := taoLargePrimeMean (P x) (hP x)
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) (H x) (m' x)
  let L : ℝ := Real.log (taoZ x)
  let I : ℝ := iteratedLog x
  let T : ℝ := (H x : ℝ) * L / (8 * I)
  let Q : ℝ := μ.real {ω | 2000000 * (H x : ℝ) + T < X ω}
  have hLpos : 0 < L := by dsimp only [L]; exact Real.log_pos hz
  have hHrealPos : (0 : ℝ) < H x := by exact_mod_cast hHx
  have hIpos : 0 < I := by simpa only [I] using hiter
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hsubset :
      {ω | 2000000 * (H x : ℝ) + T < X ω} ⊆
        {ω | M + T ≤ X ω} := by
    intro ω hω
    change 2000000 * (H x : ℝ) + T < X ω at hω
    have hm := hmeanX (hP x)
    change M ≤ 2000000 * (H x : ℝ) at hm
    change M + T ≤ X ω
    linarith
  have hchebyshev :=
    taoLargePrimeContribution_upperTail_measureReal_mul_sq_le_variance
      (P x) (hP x) (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) (H x) (m' x)
          (T := T) hTpos.le
  have htail : T ^ (2 : ℕ) * Q ≤ 2000001 * (H x : ℝ) := by
    calc
      T ^ (2 : ℕ) * Q ≤
          T ^ (2 : ℕ) * μ.real {ω | M + T ≤ X ω} := by
        exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
          (sq_nonneg T)
      _ ≤ taoLargePrimeVariance (P x) (hP x)
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) := by
        simpa only [μ, X, M] using hchebyshev
      _ ≤ 2000001 * (H x : ℝ) := hvarianceX (hP x)
  have hQ : Q ≤ 2000001 * (H x : ℝ) / T ^ (2 : ℕ) := by
    rw [le_div_iff₀ (pow_pos hTpos 2)]
    simpa only [mul_comm] using htail
  change Q ≤ 2000001 * (8 * I) ^ (2 : ℕ) /
    ((H x : ℝ) * L ^ (2 : ℕ))
  calc
    Q ≤ 2000001 * (H x : ℝ) / T ^ (2 : ℕ) := hQ
    _ = 2000001 * (8 * I) ^ (2 : ℕ) /
        ((H x : ℝ) * L ^ (2 : ℕ)) := by
      dsimp only [T]
      field_simp [hHrealPos.ne', hLpos.ne', hIpos.ne']

/-- The exact three-branch large-deviation event used by the source
anti-sieve: the deterministic `p ∣ l` branch, the logarithmically weighted
small-prime branch, or the unweighted large-prime branch. -/
def TaoSourceAntiSieveLargeEvent
    (x H m' : ℕ) (ω : TaoPrimeTuple) : Prop :=
  TaoExceptionalPrimeLargeEvent x H m' ω ∨
    (H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
        (8 * iteratedLog x) <
      taoSmallPrimeContribution x H m' ω ∨
    2000000 * (H : ℝ) +
        (H : ℝ) * Real.log (taoZ x) / (8 * iteratedLog x) <
      taoLargePrimeContribution
        (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) H m' ω

/-- Union-bound closure of all three Proposition 6.6 anti-sieve branches.
The exceptional branch has zero mass, while the other two retain their
literal `log₂(x)` losses. -/
theorem exists_eventually_measureReal_taoSourceAntiSieveLargeEvent_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | TaoSourceAntiSieveLargeEvent x (H x) (m' x) ω} ≤
        A * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  obtain ⟨A, hA, hsmall⟩ :=
    exists_eventually_taoSmallPrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
      hC hburgess hscale hP H m' hHpos
  have hlarge :=
    eventually_taoLargePrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
      hC hburgess hscale hP H m' hH hHpos
  refine ⟨A, hA, ?_⟩
  filter_upwards [hsmall, hlarge,
    eventually_taoExceptionalPrimeLargeEvent_eq_empty, hH, hHpos] with
      x hsmallX hlargeX hexceptional hHx hHxPos
  let E : Set TaoPrimeTuple :=
    {ω | TaoExceptionalPrimeLargeEvent x (H x) (m' x) ω}
  let S : Set TaoPrimeTuple :=
    {ω | (H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
        (8 * iteratedLog x) <
      taoSmallPrimeContribution x (H x) (m' x) ω}
  let L : Set TaoPrimeTuple :=
    {ω | 2000000 * (H x : ℝ) +
          (H x : ℝ) * Real.log (taoZ x) / (8 * iteratedLog x) <
        taoLargePrimeContribution
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) ω}
  have hE : E = ∅ := by
    simpa only [E] using hexceptional (H x) (m' x) hHxPos hHx
  have hunion :
      {ω | TaoSourceAntiSieveLargeEvent x (H x) (m' x) ω} =
        (E ∪ S) ∪ L := by
    ext ω
    simp only [TaoSourceAntiSieveLargeEvent, E, S, L,
      Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hunion]
  calc
    (taoPrimeTupleMeasure (P x) (hP x)).real ((E ∪ S) ∪ L) ≤
        (taoPrimeTupleMeasure (P x) (hP x)).real (E ∪ S) +
          (taoPrimeTupleMeasure (P x) (hP x)).real L :=
      measureReal_union_le _ _
    _ ≤ ((taoPrimeTupleMeasure (P x) (hP x)).real E +
          (taoPrimeTupleMeasure (P x) (hP x)).real S) +
        (taoPrimeTupleMeasure (P x) (hP x)).real L := by
      gcongr
      exact measureReal_union_le _ _
    _ = (taoPrimeTupleMeasure (P x) (hP x)).real S +
        (taoPrimeTupleMeasure (P x) (hP x)).real L := by
      rw [hE]
      simp
    _ ≤ A * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
      exact add_le_add (by simpa only [S] using hsmallX)
        (by simpa only [L] using hlargeX)

end

end Tao2026
