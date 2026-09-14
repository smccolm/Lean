import Tao2026.BadIntervalBackwardLargePrimeAdaptiveUniform

/-!
# Backward typical intervals: probability normalization

This module converts the completed backward large-prime mean and variance
estimates into the one-sided source tail used by the anti-sieve.
-/

namespace Tao2026

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

noncomputable section

theorem taoBackwardLargePrimeContribution_nonneg
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    0 ≤ taoBackwardLargePrimeContribution lowerPrime upperPrime H m' ω := by
  exact Finset.sum_nonneg fun lp hlp =>
    taoBackwardPrimeDivisibilityIndicator_nonneg m' lp.1 lp.2 ω

theorem taoBackwardLargePrimeContribution_le_card
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    taoBackwardLargePrimeContribution lowerPrime upperPrime H m' ω ≤
      (taoLargeAntiSieveIndices lowerPrime upperPrime H).card := by
  unfold taoBackwardLargePrimeContribution
  calc
    (∑ lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω) ≤
      ∑ _lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro lp hlp
        exact taoBackwardPrimeDivisibilityIndicator_le_one m' lp.1 lp.2 ω
    _ = (taoLargeAntiSieveIndices lowerPrime upperPrime H).card := by simp

theorem memLp_taoBackwardLargePrimeContribution
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) (p : ENNReal) :
    MemLp (taoBackwardLargePrimeContribution lowerPrime upperPrime H m') p
      (taoPrimeTupleMeasure P hP) := by
  apply MemLp.of_bound
    (measurable_of_countable
      (taoBackwardLargePrimeContribution lowerPrime upperPrime H m')).aestronglyMeasurable
    ((taoLargeAntiSieveIndices lowerPrime upperPrime H).card : ℝ)
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (taoBackwardLargePrimeContribution_nonneg lowerPrime upperPrime H m' ω)]
    exact_mod_cast
      taoBackwardLargePrimeContribution_le_card lowerPrime upperPrime H m' ω

theorem variance_taoBackwardLargePrimeContribution_eq
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) :
    variance (taoBackwardLargePrimeContribution lowerPrime upperPrime H m')
        (taoPrimeTupleMeasure P hP) =
      taoBackwardLargePrimeVariance P hP lowerPrime upperPrime H m' := by
  rw [variance_eq_sub
    (memLp_taoBackwardLargePrimeContribution P hP lowerPrime upperPrime H m' 2)]
  rfl

theorem taoBackwardLargePrimeContribution_upperTail_measureReal_mul_sq_le_variance
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    T ^ (2 : ℕ) *
        (taoPrimeTupleMeasure P hP).real
          {ω | taoBackwardLargePrimeMean P hP lowerPrime upperPrime H m' + T ≤
            taoBackwardLargePrimeContribution lowerPrime upperPrime H m' ω} ≤
      taoBackwardLargePrimeVariance P hP lowerPrime upperPrime H m' := by
  let μ := taoPrimeTupleMeasure P hP
  let X : TaoPrimeTuple → ℝ :=
    taoBackwardLargePrimeContribution lowerPrime upperPrime H m'
  let M : ℝ := taoBackwardLargePrimeMean P hP lowerPrime upperPrime H m'
  have hX := memLp_taoBackwardLargePrimeContribution
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
        taoBackwardLargePrimeVariance P hP lowerPrime upperPrime H m' := by
    calc
      (∫ ω, (X ω - M) ^ (2 : ℕ) ∂μ) = variance X μ := by
        exact (variance_eq_integral hX.aemeasurable).symm
      _ = taoBackwardLargePrimeVariance P hP lowerPrime upperPrime H m' := by
        simpa only [X, μ] using variance_taoBackwardLargePrimeContribution_eq
          P hP lowerPrime upperPrime H m'
  calc
    T ^ (2 : ℕ) * μ.real {ω | M + T ≤ X ω} ≤
        T ^ (2 : ℕ) * μ.real
          {ω | T ^ (2 : ℕ) ≤ (X ω - M) ^ (2 : ℕ)} := by
      exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
        (sq_nonneg T)
    _ ≤ ∫ ω, (X ω - M) ^ (2 : ℕ) ∂μ := hmarkov
    _ = taoBackwardLargePrimeVariance P hP lowerPrime upperPrime H m' :=
      hvarianceIntegral

/-- At distance `H log(z)/(8 log₂ x)` above the backward source mean, the
large-prime tail has the source-normalized Chebyshev bound. -/
theorem eventually_taoBackwardLargePrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
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
            taoBackwardLargePrimeContribution
              (taoLargePrimeSourceLowerCutoff x)
              (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) ω} ≤
        2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
          ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  have hmean := eventually_taoBackwardLargePrimeMean_sourceCutoffs_le
    hC hburgess hscale H m' hH
  have hvariance := eventually_taoBackwardLargePrimeVariance_sourceCutoffs_le
    hC hburgess hscale H m' hH
  filter_upwards [hmean, hvariance, hHpos,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hmeanX hvarianceX hHx hz hiter
  let μ := taoPrimeTupleMeasure (P x) (hP x)
  let X : TaoPrimeTuple → ℝ := taoBackwardLargePrimeContribution
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) (H x) (m' x)
  let M : ℝ := taoBackwardLargePrimeMean (P x) (hP x)
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
    taoBackwardLargePrimeContribution_upperTail_measureReal_mul_sq_le_variance
      (P x) (hP x) (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) (H x) (m' x)
          (T := T) hTpos.le
  have htail : T ^ (2 : ℕ) * Q ≤ 2000001 * (H x : ℝ) := by
    calc
      T ^ (2 : ℕ) * Q ≤
          T ^ (2 : ℕ) * μ.real {ω | M + T ≤ X ω} := by
        exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
          (sq_nonneg T)
      _ ≤ taoBackwardLargePrimeVariance (P x) (hP x)
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

theorem eventually_forall_taoBackwardLargePrimeMean_sourceCutoffs_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      H ≤ taoTypicalLengthCutoff x →
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
        taoBackwardLargePrimeMean (P x) hP
            (taoLargePrimeSourceLowerCutoff x)
            (taoLargePrimeSourceUpperCutoff x) H m' ≤
          2000000 * (H : ℝ) := by
  let R : ℕ → (ℕ × ℕ) → Prop := fun x a =>
    a.1 ≤ taoTypicalLengthCutoff x
  let Q : ℕ → (ℕ × ℕ) → Prop := fun x a =>
    ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      taoBackwardLargePrimeMean (P x) hP
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) a.1 a.2 ≤
        2000000 * (a.1 : ℝ)
  have hne : ∀ᶠ x : ℕ in atTop, ∃ a : ℕ × ℕ, R x a :=
    Filter.Eventually.of_forall fun x => ⟨(0, 0), Nat.zero_le _⟩
  have hselector : ∀ f : ℕ → ℕ × ℕ,
      (∀ᶠ x : ℕ in atTop, R x (f x)) →
        ∀ᶠ x : ℕ in atTop, Q x (f x) := by
    intro f hf
    simpa only [R, Q] using
      eventually_taoBackwardLargePrimeMean_sourceCutoffs_le hC hburgess hscale
        (fun x => (f x).1) (fun x => (f x).2) hf
  have hu := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hu] with x hx H m' hHm
  exact hx (H, m') hHm

theorem eventually_forall_taoBackwardLargePrimeVariance_sourceCutoffs_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      H ≤ taoTypicalLengthCutoff x →
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
        taoBackwardLargePrimeVariance (P x) hP
            (taoLargePrimeSourceLowerCutoff x)
            (taoLargePrimeSourceUpperCutoff x) H m' ≤
          2000001 * (H : ℝ) := by
  let R : ℕ → (ℕ × ℕ) → Prop := fun x a =>
    a.1 ≤ taoTypicalLengthCutoff x
  let Q : ℕ → (ℕ × ℕ) → Prop := fun x a =>
    ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      taoBackwardLargePrimeVariance (P x) hP
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) a.1 a.2 ≤
        2000001 * (a.1 : ℝ)
  have hne : ∀ᶠ x : ℕ in atTop, ∃ a : ℕ × ℕ, R x a :=
    Filter.Eventually.of_forall fun x => ⟨(0, 0), Nat.zero_le _⟩
  have hselector : ∀ f : ℕ → ℕ × ℕ,
      (∀ᶠ x : ℕ in atTop, R x (f x)) →
        ∀ᶠ x : ℕ in atTop, Q x (f x) := by
    intro f hf
    simpa only [R, Q] using
      eventually_taoBackwardLargePrimeVariance_sourceCutoffs_le hC hburgess hscale
        (fun x => (f x).1) (fun x => (f x).2) hf
  have hu := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hu] with x hx H m' hHm
  exact hx (H, m') hHm

theorem eventually_forall_taoBackwardLargePrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | 2000000 * (H : ℝ) +
                (H : ℝ) * Real.log (taoZ x) /
                  (8 * iteratedLog x) <
            taoBackwardLargePrimeContribution
              (taoLargePrimeSourceLowerCutoff x)
              (taoLargePrimeSourceUpperCutoff x) H m' ω} ≤
        2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  have hmean := eventually_forall_taoBackwardLargePrimeMean_sourceCutoffs_le
    hC hburgess hscale
  have hvariance := eventually_forall_taoBackwardLargePrimeVariance_sourceCutoffs_le
    hC hburgess hscale
  filter_upwards [hmean, hvariance,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hmeanX hvarianceX hz hiter H m' hH hHcut
  let μ := taoPrimeTupleMeasure (P x) (hP x)
  let X : TaoPrimeTuple → ℝ := taoBackwardLargePrimeContribution
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) H m'
  let M : ℝ := taoBackwardLargePrimeMean (P x) (hP x)
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) H m'
  let L : ℝ := Real.log (taoZ x)
  let I : ℝ := iteratedLog x
  let T : ℝ := (H : ℝ) * L / (8 * I)
  let Q : ℝ := μ.real {ω | 2000000 * (H : ℝ) + T < X ω}
  have hLpos : 0 < L := by dsimp only [L]; exact Real.log_pos hz
  have hHrealPos : (0 : ℝ) < H := by exact_mod_cast hH
  have hIpos : 0 < I := by simpa only [I] using hiter
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hsubset :
      {ω | 2000000 * (H : ℝ) + T < X ω} ⊆
        {ω | M + T ≤ X ω} := by
    intro ω hω
    change 2000000 * (H : ℝ) + T < X ω at hω
    have hm := hmeanX H m' hHcut (hP x)
    change M ≤ 2000000 * (H : ℝ) at hm
    change M + T ≤ X ω
    linarith
  have hchebyshev :=
    taoBackwardLargePrimeContribution_upperTail_measureReal_mul_sq_le_variance
      (P x) (hP x) (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) H m' (T := T) hTpos.le
  have htail : T ^ (2 : ℕ) * Q ≤ 2000001 * (H : ℝ) := by
    calc
      T ^ (2 : ℕ) * Q ≤
          T ^ (2 : ℕ) * μ.real {ω | M + T ≤ X ω} := by
        exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
          (sq_nonneg T)
      _ ≤ taoBackwardLargePrimeVariance (P x) (hP x)
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) H m' := by
        simpa only [μ, X, M] using hchebyshev
      _ ≤ 2000001 * (H : ℝ) := hvarianceX H m' hHcut (hP x)
  have hQ : Q ≤ 2000001 * (H : ℝ) / T ^ (2 : ℕ) := by
    rw [le_div_iff₀ (pow_pos hTpos 2)]
    simpa only [mul_comm] using htail
  change Q ≤ 2000001 * (8 * I) ^ (2 : ℕ) /
    ((H : ℝ) * L ^ (2 : ℕ))
  calc
    Q ≤ 2000001 * (H : ℝ) / T ^ (2 : ℕ) := hQ
    _ = 2000001 * (8 * I) ^ (2 : ℕ) /
        ((H : ℝ) * L ^ (2 : ℕ)) := by
      dsimp only [T]
      field_simp [hHrealPos.ne', hLpos.ne', hIpos.ne']

end

end Tao2026
