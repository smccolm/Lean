import Tao2026.BadIntervalLargePrimeAdaptiveBlockSum

/-!
# Burgess insertion for adaptive large-prime blocks

This module composes the adaptive endpoint and common-factor estimates with
the exact dyadic finsets consumed by Propositions 6.7 and 6.8.  The only
remaining geometric hypotheses are the literal square-root conductor ranges
required by the explicit Burgess theorem.
-/

namespace Tao2026

open Filter Topology
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- Burgess bounds the exact exceptional endpoint finset appearing in the
adaptive one-band consumer. -/
theorem exists_eventually_card_taoLargePrimeAdaptiveDyadicExceptional_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hD : ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      IsAdmissibleTaoExceptionalConductorSet
        (taoDyadicPrimeBand (R x)) (P x j)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      (((taoDyadicPrimeBand (R x)).filter fun p =>
        p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
          (taoDyadicPrimeBand (R x)) (P x) (R x)).card : ℝ) ≤
        K * (R x : ℝ) ^ (1 / 50 : ℝ) := by
  obtain ⟨K, hK, hcard⟩ :=
    exists_eventually_card_taoLargePrimeAdaptiveExceptionalConductorsFor_le_of_explicitBurgess
      hC hburgess hscale hR (fun x => taoDyadicPrimeBand (R x)) hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcard] with x hcardX
  calc
    (((taoDyadicPrimeBand (R x)).filter fun p =>
        p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
          (taoDyadicPrimeBand (R x)) (P x) (R x)).card : ℝ) ≤
      ((taoLargePrimeAdaptiveExceptionalConductorsFor
        (taoDyadicPrimeBand (R x)) (P x) (R x)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (by
          intro p hp
          exact (Finset.mem_filter.mp hp).2)
    _ ≤ K * (R x : ℝ) ^ (1 / 50 : ℝ) := hcardX

/-- Burgess bounds the exact mixed adaptive exceptional-pair finset by the
source shape `R^0.02 · #band(S) + #band(R) · S^0.02`. -/
theorem exists_eventually_card_taoLargePrimeAdaptiveExceptionalModuliPairs_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S)
    (lowerPrime upperPrime : ℕ → ℕ)
    (hD : ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      IsAdmissibleTaoExceptionalConductorSet
        (taoLargeAntiSievePrimeRange (lowerPrime x) (upperPrime x))
        (P x j))
    (hBandR : ∀ᶠ x : ℕ in atTop,
      taoDyadicPrimeBand (R x) ⊆
        taoLargeAntiSievePrimeRange (lowerPrime x) (upperPrime x))
    (hBandS : ∀ᶠ x : ℕ in atTop,
      taoDyadicPrimeBand (S x) ⊆
        taoLargeAntiSievePrimeRange (lowerPrime x) (upperPrime x))
    (hPartnerRange : ∀ᶠ x : ℕ in atTop,
      ∀ p ∈ taoDyadicPrimeBand (R x), ∀ j : Fin 1001,
        (upperPrime x : ℝ) ≤
          Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ((taoLargePrimeAdaptiveExceptionalModuliPairs
        (P x) (R x) (S x)).card : ℝ) ≤
        K * ((R x : ℝ) ^ (1 / 50 : ℝ) *
            ((taoDyadicPrimeBand (S x)).card : ℝ) +
          ((taoDyadicPrimeBand (R x)).card : ℝ) *
            (S x : ℝ) ^ (1 / 50 : ℝ)) := by
  let D : ℕ → Finset ℕ := fun x =>
    taoLargeAntiSievePrimeRange (lowerPrime x) (upperPrime x)
  obtain ⟨K₁, hK₁, hEndpointR⟩ :=
    exists_eventually_card_taoLargePrimeAdaptiveExceptionalConductorsFor_le_of_explicitBurgess
      hC hburgess hscale hR D (by simpa only [D] using hD)
  obtain ⟨K₂, hK₂, hEndpointS⟩ :=
    exists_eventually_card_taoLargePrimeAdaptiveExceptionalConductorsFor_le_of_explicitBurgess
      hC hburgess hscale hS D (by simpa only [D] using hD)
  obtain ⟨K₃, hK₃, hPartners⟩ :=
    exists_eventually_card_taoLargePrimeAdaptiveExceptionalPartnersFor_le_of_explicitBurgess
      hC hburgess hscale hS
  let K : ℝ := K₁ + K₂ + K₃
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hEndpointR, hEndpointS, hPartners, hBandR, hBandS,
    hPartnerRange] with x hEndpointRX hEndpointSX hPartnersX
      hBandRX hBandSX hPartnerRangeX
  have hA₁ : (((taoDyadicPrimeBand (R x)).filter fun p =>
      p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
        (D x) (P x) (R x)).card : ℝ) ≤
      K₁ * (R x : ℝ) ^ (1 / 50 : ℝ) := by
    calc
      (((taoDyadicPrimeBand (R x)).filter fun p =>
          p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
            (D x) (P x) (R x)).card : ℝ) ≤
        ((taoLargePrimeAdaptiveExceptionalConductorsFor
          (D x) (P x) (R x)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (by
              intro p hp
              exact (Finset.mem_filter.mp hp).2)
      _ ≤ K₁ * (R x : ℝ) ^ (1 / 50 : ℝ) := hEndpointRX
  have hA₂ : (((taoDyadicPrimeBand (S x)).filter fun q =>
      q ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
        (D x) (P x) (S x)).card : ℝ) ≤
      K₂ * (S x : ℝ) ^ (1 / 50 : ℝ) := by
    calc
      (((taoDyadicPrimeBand (S x)).filter fun q =>
          q ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
            (D x) (P x) (S x)).card : ℝ) ≤
        ((taoLargePrimeAdaptiveExceptionalConductorsFor
          (D x) (P x) (S x)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (by
              intro q hq
              exact (Finset.mem_filter.mp hq).2)
      _ ≤ K₂ * (S x : ℝ) ^ (1 / 50 : ℝ) := hEndpointSX
  have hB : ∀ p ∈ taoDyadicPrimeBand (R x),
      (((taoDyadicPrimeBand (S x)).filter fun q =>
        q ∈ taoLargePrimeAdaptiveExceptionalPartnersFor p
          (lowerPrime x) (upperPrime x) (P x) (S x)).card : ℝ) ≤
      K₃ * (S x : ℝ) ^ (1 / 50 : ℝ) := by
    intro p hp
    calc
      (((taoDyadicPrimeBand (S x)).filter fun q =>
          q ∈ taoLargePrimeAdaptiveExceptionalPartnersFor p
            (lowerPrime x) (upperPrime x) (P x) (S x)).card : ℝ) ≤
        ((taoLargePrimeAdaptiveExceptionalPartnersFor p
          (lowerPrime x) (upperPrime x) (P x) (S x)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (by
              intro q hq
              exact (Finset.mem_filter.mp hq).2)
      _ ≤ K₃ * (S x : ℝ) ^ (1 / 50 : ℝ) :=
        hPartnersX p (lowerPrime x) (upperPrime x)
          (mem_taoDyadicPrimeBand.mp hp).1 (hPartnerRangeX p hp)
  have hpair := card_taoLargePrimeAdaptiveExceptionalModuliPairs_cast_le
    (P x) (R x) (S x) (lowerPrime x) (upperPrime x)
      hBandRX hBandSX
      (K₁ * (R x : ℝ) ^ (1 / 50 : ℝ))
      (K₂ * (S x : ℝ) ^ (1 / 50 : ℝ))
      (K₃ * (S x : ℝ) ^ (1 / 50 : ℝ)) hA₁ hA₂ hB
  let U : ℝ := (R x : ℝ) ^ (1 / 50 : ℝ) *
    ((taoDyadicPrimeBand (S x)).card : ℝ)
  let V : ℝ := ((taoDyadicPrimeBand (R x)).card : ℝ) *
    (S x : ℝ) ^ (1 / 50 : ℝ)
  have hUNonneg : 0 ≤ U := by dsimp [U]; positivity
  have hVNonneg : 0 ≤ V := by dsimp [V]; positivity
  have hK₁K : K₁ ≤ K := by dsimp [K]; linarith
  have hK₂K₃K : K₂ + K₃ ≤ K := by dsimp [K]; linarith
  calc
    ((taoLargePrimeAdaptiveExceptionalModuliPairs
        (P x) (R x) (S x)).card : ℝ) ≤
      K₁ * U + K₂ * V + K₃ * V := by
        dsimp only [D, U, V]
        (convert hpair using 1; ring)
    _ = K₁ * U + (K₂ + K₃) * V := by ring
    _ ≤ K * U + K * V :=
      add_le_add (mul_le_mul_of_nonneg_right hK₁K hUNonneg)
        (mul_le_mul_of_nonneg_right hK₂K₃K hVNonneg)
    _ = K * (U + V) := by ring
    _ = K * ((R x : ℝ) ^ (1 / 50 : ℝ) *
            ((taoDyadicPrimeBand (S x)).card : ℝ) +
          ((taoDyadicPrimeBand (R x)).card : ℝ) *
            (S x : ℝ) ^ (1 / 50 : ℝ)) := by rfl

/-! ## Source-normalized block consumers -/

/-- The adaptive endpoint cardinality and improved source error inserted into
the complete finite one-band probability sum. -/
theorem exists_eventually_sum_taoLargePrimeProbability_adaptive_dyadicBlock_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (H m' : ℕ → ℕ) (B : ℕ → ℝ)
    (hD : ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      IsAdmissibleTaoExceptionalConductorSet
        (taoDyadicPrimeBand (R x)) (P x j))
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ R x - 1)
    (hB : ∀ᶠ x : ℕ in atTop, 0 ≤ B x)
    (hExceptional : ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ a ∈ taoLargeAntiSieveIndices
        (R x - 1) (2 * R x - 1) (H x),
      a.2 ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
        (taoDyadicPrimeBand (R x)) (P x) (R x) →
      taoLargePrimeProbability (P x) hP (m' x) a ≤ B x) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
        (R x - 1) (2 * R x - 1) (H x),
        taoLargePrimeProbability (P x) hP (m' x) a) ≤
        (H x - 1 : ℕ) *
          (((taoDyadicPrimeBand (R x)).card : ℝ) *
              (2 / (R x : ℝ) +
                1003 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ))) +
            (K * (R x : ℝ) ^ (1 / 50 : ℝ)) * B x) := by
  obtain ⟨K, hK, hcard⟩ :=
    exists_eventually_card_taoLargePrimeAdaptiveDyadicExceptional_le_of_explicitBurgess
      hC hburgess hscale hR hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcard,
    eventually_taoLargePrimeAdaptiveImprovedError_le_sourcePower hscale hR,
    hR.eventually_two_le, hH, hB, hExceptional] with
      x hcardX herrorX hRtwo hHX hBX hExceptionalX
  intro hP
  exact sum_taoLargePrimeProbability_adaptive_dyadicBlock_le
    (P x) hP (R x) (H x) (m' x) hRtwo hHX
      (1003 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ))) (B x)
      (K * (R x : ℝ) ^ (1 / 50 : ℝ))
      (by positivity) hBX
      (fun p hp => herrorX p hp) hcardX
      (fun a ha haE => hExceptionalX hP a ha haE)

/-- The mixed adaptive pair cardinality and covariance source error inserted
into the complete finite two-band covariance sum. -/
theorem exists_eventually_sum_taoLargePrimeCovariance_adaptive_twoBand_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S)
    (hRS : ∀ᶠ x : ℕ in atTop, R x ≤ S x)
    (lowerPrime upperPrime H m' : ℕ → ℕ) (B : ℕ → ℝ)
    (hD : ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      IsAdmissibleTaoExceptionalConductorSet
        (taoLargeAntiSievePrimeRange (lowerPrime x) (upperPrime x))
        (P x j))
    (hBandR : ∀ᶠ x : ℕ in atTop,
      taoDyadicPrimeBand (R x) ⊆
        taoLargeAntiSievePrimeRange (lowerPrime x) (upperPrime x))
    (hBandS : ∀ᶠ x : ℕ in atTop,
      taoDyadicPrimeBand (S x) ⊆
        taoLargeAntiSievePrimeRange (lowerPrime x) (upperPrime x))
    (hPartnerRange : ∀ᶠ x : ℕ in atTop,
      ∀ p ∈ taoDyadicPrimeBand (R x), ∀ j : Fin 1001,
        (upperPrime x : ℝ) ≤
          Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ)))
    (hHR : ∀ᶠ x : ℕ in atTop, H x ≤ R x - 1)
    (hHS : ∀ᶠ x : ℕ in atTop, H x ≤ S x - 1)
    (hB : ∀ᶠ x : ℕ in atTop, 0 ≤ B x)
    (hExceptional : ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ a ∈ taoLargeAntiSieveIndices
        (R x - 1) (2 * R x - 1) (H x),
      ∀ b ∈ (taoLargeAntiSieveIndices
        (S x - 1) (2 * S x - 1) (H x)).filter
          (fun b => b.2 ≠ a.2),
      ¬TaoLargePrimeAdaptivePairUnexceptional
        (P x) (R x) (S x) a b →
      taoLargePrimeJointProbability (P x) hP (m' x) a b ≤ B x) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
          (R x - 1) (2 * R x - 1) (H x),
        ∑ b ∈ (taoLargeAntiSieveIndices
          (S x - 1) (2 * S x - 1) (H x)).filter
            (fun b => b.2 ≠ a.2),
          taoLargePrimeCovariance (P x) hP (m' x) a b) ≤
        ((H x - 1 : ℕ) : ℝ) ^ 2 *
          (((taoDyadicPrimeBand (R x)).card : ℝ) *
              ((taoDyadicPrimeBand (S x)).card : ℝ) *
              (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
                (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
                (S x : ℝ) ^ (-(1 : ℝ))) +
            (K * ((R x : ℝ) ^ (1 / 50 : ℝ) *
                ((taoDyadicPrimeBand (S x)).card : ℝ) +
              ((taoDyadicPrimeBand (R x)).card : ℝ) *
                (S x : ℝ) ^ (1 / 50 : ℝ))) * B x) := by
  obtain ⟨K, hK, hcard⟩ :=
    exists_eventually_card_taoLargePrimeAdaptiveExceptionalModuliPairs_le_of_explicitBurgess
      hC hburgess hscale hR hS lowerPrime upperPrime hD
        hBandR hBandS hPartnerRange
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcard,
    eventually_taoLargePrimeMixedAdaptiveCovarianceImprovedError_le_sourcePower
      hscale hR hS hRS,
    hR.eventually_two_le, hS.eventually_two_le, hHR, hHS,
    hB, hExceptional] with
      x hcardX herrorX hRtwo hStwo hHRX hHSX hBX hExceptionalX
  intro hP
  exact sum_taoLargePrimeCovariance_adaptive_twoBand_le
    (P x) hP (R x) (S x) (H x) (m' x) hRtwo hStwo hHRX hHSX
      (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
        (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S x : ℝ) ^ (-(1 : ℝ)))
      (B x)
      (K * ((R x : ℝ) ^ (1 / 50 : ℝ) *
          ((taoDyadicPrimeBand (S x)).card : ℝ) +
        ((taoDyadicPrimeBand (R x)).card : ℝ) *
          (S x : ℝ) ^ (1 / 50 : ℝ)))
      (by
        unfold taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant
        unfold taoLargePrimeMixedAdaptiveSourceJointPowerConstant
        unfold taoLargePrimeSourceJointPowerConstant
        positivity)
      hBX (fun p hp q hq hpq _hpair => herrorX p q hp hq hpq)
      hcardX (fun a ha b hb hbad => hExceptionalX hP a ha b hb hbad)

end

end Tao2026
