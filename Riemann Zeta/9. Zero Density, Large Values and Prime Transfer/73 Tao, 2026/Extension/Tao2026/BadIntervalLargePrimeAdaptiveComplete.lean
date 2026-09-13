import Tao2026.BadIntervalLargePrimeAdaptiveGeometry

/-!
# Complete source specialization of adaptive large-prime blocks

This module discharges the conductor geometry and crude exceptional estimates
in the adaptive block consumers.  Its conclusions retain only the genuine
source-scale hypotheses on the dyadic bands and the shift range.
-/

namespace Tao2026

open Filter Topology
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- Proposition 6.7's complete adaptive dyadic block: Burgess supplies the
exceptional count, the fixed coordinate scales supply the improved error, and
the uniform two-coordinate count supplies the crude exceptional bound. -/
theorem exists_eventually_sum_taoLargePrimeProbability_adaptive_sourceBlock_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R : ℕ → ℕ} (hR : TaoLargePrimeDyadicBandSelector R)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ R x - 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
        (R x - 1) (2 * R x - 1) (H x),
        taoLargePrimeProbability (P x) hP (m' x) a) ≤
        (H x - 1 : ℕ) *
          (((taoDyadicPrimeBand (R x)).card : ℝ) *
              (2 / (R x : ℝ) +
                1003 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ))) +
            (K * (R x : ℝ) ^ (1 / 50 : ℝ)) *
              (256 * Real.log (taoZ x) ^ 2 / (R x : ℝ))) := by
  have hgeom := eventually_taoLargePrimeAdaptive_commonRange_geometry
    hscale hR hR (Filter.Eventually.of_forall fun _ => le_rfl)
  have hD : ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      IsAdmissibleTaoExceptionalConductorSet
        (taoDyadicPrimeBand (R x)) (P x j) := by
    filter_upwards [hgeom] with x hx
    intro j
    have hambient := hx.1 j
    have hsubset := hx.2.1
    exact ⟨fun p hp => hambient.1 p (hsubset hp),
      fun p hp => hambient.2 p (hsubset hp)⟩
  have hB : ∀ᶠ x : ℕ in atTop,
      0 ≤ 256 * Real.log (taoZ x) ^ 2 / (R x : ℝ) := by
    filter_upwards [hR.eventually_two_le] with x hRtwo
    positivity
  have hcrude := eventually_taoLargePrimeProbability_le_crude_dyadicBand
    hscale hR m'
  have hExceptional : ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ a ∈ taoLargeAntiSieveIndices
        (R x - 1) (2 * R x - 1) (H x),
      a.2 ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
        (taoDyadicPrimeBand (R x)) (P x) (R x) →
      taoLargePrimeProbability (P x) hP (m' x) a ≤
        256 * Real.log (taoZ x) ^ 2 / (R x : ℝ) := by
    filter_upwards [hcrude, hR.eventually_two_le, hH] with
      x hcrudeX hRtwo hHX
    intro hP a ha _haExceptional
    have haData := mem_taoLargeAntiSieveIndices.mp ha
    have haBand : a.2 ∈ taoDyadicPrimeBand (R x) := by
      rw [← taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand
        (show 0 < R x by omega)]
      exact mem_taoLargeAntiSievePrimeRange.mpr haData.2.2
    have hshift : ¬a.2 ∣ a.1 := by
      exact Nat.not_dvd_of_pos_of_lt haData.1 (by omega)
    exact hcrudeX hP a haBand hshift
  exact exists_eventually_sum_taoLargePrimeProbability_adaptive_dyadicBlock_le_of_explicitBurgess
    hC hburgess hscale hR.toTaoLargePrimeSourceBandSelector H m'
      (fun x => 256 * Real.log (taoZ x) ^ 2 / (R x : ℝ))
      hD hH hB hExceptional

/-- Proposition 6.8's complete ordered two-band covariance block.  The
ambient range `(R-1,2S-1]`, its endpoint/cofactor Burgess geometry, and the
crude joint estimate are all inferred from the source selector contracts. -/
theorem exists_eventually_sum_taoLargePrimeCovariance_adaptive_sourceTwoBand_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeDyadicBandSelector R)
    (hS : TaoLargePrimeDyadicBandSelector S)
    (hRS : ∀ᶠ x : ℕ in atTop, R x ≤ S x)
    (H m' : ℕ → ℕ)
    (hHR : ∀ᶠ x : ℕ in atTop, H x ≤ R x - 1)
    (hHS : ∀ᶠ x : ℕ in atTop, H x ≤ S x - 1) :
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
                (S x : ℝ) ^ (1 / 50 : ℝ))) *
              (6144 * Real.log (taoZ x) ^ 3 /
                ((R x : ℝ) * (S x : ℝ)))) := by
  have hgeom := eventually_taoLargePrimeAdaptive_commonRange_geometry
    hscale hR hS hRS
  have hD : ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      IsAdmissibleTaoExceptionalConductorSet
        (taoLargeAntiSievePrimeRange (R x - 1) (2 * S x - 1))
        (P x j) := hgeom.mono fun _ hx => hx.1
  have hBandR : ∀ᶠ x : ℕ in atTop,
      taoDyadicPrimeBand (R x) ⊆
        taoLargeAntiSievePrimeRange (R x - 1) (2 * S x - 1) :=
    hgeom.mono fun _ hx => hx.2.1
  have hBandS : ∀ᶠ x : ℕ in atTop,
      taoDyadicPrimeBand (S x) ⊆
        taoLargeAntiSievePrimeRange (R x - 1) (2 * S x - 1) :=
    hgeom.mono fun _ hx => hx.2.2.1
  have hPartner : ∀ᶠ x : ℕ in atTop,
      ∀ p ∈ taoDyadicPrimeBand (R x), ∀ j : Fin 1001,
        (2 * S x - 1 : ℕ) ≤
          Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ)) :=
    hgeom.mono fun _ hx => hx.2.2.2
  have hB : ∀ᶠ x : ℕ in atTop,
      0 ≤ 6144 * Real.log (taoZ x) ^ 3 /
        ((R x : ℝ) * (S x : ℝ)) := by
    filter_upwards [hR.eventually_two_le, hS.eventually_two_le,
      tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
        x hRtwo hStwo hz
    exact div_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (Real.log_nonneg hz) 3))
      (mul_nonneg (by positivity) (by positivity))
  have hcrude := eventually_taoLargePrimeJointProbability_le_crude_twoBand
    hscale hR hS m'
  have hExceptional : ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ a ∈ taoLargeAntiSieveIndices
        (R x - 1) (2 * R x - 1) (H x),
      ∀ b ∈ (taoLargeAntiSieveIndices
        (S x - 1) (2 * S x - 1) (H x)).filter
          (fun b => b.2 ≠ a.2),
      ¬TaoLargePrimeAdaptivePairUnexceptional
        (P x) (R x) (S x) a b →
      taoLargePrimeJointProbability (P x) hP (m' x) a b ≤
        6144 * Real.log (taoZ x) ^ 3 /
          ((R x : ℝ) * (S x : ℝ)) := by
    filter_upwards [hcrude, hR.eventually_two_le, hS.eventually_two_le,
      hHR, hHS] with x hcrudeX hRtwo hStwo hHRX hHSX
    intro hP a ha b hb _hbad
    have haData := mem_taoLargeAntiSieveIndices.mp ha
    have hbMem := (Finset.mem_filter.mp hb).1
    have hbData := mem_taoLargeAntiSieveIndices.mp hbMem
    have haBand : a.2 ∈ taoDyadicPrimeBand (R x) := by
      rw [← taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand
        (show 0 < R x by omega)]
      exact mem_taoLargeAntiSievePrimeRange.mpr haData.2.2
    have hbBand : b.2 ∈ taoDyadicPrimeBand (S x) := by
      rw [← taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand
        (show 0 < S x by omega)]
      exact mem_taoLargeAntiSievePrimeRange.mpr hbData.2.2
    have hpq : a.2 ≠ b.2 := (Finset.mem_filter.mp hb).2.symm
    have hshiftA : ¬a.2 ∣ a.1 :=
      Nat.not_dvd_of_pos_of_lt haData.1 (by omega)
    have hshiftB : ¬b.2 ∣ b.1 :=
      Nat.not_dvd_of_pos_of_lt hbData.1 (by omega)
    exact hcrudeX hP a b haBand hbBand hpq hshiftA hshiftB
  exact exists_eventually_sum_taoLargePrimeCovariance_adaptive_twoBand_le_of_explicitBurgess
    hC hburgess hscale hR.toTaoLargePrimeSourceBandSelector
      hS.toTaoLargePrimeSourceBandSelector hRS
      (fun x => R x - 1) (fun x => 2 * S x - 1) H m'
      (fun x => 6144 * Real.log (taoZ x) ^ 3 /
        ((R x : ℝ) * (S x : ℝ)))
      hD hBandR hBandS hPartner hHR hHS hB hExceptional

end

end Tao2026
