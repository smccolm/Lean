import Tao2026.BadIntervalLargePrimeAdaptiveUniform
import Tao2026.BadIntervalBackwardLargePrimeAdaptiveBlockSum

/-!
# Backward typical intervals: uniform adaptive large-prime bounds

Reflection changes only the residue class, so the forward crude estimates and
adaptive exceptional-family bounds remain uniform for backward shifts.
-/

namespace Tao2026

open Filter
open scoped Classical Topology

noncomputable section

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

/-- Uniform crude one-prime estimate for every backward shift in a source
dyadic band. -/
theorem eventually_taoBackwardLargePrimeProbability_le_crude_dyadicBand
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R : ℕ → ℕ} (hR : TaoLargePrimeDyadicBandSelector R)
    (m' : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ a : ℕ × ℕ, a.2 ∈ taoDyadicPrimeBand (R x) →
        0 < a.1 → a.1 < a.2 →
        taoBackwardLargePrimeProbability (P x) hP (m' x) a ≤
          256 * Real.log (taoZ x) ^ 2 / (R x : ℝ) := by
  filter_upwards [eventually_taoLargePrimeProbability_le_crude_dyadicBand
    hscale hR m'] with x hx
  intro hP a ha hapos halt
  rw [taoBackwardLargePrimeProbability_eq_reflected
    (P x) hP (m' x) halt.le]
  exact hx hP (taoBackwardReflectedShift a)
    (by simpa only [taoBackwardReflectedShift_second] using ha)
    (taoBackwardReflectedShift_not_dvd hapos halt)

/-- Uniform crude two-prime estimate for every pair of backward shifts. -/
theorem eventually_taoBackwardLargePrimeJointProbability_le_crude_twoBand
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeDyadicBandSelector R)
    (hS : TaoLargePrimeDyadicBandSelector S) (m' : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ a b : ℕ × ℕ,
        a.2 ∈ taoDyadicPrimeBand (R x) →
        b.2 ∈ taoDyadicPrimeBand (S x) → a.2 ≠ b.2 →
        0 < a.1 → a.1 < a.2 → 0 < b.1 → b.1 < b.2 →
        taoBackwardLargePrimeJointProbability (P x) hP (m' x) a b ≤
          6144 * Real.log (taoZ x) ^ 3 /
            ((R x : ℝ) * (S x : ℝ)) := by
  filter_upwards [eventually_taoLargePrimeJointProbability_le_crude_twoBand
    hscale hR hS m'] with x hx
  intro hP a b ha hb hpq hapos halt hbpos hblt
  rw [taoBackwardLargePrimeJointProbability_eq_reflected
    (P x) hP (m' x) halt.le hblt.le]
  exact hx hP (taoBackwardReflectedShift a) (taoBackwardReflectedShift b)
    (by simpa only [taoBackwardReflectedShift_second] using ha)
    (by simpa only [taoBackwardReflectedShift_second] using hb)
    (by simpa only [taoBackwardReflectedShift_second] using hpq)
    (taoBackwardReflectedShift_not_dvd hapos halt)
    (taoBackwardReflectedShift_not_dvd hbpos hblt)

/-- The adaptive backward first-moment block holds simultaneously on every
retained source scale. -/
theorem exists_eventually_forall_sum_taoBackwardLargePrimeProbability_adaptive_sourceBlock_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
        (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
        taoBackwardLargePrimeProbability (P x) hP (m' x) a) ≤
        (H x - 1 : ℕ) *
          (((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
              (2 / ((2 ^ r : ℕ) : ℝ) +
                1003 * ((2 ^ r : ℕ) : ℝ) ^
                  (-(1001 / 1000 : ℝ))) +
            (K * ((2 ^ r : ℕ) : ℝ) ^ (1 / 50 : ℝ)) *
              (256 * Real.log (taoZ x) ^ 2 / ((2 ^ r : ℕ) : ℝ))) := by
  obtain ⟨K, hK, hcard⟩ :=
    exists_eventually_forall_card_taoLargePrimeAdaptiveExceptionalConductorsFor_le_of_explicitBurgess
      hC hburgess hscale
  let Rel : ℕ → ℕ → Prop := fun x r =>
    r ∈ taoLargePrimeSourceDyadicExponents x
  let Good : ℕ → ℕ → Prop := fun x r =>
    ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
        (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
        taoBackwardLargePrimeProbability (P x) hP (m' x) a) ≤
        (H x - 1 : ℕ) *
          (((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
              (2 / ((2 ^ r : ℕ) : ℝ) +
                1003 * ((2 ^ r : ℕ) : ℝ) ^
                  (-(1001 / 1000 : ℝ))) +
            (K * ((2 ^ r : ℕ) : ℝ) ^ (1 / 50 : ℝ)) *
              (256 * Real.log (taoZ x) ^ 2 / ((2 ^ r : ℕ) : ℝ)))
  have hne : ∀ᶠ x : ℕ in atTop, ∃ r, Rel x r :=
    eventually_taoLargePrimeSourceDyadicExponents_nonempty.mono fun x hx => by
      exact ⟨hx.choose, hx.choose_spec⟩
  have hselector : ∀ f : ℕ → ℕ,
      (∀ᶠ x : ℕ in atTop, Rel x (f x)) →
        ∀ᶠ x : ℕ in atTop, Good x (f x) := by
    intro f hf
    have hf' : ∀ᶠ x : ℕ in atTop,
        f x ∈ taoLargePrimeSourceDyadicExponents x := by
      simpa only [Rel] using hf
    let R : ℕ → ℕ := fun x => 2 ^ f x
    have hR : TaoLargePrimeDyadicBandSelector R :=
      taoLargePrimeDyadicBandSelector_of_eventually_mem_sourceDyadicExponents hf'
    have hgeom := eventually_taoLargePrimeAdaptive_commonRange_geometry
      hscale hR hR (Filter.Eventually.of_forall fun _ => le_rfl)
    have herror := eventually_taoLargePrimeAdaptiveImprovedError_le_sourcePower
      hscale hR.toTaoLargePrimeSourceBandSelector
    have hcrude := eventually_taoBackwardLargePrimeProbability_le_crude_dyadicBand
      hscale hR m'
    have hHscale : ∀ᶠ x : ℕ in atTop, H x ≤ R x - 1 := by
      filter_upwards
        [hH, eventually_taoTypicalLengthCutoff_le_sourceDyadicScale_sub_one,
          hf'] with x hHX hgrid hfX
      exact hHX.trans (hgrid (f x) hfX)
    filter_upwards [hcard, hgeom, herror, hcrude, hHscale,
      hR.eventually_two_le,
      tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
        x hcardX hgeomX herrorX hcrudeX hHscaleX hRtwo hz
    intro hP
    have hD : ∀ j : Fin 1001,
        IsAdmissibleTaoExceptionalConductorSet
          (taoDyadicPrimeBand (R x)) (P x j) := by
      intro j
      have hambient := hgeomX.1 j
      have hsubset := hgeomX.2.1
      exact ⟨fun p hp => hambient.1 p (hsubset hp),
        fun p hp => hambient.2 p (hsubset hp)⟩
    have hcardFull := hcardX (R x) (taoDyadicPrimeBand (R x)) hRtwo hD
    have hcardFiltered :
        (((taoDyadicPrimeBand (R x)).filter fun p =>
          p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
            (taoDyadicPrimeBand (R x)) (P x) (R x)).card : ℝ) ≤
          K * (R x : ℝ) ^ (1 / 50 : ℝ) := by
      calc
        (((taoDyadicPrimeBand (R x)).filter fun p =>
            p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
              (taoDyadicPrimeBand (R x)) (P x) (R x)).card : ℝ) ≤
          ((taoLargePrimeAdaptiveExceptionalConductorsFor
            (taoDyadicPrimeBand (R x)) (P x) (R x)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (by
                intro p hp
                exact (Finset.mem_filter.mp hp).2)
        _ ≤ K * (R x : ℝ) ^ (1 / 50 : ℝ) := hcardFull
    have hB : 0 ≤
        256 * Real.log (taoZ x) ^ 2 / (R x : ℝ) := by positivity
    have hblock := sum_taoBackwardLargePrimeProbability_adaptive_dyadicBlock_le
      (P x) hP (R x) (H x) (m' x) hRtwo hHscaleX
        (1003 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)))
        (256 * Real.log (taoZ x) ^ 2 / (R x : ℝ))
        (K * (R x : ℝ) ^ (1 / 50 : ℝ))
        (by positivity) hB (fun p hp => herrorX p hp) hcardFiltered
        (by
          intro a ha _haExceptional
          have haData := mem_taoLargeAntiSieveIndices.mp ha
          have haBand : a.2 ∈ taoDyadicPrimeBand (R x) := by
            rw [← taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand
              (show 0 < R x by omega)]
            exact mem_taoLargeAntiSievePrimeRange.mpr haData.2.2
          have halt : a.1 < a.2 := by omega
          exact hcrudeX hP a haBand haData.1 halt)
    simpa only [Good, R] using hblock
  have hall := eventually_forall_of_forall_selector hne hselector
  refine ⟨K, hK, ?_⟩
  simpa only [Rel, Good] using hall

/-- The ordered adaptive backward covariance block holds simultaneously on
every ordered pair of retained source scales. -/
theorem exists_eventually_forall_sum_taoBackwardLargePrimeCovariance_adaptive_sourceTwoBand_restrict_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      ∀ s ∈ taoLargePrimeSourceDyadicExponents x, r ≤ s →
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ DR DS : Finset ℕ,
      DR ⊆ taoDyadicPrimeBand (2 ^ r) →
      DS ⊆ taoDyadicPrimeBand (2 ^ s) →
      (∑ a ∈ (Finset.Ico 1 (H x)).product DR,
        ∑ b ∈ ((Finset.Ico 1 (H x)).product DS).filter (fun b => b.2 ≠ a.2),
          taoBackwardLargePrimeCovariance (P x) hP (m' x) a b) ≤
        ((H x - 1 : ℕ) : ℝ) ^ 2 *
          (((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
              ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) *
              (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
                ((2 ^ r : ℕ) : ℝ) ^ (-(1001 / 1000 : ℝ)) *
                ((2 ^ s : ℕ) : ℝ) ^ (-(1 : ℝ))) +
            (K * (((2 ^ r : ℕ) : ℝ) ^ (1 / 50 : ℝ) *
                ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
              ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
                ((2 ^ s : ℕ) : ℝ) ^ (1 / 50 : ℝ))) *
              (6144 * Real.log (taoZ x) ^ 3 /
                (((2 ^ r : ℕ) : ℝ) * ((2 ^ s : ℕ) : ℝ)))) := by
  obtain ⟨K, hK, hcard⟩ :=
    exists_eventually_forall_card_taoLargePrimeAdaptiveExceptionalModuliPairs_le_of_explicitBurgess
      hC hburgess hscale
  let Rel : ℕ → (ℕ × ℕ) → Prop := fun x rs =>
    rs.1 ∈ taoLargePrimeSourceDyadicExponents x ∧
      rs.2 ∈ taoLargePrimeSourceDyadicExponents x ∧ rs.1 ≤ rs.2
  let Good : ℕ → (ℕ × ℕ) → Prop := fun x rs =>
    ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ DR DS : Finset ℕ,
      DR ⊆ taoDyadicPrimeBand (2 ^ rs.1) →
      DS ⊆ taoDyadicPrimeBand (2 ^ rs.2) →
      (∑ a ∈ (Finset.Ico 1 (H x)).product DR,
        ∑ b ∈ ((Finset.Ico 1 (H x)).product DS).filter (fun b => b.2 ≠ a.2),
          taoBackwardLargePrimeCovariance (P x) hP (m' x) a b) ≤
        ((H x - 1 : ℕ) : ℝ) ^ 2 *
          (((taoDyadicPrimeBand (2 ^ rs.1)).card : ℝ) *
              ((taoDyadicPrimeBand (2 ^ rs.2)).card : ℝ) *
              (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
                ((2 ^ rs.1 : ℕ) : ℝ) ^ (-(1001 / 1000 : ℝ)) *
                ((2 ^ rs.2 : ℕ) : ℝ) ^ (-(1 : ℝ))) +
            (K * (((2 ^ rs.1 : ℕ) : ℝ) ^ (1 / 50 : ℝ) *
                ((taoDyadicPrimeBand (2 ^ rs.2)).card : ℝ) +
              ((taoDyadicPrimeBand (2 ^ rs.1)).card : ℝ) *
                ((2 ^ rs.2 : ℕ) : ℝ) ^ (1 / 50 : ℝ))) *
              (6144 * Real.log (taoZ x) ^ 3 /
                (((2 ^ rs.1 : ℕ) : ℝ) * ((2 ^ rs.2 : ℕ) : ℝ))))
  have hne : ∀ᶠ x : ℕ in atTop, ∃ rs, Rel x rs :=
    eventually_taoLargePrimeSourceDyadicExponents_nonempty.mono fun x hx => by
      exact ⟨(hx.choose, hx.choose), hx.choose_spec, hx.choose_spec, le_rfl⟩
  have hselector : ∀ f : ℕ → (ℕ × ℕ),
      (∀ᶠ x : ℕ in atTop, Rel x (f x)) →
        ∀ᶠ x : ℕ in atTop, Good x (f x) := by
    intro f hf
    have hfR : ∀ᶠ x : ℕ in atTop,
        (f x).1 ∈ taoLargePrimeSourceDyadicExponents x := by
      exact hf.mono fun x hx => hx.1
    have hfS : ∀ᶠ x : ℕ in atTop,
        (f x).2 ∈ taoLargePrimeSourceDyadicExponents x := by
      exact hf.mono fun x hx => hx.2.1
    have hfRS : ∀ᶠ x : ℕ in atTop, (f x).1 ≤ (f x).2 := by
      exact hf.mono fun x hx => hx.2.2
    let R : ℕ → ℕ := fun x => 2 ^ (f x).1
    let S : ℕ → ℕ := fun x => 2 ^ (f x).2
    have hR : TaoLargePrimeDyadicBandSelector R :=
      taoLargePrimeDyadicBandSelector_of_eventually_mem_sourceDyadicExponents hfR
    have hS : TaoLargePrimeDyadicBandSelector S :=
      taoLargePrimeDyadicBandSelector_of_eventually_mem_sourceDyadicExponents hfS
    have hRS : ∀ᶠ x : ℕ in atTop, R x ≤ S x := by
      filter_upwards [hfRS] with x hx
      exact Nat.pow_le_pow_right (by norm_num) hx
    have hgeom := eventually_taoLargePrimeAdaptive_commonRange_geometry
      hscale hR hS hRS
    have herror :=
      eventually_taoLargePrimeMixedAdaptiveCovarianceImprovedError_le_sourcePower
        hscale hR.toTaoLargePrimeSourceBandSelector
          hS.toTaoLargePrimeSourceBandSelector hRS
    have hcrude := eventually_taoBackwardLargePrimeJointProbability_le_crude_twoBand
      hscale hR hS m'
    have hHscaleR : ∀ᶠ x : ℕ in atTop, H x ≤ R x - 1 := by
      filter_upwards
        [hH, eventually_taoTypicalLengthCutoff_le_sourceDyadicScale_sub_one,
          hfR] with x hHX hgrid hfX
      exact hHX.trans (hgrid (f x).1 hfX)
    have hHscaleS : ∀ᶠ x : ℕ in atTop, H x ≤ S x - 1 := by
      filter_upwards
        [hH, eventually_taoTypicalLengthCutoff_le_sourceDyadicScale_sub_one,
          hfS] with x hHX hgrid hfX
      exact hHX.trans (hgrid (f x).2 hfX)
    filter_upwards [hcard, hgeom, herror, hcrude, hHscaleR, hHscaleS,
      hR.eventually_two_le, hS.eventually_two_le,
      tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
        x hcardX hgeomX herrorX hcrudeX hHRX hHSX hRtwo hStwo hz
    intro hP DR DS hDR hDS
    have hcardPair := hcardX (R x) (S x) (R x - 1) (2 * S x - 1)
      hRtwo hStwo hgeomX.1 hgeomX.2.1 hgeomX.2.2.1 hgeomX.2.2.2
    have hB : 0 ≤ 6144 * Real.log (taoZ x) ^ 3 /
        ((R x : ℝ) * (S x : ℝ)) := by
      exact div_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (Real.log_nonneg hz) 3))
        (mul_nonneg (by positivity) (by positivity))
    have hblock := sum_taoBackwardLargePrimeCovariance_adaptive_twoBand_restrict_le
      (P x) hP (R x) (S x) (H x) (m' x) DR DS hDR hDS
        hRtwo hStwo hHRX hHSX
        (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)))
        (6144 * Real.log (taoZ x) ^ 3 / ((R x : ℝ) * (S x : ℝ)))
        (K * ((R x : ℝ) ^ (1 / 50 : ℝ) *
            ((taoDyadicPrimeBand (S x)).card : ℝ) +
          ((taoDyadicPrimeBand (R x)).card : ℝ) *
            (S x : ℝ) ^ (1 / 50 : ℝ)))
        (by
          unfold taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant
          unfold taoLargePrimeMixedAdaptiveSourceJointPowerConstant
          unfold taoLargePrimeSourceJointPowerConstant
          positivity)
        hB (fun p hp q hq hpq _hpair => herrorX p q hp hq hpq)
        hcardPair
        (by
          intro a ha b hb _hbad
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
          have halt : a.1 < a.2 := by omega
          have hblt : b.1 < b.2 := by omega
          exact hcrudeX hP a b haBand hbBand hpq
            haData.1 halt hbData.1 hblt)
    simpa only [Good, R, S] using hblock
  have hall := eventually_forall_of_forall_selector hne hselector
  refine ⟨K, hK, ?_⟩
  filter_upwards [hall] with x hx
  intro r hr s hs hrs hP DR DS hDR hDS
  exact hx (r, s) ⟨hr, hs, hrs⟩ hP DR DS hDR hDS

/-- Full-band corollary of the simultaneous restricted backward covariance
block. -/
theorem exists_eventually_forall_sum_taoBackwardLargePrimeCovariance_adaptive_sourceTwoBand_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      ∀ s ∈ taoLargePrimeSourceDyadicExponents x, r ≤ s →
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
          (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
        ∑ b ∈ (taoLargeAntiSieveIndices
          (2 ^ s - 1) (2 * 2 ^ s - 1) (H x)).filter
            (fun b => b.2 ≠ a.2),
          taoBackwardLargePrimeCovariance (P x) hP (m' x) a b) ≤
        ((H x - 1 : ℕ) : ℝ) ^ 2 *
          (((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
              ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) *
              (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
                ((2 ^ r : ℕ) : ℝ) ^ (-(1001 / 1000 : ℝ)) *
                ((2 ^ s : ℕ) : ℝ) ^ (-(1 : ℝ))) +
            (K * (((2 ^ r : ℕ) : ℝ) ^ (1 / 50 : ℝ) *
                ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
              ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
                ((2 ^ s : ℕ) : ℝ) ^ (1 / 50 : ℝ))) *
              (6144 * Real.log (taoZ x) ^ 3 /
                (((2 ^ r : ℕ) : ℝ) * ((2 ^ s : ℕ) : ℝ)))) := by
  obtain ⟨K, hK, hrestricted⟩ :=
    exists_eventually_forall_sum_taoBackwardLargePrimeCovariance_adaptive_sourceTwoBand_restrict_le
      hC hburgess hscale H m' hH
  refine ⟨K, hK, ?_⟩
  filter_upwards [hrestricted] with x hx
  intro r hr s hs hrs hP
  have h := hx r hr s hs hrs hP
    (taoDyadicPrimeBand (2 ^ r)) (taoDyadicPrimeBand (2 ^ s))
      (by rfl) (by rfl)
  have hRpos : 0 < (2 ^ r : ℕ) := by positivity
  have hSpos : 0 < (2 ^ s : ℕ) := by positivity
  have hrangeR := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hRpos
  have hrangeS := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hSpos
  simpa only [taoLargeAntiSieveIndices, hrangeR, hrangeS] using h

/-- The complete backward first-moment sum over all source dyadic scales is
`O(H)`. -/
theorem eventually_sum_taoBackwardLargePrimeProbability_adaptive_sourceDyadicScales_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ a ∈ taoLargeAntiSieveIndices
          (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
          taoBackwardLargePrimeProbability (P x) hP (m' x) a) ≤
        2000000 * (H x : ℝ) := by
  obtain ⟨K, hK, hblocks⟩ :=
    exists_eventually_forall_sum_taoBackwardLargePrimeProbability_adaptive_sourceBlock_le
      hC hburgess hscale H m' hH
  have hmajorant :=
    eventually_forall_taoLargePrimeSourceFirstMomentBlockMajorant_le hK.le
  filter_upwards [hblocks, hmajorant,
    eventually_card_taoLargePrimeSourceDyadicExponents_cast_le_log,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with
      x hblocksX hmajorantX hcardX hz
  intro hP
  let L : ℝ := Real.log (taoZ x)
  have hLone : 1 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hsumBlocks :
      (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ a ∈ taoLargeAntiSieveIndices
          (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
          taoBackwardLargePrimeProbability (P x) hP (m' x) a) ≤
      ∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ((H x - 1 : ℕ) : ℝ) *
          taoLargePrimeSourceFirstMomentBlockMajorant K x r := by
    apply Finset.sum_le_sum
    intro r hr
    simpa only [taoLargePrimeSourceFirstMomentBlockMajorant] using
      hblocksX r hr hP
  calc
    (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ a ∈ taoLargeAntiSieveIndices
          (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
          taoBackwardLargePrimeProbability (P x) hP (m' x) a) ≤
      ∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ((H x - 1 : ℕ) : ℝ) *
          taoLargePrimeSourceFirstMomentBlockMajorant K x r := hsumBlocks
    _ ≤ ∑ _r ∈ taoLargePrimeSourceDyadicExponents x,
        ((H x - 1 : ℕ) : ℝ) * (500000 / L) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (by simpa only [L] using hmajorantX r hr) (by positivity)
    _ = ((taoLargePrimeSourceDyadicExponents x).card : ℝ) *
        (((H x - 1 : ℕ) : ℝ) * (500000 / L)) := by simp
    _ ≤ (4 * L) * (((H x - 1 : ℕ) : ℝ) * (500000 / L)) := by
      exact mul_le_mul_of_nonneg_right (by simpa only [L] using hcardX)
        (by positivity)
    _ = 2000000 * ((H x - 1 : ℕ) : ℝ) := by
      field_simp [ne_of_gt hLpos]
      ring
    _ ≤ 2000000 * (H x : ℝ) := by
      gcongr
      exact_mod_cast Nat.sub_le (H x) 1

/-- The expected backward large-prime contribution on the literal source
prime range is `O(H)`. -/
theorem eventually_taoBackwardLargePrimeMean_sourceCutoffs_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      taoBackwardLargePrimeMean (P x) hP
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) ≤
        2000000 * (H x : ℝ) := by
  filter_upwards
    [eventually_sum_taoBackwardLargePrimeProbability_adaptive_sourceDyadicScales_le
      hC hburgess hscale H m' hH] with x hsum
  intro hP
  rw [taoBackwardLargePrimeMean_eq,
    taoLargeAntiSieveIndices_sourceCutoffs_eq,
    sum_taoLargePrimeSourceIndices_eq_sum_dyadicSlices]
  apply le_trans (Finset.sum_le_sum (fun r hr => ?_)) (hsum hP)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro a ha
      have haData := Finset.mem_product.mp ha
      rw [taoLargeAntiSieveIndices,
        taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand (by positivity)]
      exact Finset.mem_product.mpr
        ⟨haData.1, taoLargePrimeSourceDyadicPrimeSlice_subset_band x r haData.2⟩)
    (fun a _ _ => taoBackwardLargePrimeProbability_nonneg (P x) hP (m' x) a)

/-- Transposing two restricted dyadic slices leaves their backward
distinct-prime covariance block unchanged. -/
theorem sum_taoBackwardLargePrimeCovariance_sourceDyadicSlices_comm
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' x H r s : ℕ) :
    (∑ a ∈ taoLargePrimeSourceDyadicIndices x r H,
      ∑ b ∈ (taoLargePrimeSourceDyadicIndices x s H).filter
          (fun b => b.2 ≠ a.2),
        taoBackwardLargePrimeCovariance P hP m' a b) =
      ∑ b ∈ taoLargePrimeSourceDyadicIndices x s H,
        ∑ a ∈ (taoLargePrimeSourceDyadicIndices x r H).filter
            (fun a => a.2 ≠ b.2),
          taoBackwardLargePrimeCovariance P hP m' b a := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hab : a.2 ≠ b.2
  · rw [if_pos hab, if_pos hab.symm]
    exact taoBackwardLargePrimeCovariance_comm P hP m' a b
  · rw [if_neg hab, if_neg]
    exact fun h => hab h.symm

/-- Exact decomposition of the literal source backward covariance sum into
ordered pairs of exact dyadic slices. -/
theorem sum_taoBackwardLargePrimeCovariance_sourceIndices_eq_sum_dyadicSlices
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' x H : ℕ) :
    (∑ a ∈ (Finset.Ico 1 H).product (taoLargePrimeSourcePrimes x),
      ∑ b ∈ ((Finset.Ico 1 H).product
          (taoLargePrimeSourcePrimes x)).filter (fun b => b.2 ≠ a.2),
        taoBackwardLargePrimeCovariance P hP m' a b) =
      ∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ s ∈ taoLargePrimeSourceDyadicExponents x,
          ∑ a ∈ taoLargePrimeSourceDyadicIndices x r H,
            ∑ b ∈ (taoLargePrimeSourceDyadicIndices x s H).filter
                (fun b => b.2 ≠ a.2),
              taoBackwardLargePrimeCovariance P hP m' a b := by
  rw [sum_taoLargePrimeSourceIndices_eq_sum_dyadicSlices]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (∑ a ∈ taoLargePrimeSourceDyadicIndices x r H,
        ∑ b ∈ ((Finset.Ico 1 H).product
            (taoLargePrimeSourcePrimes x)).filter (fun b => b.2 ≠ a.2),
          taoBackwardLargePrimeCovariance P hP m' a b) =
        ∑ a ∈ taoLargePrimeSourceDyadicIndices x r H,
          ∑ s ∈ taoLargePrimeSourceDyadicExponents x,
            ∑ b ∈ (taoLargePrimeSourceDyadicIndices x s H).filter
                (fun b => b.2 ≠ a.2),
              taoBackwardLargePrimeCovariance P hP m' a b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_filter]
      rw [sum_taoLargePrimeSourceIndices_eq_sum_dyadicSlices]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_filter]
    _ = ∑ s ∈ taoLargePrimeSourceDyadicExponents x,
          ∑ a ∈ taoLargePrimeSourceDyadicIndices x r H,
            ∑ b ∈ (taoLargePrimeSourceDyadicIndices x s H).filter
                (fun b => b.2 ≠ a.2),
              taoBackwardLargePrimeCovariance P hP m' a b := by
      rw [Finset.sum_comm]

/-- The complete backward off-diagonal covariance sum on the literal source
prime range is `O(H)`. -/
theorem eventually_sum_taoBackwardLargePrimeCovariance_sourceCutoffs_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x),
        ∑ b ∈ (taoLargeAntiSieveIndices
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x)).filter
            (fun b => b.2 ≠ a.2),
          taoBackwardLargePrimeCovariance (P x) hP (m' x) a b) ≤
        (H x : ℝ) := by
  obtain ⟨K, hK, hblocks⟩ :=
    exists_eventually_forall_sum_taoBackwardLargePrimeCovariance_adaptive_sourceTwoBand_restrict_le
      hC hburgess hscale H m' hH
  let B : ℝ := 4 * taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant + 1
  have hA : 0 ≤ taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant := by
    unfold taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant
    unfold taoLargePrimeMixedAdaptiveSourceJointPowerConstant
    unfold taoLargePrimeSourceJointPowerConstant
    positivity
  have hB : 0 < B := by dsimp only [B]; linarith
  have hmajorant :=
    eventually_forall_taoLargePrimeSourceCovarianceBlockMajorant_le hK.le
  have hlogAbsorb := eventually_const_mul_log_rpow_taoZ_div_rpow_le
    (C := 16 * B) (k := (2 : ℝ)) (a := (1 / 400000 : ℝ))
      (b := (0 : ℝ)) (mul_nonneg (by norm_num) hB.le) (by norm_num)
  have hlengthAbsorb := eventually_const_mul_taoTypicalLengthCutoff_le_taoZ_rpow
    (C := (1 : ℝ)) (δ := (1 / 400000 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [hblocks, hmajorant,
    eventually_card_taoLargePrimeSourceDyadicExponents_cast_le_log,
    hlogAbsorb, hlengthAbsorb, hH,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with
      x hblocksX hmajorantX hcardX hlogAbsorbX hlengthAbsorbX hHX hz
  intro hP
  let L : ℝ := Real.log (taoZ x)
  let Zδ : ℝ := (taoZ x) ^ (1 / 200000 : ℝ)
  let Zhalf : ℝ := (taoZ x) ^ (1 / 400000 : ℝ)
  have hLone : 1 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hZδpos : 0 < Zδ := by
    dsimp only [Zδ]
    exact Real.rpow_pos_of_pos (taoZ_pos x) _
  have hZhalfPos : 0 < Zhalf := by
    dsimp only [Zhalf]
    exact Real.rpow_pos_of_pos (taoZ_pos x) _
  have hlogAbsorbNat : 16 * B * L ^ (2 : ℕ) ≤ Zhalf := by
    have hx := hlogAbsorbX
    rw [Real.rpow_zero, div_one] at hx
    have hx' : 16 * B * L ^ (2 : ℕ) / Zhalf ≤ 1 := by
      rw [show L ^ (2 : ℕ) = L ^ (2 : ℝ) from
        (Real.rpow_natCast L 2).symm]
      simpa only [L, Zhalf] using hx
    have := (div_le_iff₀ hZhalfPos).mp hx'
    simpa only [one_mul] using this
  have hlengthPower : (H x : ℝ) ≤ Zhalf := by
    calc
      (H x : ℝ) ≤ (taoTypicalLengthCutoff x : ℝ) := by
        exact_mod_cast hHX
      _ = 1 * (taoTypicalLengthCutoff x : ℝ) := by ring
      _ ≤ Zhalf := by simpa only [Zhalf] using hlengthAbsorbX
  have hhalfSquare : Zhalf * Zhalf = Zδ := by
    dsimp only [Zhalf, Zδ]
    rw [← Real.rpow_add (taoZ_pos x)]
    congr 1
    norm_num
  have hcoefficient : (4 * L) ^ (2 : ℕ) * B * (H x : ℝ) ≤ Zδ := by
    calc
      (4 * L) ^ (2 : ℕ) * B * (H x : ℝ) =
          (16 * B * L ^ (2 : ℕ)) * (H x : ℝ) := by ring
      _ ≤ Zhalf * Zhalf :=
        mul_le_mul hlogAbsorbNat hlengthPower (by positivity) hZhalfPos.le
      _ = Zδ := hhalfSquare
  have hHsub : (((H x - 1 : ℕ) : ℝ) : ℝ) ≤ (H x : ℝ) := by
    exact_mod_cast Nat.sub_le (H x) 1
  have htermNonneg : 0 ≤
      ((H x : ℝ) ^ 2 * (B * (Zδ)⁻¹)) := by positivity
  have hblockUniform :
      ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      ∀ s ∈ taoLargePrimeSourceDyadicExponents x,
      (∑ a ∈ taoLargePrimeSourceDyadicIndices x r (H x),
        ∑ b ∈ (taoLargePrimeSourceDyadicIndices x s (H x)).filter
            (fun b => b.2 ≠ a.2),
          taoBackwardLargePrimeCovariance (P x) hP (m' x) a b) ≤
        (H x : ℝ) ^ 2 * (B * (Zδ)⁻¹) := by
    intro r hr s hs
    by_cases hrs : r ≤ s
    · have hblock := hblocksX r hr s hs hrs hP
          (taoLargePrimeSourceDyadicPrimeSlice x r)
          (taoLargePrimeSourceDyadicPrimeSlice x s)
          (taoLargePrimeSourceDyadicPrimeSlice_subset_band x r)
          (taoLargePrimeSourceDyadicPrimeSlice_subset_band x s)
      have hmaj := hmajorantX r hr s hs hrs
      have hmaj' : taoLargePrimeSourceCovarianceBlockMajorant K x r s ≤
          B * (Zδ)⁻¹ := by
        simpa only [B, Zδ, Real.rpow_neg (taoZ_pos x).le] using hmaj
      have hmajNonneg : 0 ≤
          taoLargePrimeSourceCovarianceBlockMajorant K x r s := by
        rw [taoLargePrimeSourceCovarianceBlockMajorant]
        positivity
      calc
        _ ≤ ((H x - 1 : ℕ) : ℝ) ^ 2 *
            taoLargePrimeSourceCovarianceBlockMajorant K x r s := by
          simpa only [taoLargePrimeSourceDyadicIndices,
            taoLargePrimeSourceCovarianceBlockMajorant] using hblock
        _ ≤ (H x : ℝ) ^ 2 *
            taoLargePrimeSourceCovarianceBlockMajorant K x r s := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hHsub 2) hmajNonneg
        _ ≤ (H x : ℝ) ^ 2 * (B * (Zδ)⁻¹) :=
          mul_le_mul_of_nonneg_left hmaj' (sq_nonneg _)
    · have hsr : s ≤ r := Nat.le_of_lt (lt_of_not_ge hrs)
      have hblock := hblocksX s hs r hr hsr hP
          (taoLargePrimeSourceDyadicPrimeSlice x s)
          (taoLargePrimeSourceDyadicPrimeSlice x r)
          (taoLargePrimeSourceDyadicPrimeSlice_subset_band x s)
          (taoLargePrimeSourceDyadicPrimeSlice_subset_band x r)
      have hmaj := hmajorantX s hs r hr hsr
      have hmaj' : taoLargePrimeSourceCovarianceBlockMajorant K x s r ≤
          B * (Zδ)⁻¹ := by
        simpa only [B, Zδ, Real.rpow_neg (taoZ_pos x).le] using hmaj
      have hmajNonneg : 0 ≤
          taoLargePrimeSourceCovarianceBlockMajorant K x s r := by
        rw [taoLargePrimeSourceCovarianceBlockMajorant]
        positivity
      calc
        _ = ∑ b ∈ taoLargePrimeSourceDyadicIndices x s (H x),
              ∑ a ∈ (taoLargePrimeSourceDyadicIndices x r (H x)).filter
                  (fun a => a.2 ≠ b.2),
                taoBackwardLargePrimeCovariance (P x) hP (m' x) b a :=
          sum_taoBackwardLargePrimeCovariance_sourceDyadicSlices_comm
            (P x) hP (m' x) x (H x) r s
        _ ≤ ((H x - 1 : ℕ) : ℝ) ^ 2 *
            taoLargePrimeSourceCovarianceBlockMajorant K x s r := by
          simpa only [taoLargePrimeSourceDyadicIndices,
            taoLargePrimeSourceCovarianceBlockMajorant] using hblock
        _ ≤ (H x : ℝ) ^ 2 *
            taoLargePrimeSourceCovarianceBlockMajorant K x s r := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hHsub 2) hmajNonneg
        _ ≤ (H x : ℝ) ^ 2 * (B * (Zδ)⁻¹) :=
          mul_le_mul_of_nonneg_left hmaj' (sq_nonneg _)
  rw [taoLargeAntiSieveIndices_sourceCutoffs_eq,
    sum_taoBackwardLargePrimeCovariance_sourceIndices_eq_sum_dyadicSlices]
  calc
    (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ s ∈ taoLargePrimeSourceDyadicExponents x,
          ∑ a ∈ taoLargePrimeSourceDyadicIndices x r (H x),
            ∑ b ∈ (taoLargePrimeSourceDyadicIndices x s (H x)).filter
                (fun b => b.2 ≠ a.2),
              taoBackwardLargePrimeCovariance (P x) hP (m' x) a b) ≤
      ∑ _r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ _s ∈ taoLargePrimeSourceDyadicExponents x,
          (H x : ℝ) ^ 2 * (B * (Zδ)⁻¹) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      exact hblockUniform r hr s hs
    _ = ((taoLargePrimeSourceDyadicExponents x).card : ℝ) ^ 2 *
        ((H x : ℝ) ^ 2 * (B * (Zδ)⁻¹)) := by simp; ring
    _ ≤ (4 * L) ^ 2 * ((H x : ℝ) ^ 2 * (B * (Zδ)⁻¹)) := by
      have hcardNonneg : 0 ≤
          ((taoLargePrimeSourceDyadicExponents x).card : ℝ) := by positivity
      have hcardSq := pow_le_pow_left₀ hcardNonneg
        (by simpa only [L] using hcardX) 2
      exact mul_le_mul_of_nonneg_right hcardSq htermNonneg
    _ = (H x : ℝ) *
        (((4 * L) ^ 2 * B * (H x : ℝ)) * (Zδ)⁻¹) := by ring
    _ ≤ (H x : ℝ) * (Zδ * (Zδ)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoefficient (by positivity)) (by positivity)
    _ = (H x : ℝ) := by
      rw [mul_inv_cancel₀ hZδpos.ne', mul_one]

/-- The complete backward large-prime variance on the literal source range is
`O(H)`. -/
theorem eventually_taoBackwardLargePrimeVariance_sourceCutoffs_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      taoBackwardLargePrimeVariance (P x) hP
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) ≤
        2000001 * (H x : ℝ) := by
  filter_upwards
    [eventually_taoBackwardLargePrimeMean_sourceCutoffs_le
      hC hburgess hscale H m' hH,
    eventually_sum_taoBackwardLargePrimeCovariance_sourceCutoffs_le
      hC hburgess hscale H m' hH,
    hH, eventually_taoTypicalLengthCutoff_le_sourceLowerCutoff] with
      x hmean hcov hHX hlower
  intro hP
  have hHlower : H x ≤ taoLargePrimeSourceLowerCutoff x := hHX.trans hlower
  calc
    taoBackwardLargePrimeVariance (P x) hP
        (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) ≤
      taoBackwardLargePrimeMean (P x) hP
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) +
        ∑ a ∈ taoLargeAntiSieveIndices
            (taoLargePrimeSourceLowerCutoff x)
            (taoLargePrimeSourceUpperCutoff x) (H x),
          ∑ b ∈ (taoLargeAntiSieveIndices
            (taoLargePrimeSourceLowerCutoff x)
            (taoLargePrimeSourceUpperCutoff x) (H x)).filter
              (fun b => b.2 ≠ a.2),
            taoBackwardLargePrimeCovariance (P x) hP (m' x) a b :=
      taoBackwardLargePrimeVariance_le_mean_add_distinctPrimeCovariances
        (P x) hP _ _ _ _ hHlower
    _ ≤ 2000000 * (H x : ℝ) + (H x : ℝ) :=
      add_le_add (hmean hP) (hcov hP)
    _ = 2000001 * (H x : ℝ) := by ring

end

end Tao2026
