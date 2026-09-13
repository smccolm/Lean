import Tao2026.BadIntervalLargePrimeErrorNormalize

/-!
# Source-scale large-prime error envelopes

The tuple coordinate scales satisfy `P_j = z^(1+o(1))`.  This module turns
that logarithmic contract and the dyadic PNT into simultaneous explicit
envelopes for the reciprocal-band, eighth-power, and change-level collision
aggregates occurring in the improved probability errors.
-/

namespace Tao2026

open Filter Topology

noncomputable section

/-- Every coordinate scale is eventually at least `z^β`, uniformly over the
fixed coordinate family, for any fixed exponent `β < 1`. -/
theorem eventually_taoPrimeTupleSourceScale_lower_rpow
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {β : ℝ} (hβ : β < 1) :
    ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      (taoZ x) ^ β ≤ (P x j : ℝ) := by
  have hj : ∀ j : Fin 1001, ∀ᶠ x : ℕ in atTop,
      (taoZ x) ^ β ≤ (P x j : ℝ) := by
    intro j
    filter_upwards [
      (hscale.log_ratio j).eventually (Ioi_mem_nhds hβ),
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
      (hscale.tendsto_scale j).eventually (eventually_gt_atTop (0 : ℕ))] with
        x hratio hz hP
    have hlogz : 0 < Real.log (taoZ x) := Real.log_pos hz
    have hlog : β * Real.log (taoZ x) ≤ Real.log (P x j : ℝ) := by
      exact (le_div_iff₀ hlogz).mp hratio.le
    have hPpos : (0 : ℝ) < (P x j : ℝ) := by exact_mod_cast hP
    calc
      (taoZ x) ^ β = Real.exp (Real.log (taoZ x) * β) :=
        Real.rpow_def_of_pos (taoZ_pos x) _
      _ ≤ Real.exp (Real.log (P x j : ℝ)) :=
        Real.exp_le_exp.mpr (by simpa [mul_comm] using hlog)
      _ = (P x j : ℝ) := Real.exp_log hPpos
  have hall : ∀ᶠ x : ℕ in atTop,
      ∀ j ∈ (Finset.univ : Finset (Fin 1001)),
        (taoZ x) ^ β ≤ (P x j : ℝ) := by
    rw [Filter.eventually_all_finset]
    intro j hjmem
    exact hj j
  simpa using hall

/-- Every coordinate scale is eventually at least `z^(9/10)`, uniformly over
the fixed 1001-coordinate family. -/
theorem eventually_taoPrimeTupleSourceScale_lower_nine_tenths
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      (taoZ x) ^ (9 / 10 : ℝ) ≤ (P x j : ℝ) := by
  exact eventually_taoPrimeTupleSourceScale_lower_rpow hscale (by norm_num)

/-- Pointwise reciprocal-band envelope, simultaneously for all tuple
coordinates. -/
theorem eventually_taoPrimeTupleSourceScale_band_reciprocal_le
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      ((taoDyadicPrimeBand (P x j)).card : ℝ)⁻¹ ≤
        4 * Real.log (taoZ x) / (taoZ x) ^ (9 / 10 : ℝ) := by
  filter_upwards [eventually_taoPrimeTupleSourceScale_lower_nine_tenths hscale,
    eventually_taoPrimeTupleSourceScale_band_normalization hscale,
    eventually_taoPrimeTupleSourceScale_bands_nonempty hscale,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hlow hband hnonempty hz
  intro j
  have hcardPos : (0 : ℝ) < (taoDyadicPrimeBand (P x j)).card := by
    exact_mod_cast Finset.card_pos.mpr (hnonempty j)
  have hzpow : (0 : ℝ) < (taoZ x) ^ (9 / 10 : ℝ) := by positivity
  rw [← one_div]
  apply (div_le_div_iff₀ hcardPos hzpow).2
  calc
    1 * (taoZ x) ^ (9 / 10 : ℝ) ≤ (P x j : ℝ) := by
      simpa using hlow j
    _ ≤ (4 * Real.log (taoZ x)) *
        ((taoDyadicPrimeBand (P x j)).card : ℝ) := hband j

/-- Summed principal-collision mass at the source scale. -/
theorem eventually_taoPrimeTupleBandReciprocalSum_le_source
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop,
      taoPrimeTupleBandReciprocalSum (P x) ≤
        1001 * (4 * Real.log (taoZ x) /
          (taoZ x) ^ (9 / 10 : ℝ)) := by
  filter_upwards [eventually_taoPrimeTupleSourceScale_band_reciprocal_le hscale]
    with x hterm
  unfold taoPrimeTupleBandReciprocalSum
  calc
    (∑ j : Fin 1001, ((taoDyadicPrimeBand (P x j)).card : ℝ)⁻¹) ≤
        ∑ _j : Fin 1001,
          4 * Real.log (taoZ x) / (taoZ x) ^ (9 / 10 : ℝ) := by
      exact Finset.sum_le_sum fun j _ => hterm j
    _ = 1001 * (4 * Real.log (taoZ x) /
        (taoZ x) ^ (9 / 10 : ℝ)) := by simp

/-- Summed nonprincipal eighth-power mass at the source scale. -/
theorem eventually_taoPrimeTupleEighthPowerSum_le_source
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop,
      taoPrimeTupleEighthPowerSum (P x) ≤
        1000 * (((taoZ x) ^ (9 / 10 : ℝ)) ^ (-(8 : ℝ))) := by
  filter_upwards [eventually_taoPrimeTupleSourceScale_lower_nine_tenths hscale,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hlow hz
  have hterm : ∀ j : Fin 1001,
      (P x j : ℝ) ^ (-(8 : ℝ)) ≤
        ((taoZ x) ^ (9 / 10 : ℝ)) ^ (-(8 : ℝ)) := by
    intro j
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (hlow j) (by norm_num)
  unfold taoPrimeTupleEighthPowerSum
  calc
    (∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        (P x j : ℝ) ^ (-(8 : ℝ))) ≤
      ∑ _j ∈ Finset.univ.erase (0 : Fin 1001),
        ((taoZ x) ^ (9 / 10 : ℝ)) ^ (-(8 : ℝ)) := by
      exact Finset.sum_le_sum fun j _ => hterm j
    _ = 1000 * (((taoZ x) ^ (9 / 10 : ℝ)) ^ (-(8 : ℝ))) := by simp

/-- Summed 1000th-power change-level collision mass at the source scale. -/
theorem eventually_taoPrimeTupleChangeLevelCollisionSum_le_source
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop,
      taoPrimeTupleChangeLevelCollisionSum (P x) ≤
        1000 * (16 * Real.log (taoZ x) /
          (taoZ x) ^ (9 / 10 : ℝ)) ^ (1000 : ℕ) := by
  filter_upwards [eventually_taoPrimeTupleSourceScale_band_reciprocal_le hscale,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hreciprocal hz
  have hterm : ∀ j : Fin 1001,
      (4 * ((taoDyadicPrimeBand (P x j)).card : ℝ)⁻¹) ^ (1000 : ℕ) ≤
        (16 * Real.log (taoZ x) /
          (taoZ x) ^ (9 / 10 : ℝ)) ^ (1000 : ℕ) := by
    intro j
    have hbase : 4 * ((taoDyadicPrimeBand (P x j)).card : ℝ)⁻¹ ≤
          4 * (4 * Real.log (taoZ x) /
            (taoZ x) ^ (9 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hreciprocal j) (by norm_num)
    have hbase' : 4 * ((taoDyadicPrimeBand (P x j)).card : ℝ)⁻¹ ≤
        16 * Real.log (taoZ x) /
          (taoZ x) ^ (9 / 10 : ℝ) := by
      calc
        _ ≤ 4 * (4 * Real.log (taoZ x) /
            (taoZ x) ^ (9 / 10 : ℝ)) := hbase
        _ = 16 * Real.log (taoZ x) /
            (taoZ x) ^ (9 / 10 : ℝ) := by ring
    exact pow_le_pow_left₀ (by positivity) hbase' 1000
  unfold taoPrimeTupleChangeLevelCollisionSum
  calc
    (∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        (4 * ((taoDyadicPrimeBand (P x j)).card : ℝ)⁻¹) ^ (1000 : ℕ)) ≤
      ∑ _j ∈ Finset.univ.erase (0 : Fin 1001),
        (16 * Real.log (taoZ x) /
          (taoZ x) ^ (9 / 10 : ℝ)) ^ (1000 : ℕ) := by
      exact Finset.sum_le_sum fun j _ => hterm j
    _ = 1000 * (16 * Real.log (taoZ x) /
        (taoZ x) ^ (9 / 10 : ℝ)) ^ (1000 : ℕ) := by simp

/-- Explicit source envelope for the summed reciprocal-band collisions. -/
def taoLargePrimeSourceBandReciprocalEnvelope (x : ℕ) : ℝ :=
  1001 * (4 * Real.log (taoZ x) / (taoZ x) ^ (9 / 10 : ℝ))

/-- Explicit source envelope for the summed eighth-power tail. -/
def taoLargePrimeSourceEighthPowerEnvelope (x : ℕ) : ℝ :=
  1000 * (((taoZ x) ^ (9 / 10 : ℝ)) ^ (-(8 : ℝ)))

/-- Explicit source envelope for the change-level collision tail. -/
def taoLargePrimeSourceChangeLevelEnvelope (x : ℕ) : ℝ :=
  1000 * (16 * Real.log (taoZ x) /
    (taoZ x) ^ (9 / 10 : ℝ)) ^ (1000 : ℕ)

/-- One-prime improved error envelope at dyadic modulus scale `R`. -/
def taoLargePrimeSourceSingleErrorEnvelope (x R : ℕ) : ℝ :=
  2 / (R : ℝ) * taoLargePrimeSourceBandReciprocalEnvelope x +
    taoLargePrimeSourceEighthPowerEnvelope x

/-- Joint two-prime improved error envelope at scales `R,S`. -/
def taoLargePrimeSourceJointErrorEnvelope (x R S : ℕ) : ℝ :=
  (4 / ((R : ℝ) * (S : ℝ))) *
      (2 * taoLargePrimeSourceBandReciprocalEnvelope x) +
    (2 : ℝ) ^ 999 *
      (4 * taoLargePrimeSourceEighthPowerEnvelope x +
        taoLargePrimeSourceChangeLevelEnvelope x)

/-- Covariance error envelope obtained after exact cancellation of the
one- and two-prime main terms. -/
def taoLargePrimeSourceCovarianceErrorEnvelope (x R S : ℕ) : ℝ :=
  taoLargePrimeSourceJointErrorEnvelope x R S +
    (2 / (R : ℝ)) * taoLargePrimeSourceSingleErrorEnvelope x S +
    (2 / (S : ℝ)) * taoLargePrimeSourceSingleErrorEnvelope x R +
    taoLargePrimeSourceSingleErrorEnvelope x R *
      taoLargePrimeSourceSingleErrorEnvelope x S

theorem taoLargePrimeSourceBandReciprocalEnvelope_nonneg (x : ℕ) :
    0 ≤ taoLargePrimeSourceBandReciprocalEnvelope x := by
  have hlog : 0 ≤ Real.log (taoZ x) := by
    rw [log_taoZ]
    positivity
  have hzpow : 0 ≤ (taoZ x) ^ (9 / 10 : ℝ) :=
    (Real.rpow_pos_of_pos (taoZ_pos x) _).le
  unfold taoLargePrimeSourceBandReciprocalEnvelope
  exact mul_nonneg (by norm_num)
    (div_nonneg (mul_nonneg (by norm_num) hlog) hzpow)

theorem taoLargePrimeSourceEighthPowerEnvelope_nonneg (x : ℕ) :
    0 ≤ taoLargePrimeSourceEighthPowerEnvelope x := by
  have hzpow : 0 ≤ (taoZ x) ^ (9 / 10 : ℝ) :=
    (Real.rpow_pos_of_pos (taoZ_pos x) _).le
  unfold taoLargePrimeSourceEighthPowerEnvelope
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg hzpow _)

theorem taoLargePrimeSourceChangeLevelEnvelope_nonneg (x : ℕ) :
    0 ≤ taoLargePrimeSourceChangeLevelEnvelope x := by
  have hlog : 0 ≤ Real.log (taoZ x) := by
    rw [log_taoZ]
    positivity
  have hzpow : 0 ≤ (taoZ x) ^ (9 / 10 : ℝ) :=
    (Real.rpow_pos_of_pos (taoZ_pos x) _).le
  have hbase : 0 ≤ 16 * Real.log (taoZ x) /
      (taoZ x) ^ (9 / 10 : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hlog) hzpow
  unfold taoLargePrimeSourceChangeLevelEnvelope
  exact mul_nonneg (by norm_num) (pow_nonneg hbase _)

theorem taoLargePrimeSourceSingleErrorEnvelope_nonneg (x R : ℕ) :
    0 ≤ taoLargePrimeSourceSingleErrorEnvelope x R := by
  unfold taoLargePrimeSourceSingleErrorEnvelope
  exact add_nonneg
    (mul_nonneg (by positivity)
      (taoLargePrimeSourceBandReciprocalEnvelope_nonneg x))
    (taoLargePrimeSourceEighthPowerEnvelope_nonneg x)

/-- The literal one-prime improved error is eventually bounded by the source
envelope, simultaneously for every dyadic modulus band. -/
theorem eventually_taoLargePrimeImprovedError_le_sourceEnvelope
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ R p : ℕ, 2 ≤ R →
      p ∈ taoDyadicPrimeBand R →
      taoLargePrimeImprovedError (P x) p ≤
        taoLargePrimeSourceSingleErrorEnvelope x R := by
  filter_upwards [eventually_taoPrimeTupleBandReciprocalSum_le_source hscale,
    eventually_taoPrimeTupleEighthPowerSum_le_source hscale] with x hU hV
  intro R p hR hp
  exact taoLargePrimeImprovedError_le_aggregate (P x) hR hp
    (taoLargePrimeSourceBandReciprocalEnvelope x)
    (taoLargePrimeSourceEighthPowerEnvelope x)
    (by simpa only [taoLargePrimeSourceBandReciprocalEnvelope] using hU)
    (by simpa only [taoLargePrimeSourceEighthPowerEnvelope] using hV)

/-- The literal two-prime joint improved error is eventually bounded by its
source envelope, uniformly over both dyadic bands. -/
theorem eventually_taoLargePrimeJointImprovedError_le_sourceEnvelope
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ R S p q : ℕ, 2 ≤ R → 2 ≤ S →
      p ∈ taoDyadicPrimeBand R → q ∈ taoDyadicPrimeBand S → p ≠ q →
      taoLargePrimeJointImprovedError (P x) p q ≤
        taoLargePrimeSourceJointErrorEnvelope x R S := by
  filter_upwards [eventually_taoPrimeTupleBandReciprocalSum_le_source hscale,
    eventually_taoPrimeTupleEighthPowerSum_le_source hscale,
    eventually_taoPrimeTupleChangeLevelCollisionSum_le_source hscale] with
      x hU hV hW
  intro R S p q hR hS hp hq hpq
  exact taoLargePrimeJointImprovedError_le_aggregate (P x)
    hR hS hp hq hpq
    (taoLargePrimeSourceBandReciprocalEnvelope x)
    (taoLargePrimeSourceEighthPowerEnvelope x)
    (taoLargePrimeSourceChangeLevelEnvelope x)
    (by simpa only [taoLargePrimeSourceBandReciprocalEnvelope] using hU)
    (by simpa only [taoLargePrimeSourceEighthPowerEnvelope] using hV)
    (by simpa only [taoLargePrimeSourceChangeLevelEnvelope] using hW)

/-- Source envelope for the exact covariance error, uniformly over every
ordered distinct-prime pair in two dyadic bands. -/
theorem eventually_taoLargePrimeCovarianceImprovedError_le_sourceEnvelope
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ R S p q : ℕ, 2 ≤ R → 2 ≤ S →
      p ∈ taoDyadicPrimeBand R → q ∈ taoDyadicPrimeBand S → p ≠ q →
      taoLargePrimeCovarianceImprovedError (P x) p q ≤
        taoLargePrimeSourceCovarianceErrorEnvelope x R S := by
  filter_upwards [eventually_taoLargePrimeImprovedError_le_sourceEnvelope hscale,
    eventually_taoLargePrimeJointImprovedError_le_sourceEnvelope hscale] with
      x hsingle hjoint
  intro R S p q hR hS hp hq hpq
  exact taoLargePrimeCovarianceImprovedError_le_of_uniform (P x)
    hR hS hp hq
    (taoLargePrimeSourceSingleErrorEnvelope x R)
    (taoLargePrimeSourceSingleErrorEnvelope x S)
    (taoLargePrimeSourceJointErrorEnvelope x R S)
    (taoLargePrimeSourceSingleErrorEnvelope_nonneg x R)
    (hsingle R p hR hp) (hsingle S q hS hq)
    (hjoint R S p q hR hS hp hq hpq)

end

end Tao2026
