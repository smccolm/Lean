import Tao2026.BadIntervalLargePrimeCrudeNormalize
import Tao2026.ExceptionalCharacterNormalization
import Tao2026.BadIntervalSourceScales

/-!
# PNT specialization of the large-prime crude bounds

This module gives `P_j = z^{1+o(1)}` a precise sequence-level meaning for the
1001 prime-tuple scales.  The dyadic prime number theorem then supplies one
common band loss `4 log z`, uniformly over all coordinates.  Substitution into
the finite normalization theorems proves explicit source-scale versions of
the crude clauses in Propositions 6.7(i) and 6.8(i).
-/

namespace Tao2026

open Filter Topology

noncomputable section

/-- Exact sequence contract for the paper's statement that all 1001 dyadic
coordinate scales satisfy `P_j = z^{1+o(1)}`. -/
structure TaoPrimeTupleSourceScaleFamily
    (P : ℕ → Fin 1001 → ℕ) : Prop where
  tendsto_scale : ∀ j, Tendsto (fun x => P x j) atTop atTop
  log_ratio : ∀ j,
    Tendsto (fun x => Real.log (P x j : ℝ) / Real.log (taoZ x))
      atTop (𝓝 1)

/-- Uniform PNT normalization for every coordinate in a source-scale family.
The factor four consists of the concrete PNT loss two and the eventual
comparison `log P_j ≤ 2 log z`. -/
theorem eventually_taoPrimeTupleSourceScale_band_normalization
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      (P x j : ℝ) ≤ 4 * Real.log (taoZ x) *
        ((taoDyadicPrimeBand (P x j)).card : ℝ) := by
  have hone : ∀ j : Fin 1001, ∀ᶠ x : ℕ in atTop,
      (1 : ℝ) < P x j := fun j =>
    (tendsto_natCast_atTop_atTop.comp (hscale.tendsto_scale j)).eventually
      (eventually_gt_atTop (1 : ℝ))
  have hpnt : ∀ j : Fin 1001, ∀ᶠ x : ℕ in atTop,
      (P x j : ℝ) / (2 * Real.log (P x j)) ≤
        ((taoDyadicPrimeBand (P x j)).card : ℝ) := fun j =>
    (hscale.tendsto_scale j).eventually
      eventually_nat_div_two_log_le_card_taoDyadicPrimeBand
  have hratio : ∀ j : Fin 1001, ∀ᶠ x : ℕ in atTop,
      Real.log (P x j : ℝ) / Real.log (taoZ x) < 2 := fun j =>
    (hscale.log_ratio j).eventually (Iio_mem_nhds (by norm_num))
  have hlogz : ∀ᶠ x : ℕ in atTop, 0 < Real.log (taoZ x) :=
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)) |>.mono
      (fun _ hx => Real.log_pos hx)
  have hall : ∀ᶠ x : ℕ in atTop, ∀ j ∈ (Finset.univ : Finset (Fin 1001)),
      (P x j : ℝ) ≤ 4 * Real.log (taoZ x) *
        ((taoDyadicPrimeBand (P x j)).card : ℝ) := by
    rw [Filter.eventually_all_finset]
    intro j hj
    filter_upwards [hone j, hpnt j, hratio j, hlogz] with x hPone hPNT hr hz
    have hlogP : 0 < Real.log (P x j : ℝ) := Real.log_pos hPone
    have hlogPle : Real.log (P x j : ℝ) ≤ 2 * Real.log (taoZ x) :=
      (div_le_iff₀ hz).mp hr.le
    have hcard : 0 ≤ ((taoDyadicPrimeBand (P x j)).card : ℝ) := by positivity
    calc
      (P x j : ℝ) ≤
          ((taoDyadicPrimeBand (P x j)).card : ℝ) *
            (2 * Real.log (P x j : ℝ)) :=
        (div_le_iff₀ (mul_pos (by norm_num) hlogP)).mp hPNT
      _ ≤ ((taoDyadicPrimeBand (P x j)).card : ℝ) *
          (4 * Real.log (taoZ x)) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hcard
      _ = 4 * Real.log (taoZ x) *
          ((taoDyadicPrimeBand (P x j)).card : ℝ) := by ring
  simpa using hall

/-- All dyadic bands in a source-scale family are eventually nonempty,
simultaneously over the finite coordinate type. -/
theorem eventually_taoPrimeTupleSourceScale_bands_nonempty
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      (taoDyadicPrimeBand (P x j)).Nonempty := by
  have hj : ∀ j : Fin 1001, ∀ᶠ x : ℕ in atTop,
      (taoDyadicPrimeBand (P x j)).Nonempty := fun j =>
    (hscale.tendsto_scale j).eventually eventually_taoDyadicPrimeBand_nonempty
  have hall : ∀ᶠ x : ℕ in atTop,
      ∀ j ∈ (Finset.univ : Finset (Fin 1001)),
        (taoDyadicPrimeBand (P x j)).Nonempty := by
    rw [Filter.eventually_all_finset]
    intro j hjmem
    exact hj j
  simpa using hall

/-- Explicit source-scale form of Proposition 6.7(i).  The remaining
modulus/product comparison is stated as the exact eventual arithmetic fact
needed by the finite fiber theorem. -/
theorem eventually_taoLargePrimeProbability_le_crude_source
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (m' : ℕ → ℕ) (a : ℕ → ℕ × ℕ) (j₁ j₂ : Fin 1001)
    (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) (hj : j₁ ≠ j₂)
    (hp : ∀ᶠ x : ℕ in atTop, Nat.Prime (a x).2)
    (hpl : ∀ᶠ x : ℕ in atTop, ¬(a x).2 ∣ (a x).1)
    (hqU : ∀ᶠ x : ℕ in atTop,
      (a x).2 ≤ (2 * P x j₁) * (2 * P x j₂)) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
        taoLargePrimeProbability (P x) hP (m' x) (a x) ≤
          256 * Real.log (taoZ x) ^ 2 / ((a x).2 : ℝ) := by
  filter_upwards [eventually_taoPrimeTupleSourceScale_band_normalization hscale,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    hp, hpl, hqU] with x hband hz hpX hplX hqUX
  intro hP
  have hraw := taoLargePrimeProbability_le_crude_logScale_pair
    (P x) hP (m' x) (a x) j₁ j₂ hj₁ hj₂ hj hpX hplX
      (4 * Real.log (taoZ x))
      (mul_nonneg (by norm_num) (Real.log_pos hz).le)
      (hband j₁) (hband j₂) hqUX
  convert hraw using 1
  all_goals ring

/-- Explicit source-scale form of Proposition 6.8(i), with the exact eventual
product-modulus comparison exposed for the subsequent dyadic-scale consumer. -/
theorem eventually_taoLargePrimeJointProbability_le_crude_source
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (m' : ℕ → ℕ) (a b : ℕ → ℕ × ℕ) (j₁ j₂ j₃ : Fin 1001)
    (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) (hj₃ : j₃ ≠ 0)
    (h₁₂ : j₁ ≠ j₂) (h₁₃ : j₁ ≠ j₃) (h₂₃ : j₂ ≠ j₃)
    (hp : ∀ᶠ x : ℕ in atTop, Nat.Prime (a x).2)
    (hq : ∀ᶠ x : ℕ in atTop, Nat.Prime (b x).2)
    (hpq : ∀ᶠ x : ℕ in atTop, (a x).2 ≠ (b x).2)
    (hpa : ∀ᶠ x : ℕ in atTop, ¬(a x).2 ∣ (a x).1)
    (hqb : ∀ᶠ x : ℕ in atTop, ¬(b x).2 ∣ (b x).1)
    (hqU : ∀ᶠ x : ℕ in atTop, (a x).2 * (b x).2 ≤
      ((2 * P x j₁) * (2 * P x j₂)) * (2 * P x j₃)) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
        taoLargePrimeJointProbability (P x) hP (m' x) (a x) (b x) ≤
          6144 * Real.log (taoZ x) ^ 3 /
            (((a x).2 : ℝ) * ((b x).2 : ℝ)) := by
  filter_upwards [eventually_taoPrimeTupleSourceScale_band_normalization hscale,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    hp, hq, hpq, hpa, hqb, hqU] with
      x hband hz hpX hqX hpqX hpaX hqbX hqUX
  intro hP
  have hraw := taoLargePrimeJointProbability_le_crude_logScale_triple
    (P x) hP (m' x) (a x) (b x) j₁ j₂ j₃
      hj₁ hj₂ hj₃ h₁₂ h₁₃ h₂₃ hpX hqX hpqX hpaX hqbX
      (4 * Real.log (taoZ x))
      (mul_nonneg (by norm_num) (Real.log_pos hz).le)
      (hband j₁) (hband j₂) (hband j₃) hqUX
  convert hraw using 1
  all_goals ring

end

end Tao2026
