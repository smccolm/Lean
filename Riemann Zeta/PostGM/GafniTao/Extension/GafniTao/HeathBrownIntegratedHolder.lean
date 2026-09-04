import GafniTao.HeathBrownHolder
import GafniTao.FordMomentInterpolation

/-!
# Heath-Brown's integrated Weyl-sum bound

This specializes the three-factor Hölder inequality to the literal Weyl sum
and literal coefficient-cell multiplicity.  Its conclusion contains the
actual Vinogradov solution count and the actual derivative-pair count from
Heath-Brown's Lemma 2.
-/

open MeasureTheory
open scoped ENNReal

namespace GafniTao

noncomputable section

theorem integrable_heathBrownNu_sq
    (N k H : ℕ) (f : ℝ → ℝ) :
    Integrable (fun α => (heathBrownNu N k H f α) ^ 2)
      (heathBrownCoefficientMeasure k) := by
  have hsum : Integrable
      (fun α => ∑ p ∈ (heathBrownInteriorIndices N H).product
          (heathBrownInteriorIndices N H),
        heathBrownCellIntersectionIndicator k H f p α)
      (heathBrownCoefficientMeasure k) :=
    integrable_finsetSum _ fun p hp =>
      integrable_heathBrownCellIntersectionIndicator k H f p
  apply hsum.congr
  filter_upwards [] with α
  exact (heathBrownNu_sq_eq_pair_sum N k H f α).symm

theorem lintegral_heathBrownNu_eq
    (N k H : ℕ) (hH : 2 ≤ H) (f : ℝ → ℝ) :
    ∫⁻ α, ENNReal.ofReal (heathBrownNu N k H f α)
        ∂(heathBrownCoefficientMeasure k) =
      ENNReal.ofReal
        (((N - H : ℕ) : ℝ) *
          ((2 : ℝ) ^ (k - 1) *
            (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) := by
  rw [← integral_heathBrownNu_exact N k H hH f]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_heathBrownNu N k H f)
    (Filter.Eventually.of_forall fun α =>
      heathBrownNu_nonneg N k H f α)).symm

theorem lintegral_heathBrownNu_sq_le
    (N k H : ℕ) (hH : 2 ≤ H) (f : ℝ → ℝ) :
    ∫⁻ α, (ENNReal.ofReal (heathBrownNu N k H f α)) ^ 2
        ∂(heathBrownCoefficientMeasure k) ≤
      ENNReal.ofReal
        (((heathBrownPairCount N k H f).card : ℝ) *
          ((2 : ℝ) ^ (k - 1) *
            (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) := by
  calc
    (∫⁻ α, (ENNReal.ofReal (heathBrownNu N k H f α)) ^ 2
        ∂(heathBrownCoefficientMeasure k)) =
        ∫⁻ α, ENNReal.ofReal ((heathBrownNu N k H f α) ^ 2)
          ∂(heathBrownCoefficientMeasure k) := by
      apply lintegral_congr
      intro α
      rw [ENNReal.ofReal_pow (heathBrownNu_nonneg N k H f α)]
    _ =
        ENNReal.ofReal
          (∫ α, (heathBrownNu N k H f α) ^ 2
            ∂(heathBrownCoefficientMeasure k)) := by
      exact (ofReal_integral_eq_lintegral_ofReal
        (integrable_heathBrownNu_sq N k H f)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (integral_heathBrownNu_sq_source_bound N k H hH f)

/-- The literal `I(Q)` estimate in Heath-Brown Lemma 1.  The three factors
on the right are respectively `J_{s,k-1}(H)`, the source pair count
`mathcal N`, and the number of interior source indices, each with the exact
coefficient-cell volume. -/
theorem heathBrown_integratedWeyl_le_source_moments
    (N k H : ℕ) (hH : 2 ≤ H) (f : ℝ → ℝ)
    {Q s : ℕ} (hQH : Q ≤ H) (hs : 1 ≤ s) :
    ∫⁻ α : HeathBrownCoefficientTorus k,
        ENNReal.ofReal ‖heathBrownWeylSum k Q α‖ *
          ENNReal.ofReal (heathBrownNu N k H f α)
        ∂(heathBrownCoefficientMeasure k) ≤
      (fordVinogradovMomentNat s (k - 1) H : ENNReal) ^
          (1 / (2 * (s : ℝ))) *
        ENNReal.ofReal
          (((heathBrownPairCount N k H f).card : ℝ) *
            ((2 : ℝ) ^ (k - 1) *
              (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) ^
          (1 / (2 * (s : ℝ))) *
        ENNReal.ofReal
          (((N - H : ℕ) : ℝ) *
            ((2 : ℝ) ^ (k - 1) *
              (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) ^
          (1 - 1 / (s : ℝ)) := by
  let A : HeathBrownCoefficientTorus k → ENNReal := fun α =>
    ENNReal.ofReal ‖heathBrownWeylSum k Q α‖
  let B : HeathBrownCoefficientTorus k → ENNReal := fun α =>
    ENNReal.ofReal (heathBrownNu N k H f α)
  have hA : AEMeasurable A (heathBrownCoefficientMeasure k) := by
    exact (ENNReal.continuous_ofReal.comp
      (continuous_fordVinogradovWeylSum (k - 1) Q).norm).aemeasurable
  have hB : AEMeasurable B (heathBrownCoefficientMeasure k) := by
    exact (integrable_heathBrownNu N k H f).aemeasurable.ennreal_ofReal
  have hholder := heathBrown_lintegral_mul_le_three_moments hA hB hs
  have hAI : (∫⁻ α, A α ^ (2 * s)
      ∂(heathBrownCoefficientMeasure k)) =
      (fordVinogradovMomentNat s (k - 1) Q : ENNReal) := by
    exact ford_vinogradov_lintegral_mean_eq s (k - 1) Q
  have hBI : (∫⁻ α, B α ∂(heathBrownCoefficientMeasure k)) =
      ENNReal.ofReal
        (((N - H : ℕ) : ℝ) *
          ((2 : ℝ) ^ (k - 1) *
            (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) :=
    lintegral_heathBrownNu_eq N k H hH f
  have hBII : (∫⁻ α, B α ^ 2 ∂(heathBrownCoefficientMeasure k)) ≤
      ENNReal.ofReal
        (((heathBrownPairCount N k H f).card : ℝ) *
          ((2 : ℝ) ^ (k - 1) *
            (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) :=
    lintegral_heathBrownNu_sq_le N k H hH f
  change (∫⁻ α, A α * B α ∂(heathBrownCoefficientMeasure k)) ≤ _
  rw [hAI, hBI] at hholder
  calc
    (∫⁻ α, A α * B α ∂(heathBrownCoefficientMeasure k)) ≤ _ := hholder
    _ ≤ _ := by
      gcongr
      · exact_mod_cast fordVinogradovMomentNat_mono s (k - 1) hQH

#print axioms integrable_heathBrownNu_sq
#print axioms lintegral_heathBrownNu_eq
#print axioms lintegral_heathBrownNu_sq_le
#print axioms heathBrown_integratedWeyl_le_source_moments

end

end GafniTao
