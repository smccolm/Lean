import Dubon2026.PrimeEnergyMass
import Dubon2026.EnergyBandGrowth
import Dubon2026.WeightedPrimeEnergy
import Dubon2026.LevelOneSelfTwist

namespace Dubon2026
open Filter Set MeasureTheory
open scoped Topology
noncomputable section

private theorem band_coefficient_comparability (a : ℕ → ℂ) :
    PrimeCoefficientComparability a (maximalEnergyBand (fun p => ‖a p‖^2)) (1/2) := by
  let B := maximalEnergyBand (fun p => ‖a p‖^2)
  have hB : IsolatedPrimeBlocks B := fun N p hp =>
    mem_dyadicPrimes.mp (maximalEnergyBand_subset _ N hp)
  let b := fun _ : ℕ => (1 : ℂ)
  have hb : ∀ᶠ N in atTop, ∀ p ∈ B N, 1 ≤ ‖b p‖ ∧ ‖b p‖ ≤ 2 :=
    Eventually.of_forall fun _ _ _ => by norm_num [b]
  have hc := primeCoefficientComparability_of_selected_bounds hB hb (1/2)
  intro l u hlu hu
  obtain ⟨K, hK, hcomp⟩ := hc l u hlu hu
  refine ⟨2*K, by linarith, ?_⟩
  filter_upwards [hcomp] with N hN
  intro σ hσ p hp q hq
  have hratio := hN σ hσ p hp q hq
  simp only [b, norm_one, one_mul] at hratio
  obtain ⟨hq0,hpq⟩ := maximalEnergyBand_comparable hp hq
  obtain ⟨hp0,hqp⟩ := maximalEnergyBand_comparable hq hp
  change 0 < ‖a q‖^2 at hq0
  change ‖a p‖^2 ≤ 2 * ‖a q‖^2 at hpq
  change ‖a q‖^2 ≤ 2 * ‖a p‖^2 at hqp
  have hpos : 0 < ‖a q‖ := lt_of_le_of_ne (norm_nonneg _) (by rintro h; rw [← h] at hq0; norm_num at hq0)
  have hpq' : ‖a p‖ ≤ 2 * ‖a q‖ := by
    apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity)
    nlinarith [sq_nonneg ‖a q‖]
  have hqp' : ‖a q‖ ≤ 2 * ‖a p‖ := by
    apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity)
    nlinarith [sq_nonneg ‖a p‖]
  have hl : (1/2 : ℝ) ≤ ‖a p‖ / ‖a q‖ := (le_div_iff₀ hpos).mpr (by linarith)
  have hh : ‖a p‖ / ‖a q‖ ≤ 2 := (div_le_iff₀ hpos).mpr hpq'
  rw [mul_div_mul_comm]
  refine ⟨?_, mul_le_mul hh hratio.2 (by positivity) (by norm_num)⟩
  simpa only [mul_inv_rev, one_div, mul_comm] using
    mul_le_mul hl hratio.1 (inv_nonneg.mpr (by linarith)) (div_nonneg (norm_nonneg _) hpos.le)

/-- Both concentration lines and the fixed-length vertical count for the original primitive form.
Only the weight restriction is required. The prime block is chosen by its squared mass. -/
theorem primitive_concentration {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    TendstoLocallyUniformly (normalizedJessen (normalizedCuspCoefficients f.toCuspForm))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (normalizedCuspCoefficients_one f.toCuspForm f.normalized)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    TendstoLocallyUniformly (normalizedJessen (cuspCoefficients f.toCuspForm))
      (fun σ => max ((k : ℝ) / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (a := cuspCoefficients f.toCuspForm) f.normalized) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (cuspCoefficients f.toCuspForm) N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex (cuspCoefficients f.toCuspForm) N)) *
        ((verticalZeroCount (cuspCoefficients f.toCuspForm) N hN (f.normalized.trans_ne one_ne_zero) l u T : ℝ) /
          (2 * T))) atTop
        (𝓝 (((jessenProbability (a := cuspCoefficients f.toCuspForm) f.normalized N : Measure ℝ) (Ioo l u)).toReal))) := by
  let a := normalizedCuspCoefficients f.toCuspForm
  let e := fun n => ‖a n‖^2
  let B := maximalEnergyBand e
  obtain ⟨C,hC,hu⟩ := exists_prefix_square_bound_of_mean (tendsto_cusp_square_mean f.toCuspForm (by omega))
  obtain ⟨hpos,hlog⟩ := maximalEnergyBand_growth (e := e) (fun n => sq_nonneg _) hC hu
    (primitive_dyadic_prime_energy_lower f hk)
  obtain ⟨D,hD,hp⟩ := exists_normalized_cusp_coefficient_three_fifths f.toCuspForm hk
  have hc := maximalEnergyBand_card_growth hD hp hpos hlog
  have hB : IsolatedPrimeBlocks B := fun N p hp => mem_dyadicPrimes.mp (maximalEnergyBand_subset e N hp)
  have henergy := (tendstoLocallyUniformly_weighted_prime_energy hB (a := a) hpos hlog).tendstoLocallyUniformlyOn
    (s := Iio (1/2))
  exact primitive_concentration_of_isolated_block f (by omega) hB hc (band_coefficient_comparability a) henergy

/-- Dubon's level-one corollary on the Fourier coefficients supplied by the
normalized Hecke eigenform. The native level-one bridge proves primitivity. -/
theorem level_one_eigenform_concentration {k : ℤ} (hk : 2 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : cuspCoefficients f 1 = 1) (he : IsCuspHeckeEigenform f) :
    TendstoLocallyUniformly (normalizedJessen (normalizedCuspCoefficients f))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (normalizedCuspCoefficients_one f hf)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    TendstoLocallyUniformly (normalizedJessen (cuspCoefficients f))
      (fun σ => max ((k : ℝ) / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (a := cuspCoefficients f) hf) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have h := primitive_concentration (primitiveCuspFormLevelOne f hf he) hk
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

end
end Dubon2026
