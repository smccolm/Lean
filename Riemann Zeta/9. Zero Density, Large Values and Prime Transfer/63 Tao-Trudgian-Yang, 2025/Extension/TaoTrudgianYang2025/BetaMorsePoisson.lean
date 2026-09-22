import TaoTrudgianYang2025.BetaMorseFourier

/-!
# Original closed source sums enter the actual quadratic transform

One cutoff is constructed before T. Every mode whose frequency slope
lies in the actual derivative image is transformed with that same
cutoff, with proved integrability and a uniform amplitude bound.
Nonstationary modes and stationary integral errors remain separate.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem modelPhase_closed_interval_poisson_morse
    {F : ℝ → ℝ} {σ δ N : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hN : 0 < N)
    {a b : ℕ} (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ u : ℝ, 0 ≤ χ u ∧ χ u ≤ 1) ∧
      (∀ n : ℤ, χ ((n : ℝ)/N) =
        if n ∈ modelPhaseInteriorIndices N a b then 1 else 0) ∧
      ∀ T : ℝ, 0 < T →
        Summable (fun r : ℤ => ‖modelPhaseFourierMode χ F T N r‖) ∧
        ‖exponentialSumAt F T N a b -
          ∑' r : ℤ, modelPhaseFourierMode χ F T N r‖ ≤ 2 ∧
        ∀ r : ℤ, (r : ℝ)*N/T ∈ modelPhaseSlopeRange F →
          modelPhaseFourierMode χ F T N r =
            (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
              modelPhaseMorseWeightedIntegral χ F T ((r : ℝ)*N/T) ∧
          IntegrableOn (fun z => (modelPhaseMorseAmplitude χ F ((r : ℝ)*N/T) z : ℂ)*
            (𝐞 (-(T/2)*z^2) : ℂ)) (modelPhaseMorseRange F ((r : ℝ)*N/T)) ∧
          ∀ z ∈ modelPhaseMorseRange F ((r : ℝ)*N/T),
            0 ≤ modelPhaseMorseAmplitude χ F ((r : ℝ)*N/T) z ∧
            modelPhaseMorseAmplitude χ F ((r : ℝ)*N/T) z ≤
              Real.sqrt (σ+1)/modelPhaseCurvatureLower σ := by
  classical
  obtain ⟨χ,hχ,hs,hcompact,hbounds,hvalues⟩ := exists_modelPhase_interior_cutoff hN a b
  refine ⟨χ,hχ,hs,hcompact,hbounds,hvalues,?_⟩
  intro T hT
  refine ⟨summable_norm_modelPhaseFourierMode hχ hs hF hN T,?_,?_⟩
  · have hsource : (∑' n : ℤ, modelPhaseWeightedKernel χ F T N n) =
        ∑ n ∈ modelPhaseInteriorIndices N a b, (𝐞 (T*F ((n : ℝ)/N)) : ℂ) := by
      rw [tsum_eq_sum (s := modelPhaseInteriorIndices N a b) (fun n hn => by
        simp only [modelPhaseWeightedKernel,hvalues n,if_neg hn,Complex.ofReal_zero,zero_mul])]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [modelPhaseWeightedKernel,hvalues n,if_pos hn,Complex.ofReal_one,one_mul]
    rw [← modelPhase_weighted_poisson hχ hs hF hN T,
      ← modelPhaseWeightedKernel_tsum_eq_finite hs hN T,hsource,exponentialSumAt_eq_int_sum]
    exact norm_modelPhase_full_sub_interior_le_two F T
      (by exact_mod_cast ha) (by exact_mod_cast hb)
  · intro r hr
    refine ⟨modelPhaseFourierMode_morse hs hσ hδ hF hT.ne' hN hr,
      modelPhaseMorseWeightedIntegrand_integrableOn hχ.continuous hσ hδ hF hr T,?_⟩
    intro z hz
    refine ⟨modelPhaseMorseAmplitude_nonneg hσ hδ hF hr hz (fun u _ => (hbounds u).1),?_⟩
    have h := abs_modelPhaseMorseAmplitude_le hσ hδ hF hr hz (by norm_num : (0 : ℝ) ≤ 1)
      (fun u _ => by rw [abs_of_nonneg (hbounds u).1]; exact (hbounds u).2)
    exact (le_abs_self _).trans (by simpa only [one_mul] using h)

end TaoTrudgianYang2025

