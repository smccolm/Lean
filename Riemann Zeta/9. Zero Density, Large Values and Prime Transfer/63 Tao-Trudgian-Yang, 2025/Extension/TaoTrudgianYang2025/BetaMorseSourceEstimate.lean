import TaoTrudgianYang2025.BetaMorseStationaryEstimate

/-!
# Original closed source sums with proved stationary-mode errors

The original lattice cutoff is chosen before sigma and the phase. Its
stationary constants precede F and T. Their dependence on that fixed
cutoff is explicit; no uniform lattice-margin budget is claimed here.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem modelPhase_closed_interval_poisson_stationary
    {N : ℝ} (hN : 0 < N) {a b : ℕ}
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ u : ℝ, 0 ≤ χ u ∧ χ u ≤ 1) ∧
      (∀ n : ℤ, χ ((n : ℝ)/N) =
        if n ∈ modelPhaseInteriorIndices N a b then 1 else 0) ∧
      ∀ σ : ℝ, 0 < σ → ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (δ : ℝ),
          δ ≤ min (modelPhaseCurvatureLower σ) 1 →
          IsApproximateModelPhaseFunction F σ P δ →
          ∀ T : ℝ, 0 < T →
            Summable (fun r : ℤ => ‖modelPhaseFourierMode χ F T N r‖) ∧
            ‖exponentialSumAt F T N a b-∑' r : ℤ, modelPhaseFourierMode χ F T N r‖ ≤ 2 ∧
            ∀ r : ℤ, (r : ℝ)*N/T ∈ modelPhaseSlopeRange F →
              ‖modelPhaseFourierMode χ F T N r-
                (χ (modelPhaseInverseSlope F ((r : ℝ)*N/T)) : ℂ)*
                  modelPhaseStationaryMainTerm F T N r‖ ≤ C*N/T := by
  classical
  obtain ⟨χ,hχ,hs,hcompact,hbounds,hvalues⟩ := exists_modelPhase_interior_cutoff hN a b
  refine ⟨χ,hχ,hs,hcompact,hbounds,hvalues,?_⟩
  intro σ hσ
  obtain ⟨P,hP,C,hC,herror⟩ := modelPhaseFourierMode_stationary_uniform hχ hs hσ
  refine ⟨P,hP,C,hC,?_⟩
  intro F δ hδ hF T hT
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
    exact herror F δ T N r hδ hF hT hN hr

end TaoTrudgianYang2025
