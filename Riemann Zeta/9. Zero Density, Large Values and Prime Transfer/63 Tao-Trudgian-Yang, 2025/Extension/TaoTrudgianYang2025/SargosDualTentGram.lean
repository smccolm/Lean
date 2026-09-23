import TaoTrudgianYang2025.SargosDualTentKernel

/-! Exact dual Gram integration and the lower weight of every counted pair. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem integrable_sargosTentPlanarIntegrand_complex {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun p : ℝ × ℝ => (sargosTentPlanarIntegrand S u v a b p : ℂ))
      (volume.prod volume) := by
  simp_rw [sargosTentPlanarIntegrand_eq_gram]
  exact integrable_finsetSum _ (fun q hq => integrable_sargosTentKernelTerm ha hb _ _)

theorem integrable_sargosTentPlanarIntegrand {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (sargosTentPlanarIntegrand S u v a b) (volume.prod volume) := by
  have h := (integrable_sargosTentPlanarIntegrand_complex S u v ha hb).re
  simpa only [Complex.ofReal_re] using h

theorem integral_sargosTentPlanarIntegrand_eq_gram {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ p : ℝ × ℝ, sargosTentPlanarIntegrand S u v a b p ∂(volume.prod volume)) =
      ∑ q ∈ S ×ˢ S,
        sargosSincKernel a (u q.1-u q.2)*sargosSincKernel b (v q.1-v q.2) := by
  apply Complex.ofReal_injective
  calc
    _ = ∫ p : ℝ × ℝ, (sargosTentPlanarIntegrand S u v a b p : ℂ)
        ∂(volume.prod volume) := integral_complex_ofReal.symm
    _ = ∑ q ∈ S ×ˢ S, ∫ p : ℝ × ℝ,
        sargosTentKernelTerm a b (u q.1-u q.2) (v q.1-v q.2) p
          ∂(volume.prod volume) := by
      simp_rw [sargosTentPlanarIntegrand_eq_gram]
      exact integral_finsetSum _ (fun q hq => integrable_sargosTentKernelTerm ha hb _ _)
    _ = ∑ q ∈ S ×ˢ S,
        (sargosSincKernel a (u q.1-u q.2) : ℂ)*(sargosSincKernel b (v q.1-v q.2) : ℂ) := by
      simp_rw [integral_sargosTentKernelTerm ha hb]
    _ = _ := by push_cast; rfl

theorem sargosNearPairs_weighted_card_le_gram {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : a*A ≤ 1/2) (hB : b*B ≤ 1/2) :
    (a*b/16)*((sargosNearPairs S u v A B).card : ℝ) ≤
      ∑ q ∈ S ×ˢ S,
        sargosSincKernel a (u q.1-u q.2)*sargosSincKernel b (v q.1-v q.2) := by
  classical
  calc
    _ = ∑ q ∈ sargosNearPairs S u v A B, a*b/16 := by simp; ring
    _ ≤ ∑ q ∈ sargosNearPairs S u v A B,
        sargosSincKernel a (u q.1-u q.2)*sargosSincKernel b (v q.1-v q.2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hc := (Finset.mem_filter.mp hq).2
      exact sargosSincKernel_rectangle_lower ha hb
        ((mul_le_mul_of_nonneg_left hc.1 ha.le).trans hA)
        ((mul_le_mul_of_nonneg_left hc.2 hb.le).trans hB)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact (Finset.mem_filter.mp hq).1
      · intro q hq hnq
        exact mul_nonneg (sargosSincKernel_nonneg ha.le _) (sargosSincKernel_nonneg hb.le _)

theorem sargosNearPairs_weighted_card_le_tentIntegral {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : a*A ≤ 1/2) (hB : b*B ≤ 1/2) :
    (a*b/16)*((sargosNearPairs S u v A B).card : ℝ) ≤
      ∫ p : ℝ × ℝ, sargosTentPlanarIntegrand S u v a b p ∂(volume.prod volume) := by
  rw [integral_sargosTentPlanarIntegrand_eq_gram S u v ha hb]
  exact sargosNearPairs_weighted_card_le_gram S u v ha hb hA hB

end TaoTrudgianYang2025
