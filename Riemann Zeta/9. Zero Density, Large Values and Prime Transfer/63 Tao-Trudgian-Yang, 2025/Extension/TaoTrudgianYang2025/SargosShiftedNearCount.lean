import TaoTrudgianYang2025.SargosShiftedTentGram

/-! Actual shifted near-pair cardinalities bounded by central moments. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosShiftedNearPairs_weighted_card_le_gram {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : a*A ≤ 1/2) (hB : b*B ≤ 1/2) (c d : ℝ) :
    (a*b/16)*((sargosShiftedNearPairs S u v c d A B).card : ℝ) ≤
      ∑ q ∈ S ×ˢ S,
        sargosSincKernel a (u q.1-u q.2-c)*sargosSincKernel b (v q.1-v q.2-d) := by
  classical
  calc
    _ = ∑ q ∈ sargosShiftedNearPairs S u v c d A B, a*b/16 := by simp; ring
    _ ≤ ∑ q ∈ sargosShiftedNearPairs S u v c d A B,
        sargosSincKernel a (u q.1-u q.2-c)*sargosSincKernel b (v q.1-v q.2-d) := by
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
      · intro q _hq _hnq
        exact mul_nonneg (sargosSincKernel_nonneg ha.le _) (sargosSincKernel_nonneg hb.le _)

theorem sargosShiftedNearPairs_card_le_central {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {Δ μ : ℝ} (hΔ : 0 < Δ) (hμ : 0 < μ)
    (c d : ℝ) :
    ((sargosShiftedNearPairs S u v c d (1/Δ) (1/μ)).card : ℝ) ≤
      (64/(Δ*μ))*(∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
        ‖sargosPlanarSum S (fun _ => 1) u v α γ‖^2) := by
  have hA : (Δ/2)*(1/Δ) ≤ 1/2 := by field_simp; norm_num
  have hB : (μ/2)*(1/μ) ≤ 1/2 := by field_simp; norm_num
  have h := (sargosShiftedNearPairs_weighted_card_le_gram S u v
    (by positivity : 0 < Δ/2) (by positivity : 0 < μ/2) hA hB c d).trans
    ((sargos_shifted_tent_gram_le_integral S u v (by positivity) (by positivity) c d).trans
      (sargosTentPlanarIntegral_le_central S u v (by positivity) (by positivity)))
  have he : (Δ/2)*(μ/2)/16 = Δ*μ/64 := by ring
  rw [he] at h
  have hpos : 0 < Δ*μ/64 := by positivity
  have hd : ((sargosShiftedNearPairs S u v c d (1/Δ) (1/μ)).card : ℝ) ≤
      (∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
        ‖sargosPlanarSum S (fun _ => 1) u v α γ‖^2)/(Δ*μ/64) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using h)
  convert hd using 1
  field_simp

end TaoTrudgianYang2025

