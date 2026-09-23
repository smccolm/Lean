import TaoTrudgianYang2025.SargosCProcessHighScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform initial-scale thresholds derived from the quantitative high-height bounds. -/

noncomputable section

open Filter Topology

namespace TaoTrudgianYang2025

theorem sargosCProcessScale_high_smallness {k l T N : ℝ}
    (hkl : InExponentPairTriangle k l) (hN : 1 ≤ N)
    (hhigh : N^(sargosCProcessThreshold k l) ≤ T) :
    (sargosCProcessScale k l T N)^3/N^2 ≤ N^(-3/100:ℝ) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hTp : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hhigh
  have hR := sargosCProcessScale_pos (k := k) (l := l) hTp hNp
  have hc := sargosCProcessScale_high_cap hkl hN hhigh
  calc
    _ ≤ (N^(2/3-1/100:ℝ))^3/N^2 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hR.le hc 3) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hNp.le,← Real.rpow_natCast N 2,← Real.rpow_sub hNp]
      norm_num

theorem sargosCProcess_initial_threshold {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      N^(-3/100:ℝ) ≤ η ∧ 8 ≤ N^(1/3:ℝ) := by
  have hlim : Tendsto (fun N : ℝ => N^(-3/100:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/100)
  obtain ⟨A,hA⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 η hη)
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).eventually (eventually_ge_atTop 8))
  refine ⟨max 1 (max A B),le_max_left _ _,?_⟩
  intro N hN
  exact ⟨(hA N ((le_max_left A B).trans ((le_max_right _ _).trans hN))).le,
    hB N ((le_max_right A B).trans ((le_max_right _ _).trans hN))⟩

theorem sargosCProcessScale_high_admissibility {k l η : ℝ}
    (hkl : InExponentPairTriangle k l) (hη : 0 < η) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ (T N : ℝ), N₀ ≤ N →
      N^(sargosCProcessThreshold k l) ≤ T →
      (sargosCProcessScale k l T N)^3/N^2 ≤ η ∧
        8*N^4 ≤ T*(sargosCProcessScale k l T N)^3 := by
  obtain ⟨N₀,hN₀,hthreshold⟩ := sargosCProcess_initial_threshold hη
  refine ⟨N₀,hN₀,?_⟩
  intro T N hN hhigh
  have hN1 := hN₀.trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  obtain ⟨hsmall,hlarge⟩ := hthreshold N hN
  refine ⟨(sargosCProcessScale_high_smallness hkl hN1 hhigh).trans hsmall,?_⟩
  calc
    _ ≤ N^(1/3:ℝ)*N^4 := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = N^(13/3:ℝ) := by
      rw [← Real.rpow_natCast N 4,← Real.rpow_add hNp]
      norm_num
    _ ≤ _ := sargosCProcessScale_high_secondary hkl hN1 hhigh

end TaoTrudgianYang2025
