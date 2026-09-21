import TaoTrudgianYang2025.AtkinsonFarRadical

/-!
# Far-height cancellation for the actual truncated gap majorant

The bound applies to both height orders and every far gap. The triangle
branch handles the large-curvature range rather than losing a linear gap
term. No full-block replacement of a shorter prefix is used.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem atkinsonOrderedPrefixGapMajorant_le_min_bProcess (M N : ℕ) (t u : ℝ) :
    atkinsonOrderedPrefixGapMajorant M N t u ≤ min (N:ℝ) (atkinsonPrefixBProcessMajorant M N t u) := by
  unfold atkinsonOrderedPrefixGapMajorant
  split_ifs
  · exact min_le_min le_rfl (min_le_left _ _)
  · exact le_rfl

theorem atkinsonOrderedPrefixGapMajorant_le_far {H t u : ℝ} {M : ℕ}
    (hH : 0 < H) (hHu : H ≤ u) (huH : u ≤ 2*H) (htu : u < t) (hM : 0 < M)
    (hfar : Real.sqrt (H*(M:ℝ)) ≤ t-u) :
    atkinsonOrderedPrefixGapMajorant M M t u ≤
      2000*Real.sqrt ((M:ℝ)*(t-u)/Real.sqrt (H*(M:ℝ))) := by
  have hb := atkinson_far_lambda_bounds hH hHu huH htu hM
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hR : 0 < Real.sqrt (H*(M:ℝ)) := by positivity
  have hupper := atkinsonIndexBProcessLambdaUpper_pos (N := M) (hH.trans_le hHu) htu hM
  exact (atkinsonOrderedPrefixGapMajorant_le_min_bProcess M M t u).trans
    (atkinson_far_min_bProcess hM0 hR hfar hb.1 hupper.le hb.2)

theorem atkinsonPrefixGapMajorant_le_far {H t u : ℝ} {M : ℕ}
    (hH : 0 < H) (htH : H ≤ t) (hHt : t ≤ 2*H)
    (huH : H ≤ u) (hHu : u ≤ 2*H) (hM : 0 < M)
    (hfar : Real.sqrt (H*(M:ℝ)) ≤ |t-u|) :
    atkinsonPrefixGapMajorant M M t u ≤
      2000*Real.sqrt ((M:ℝ)*|t-u|/Real.sqrt (H*(M:ℝ))) := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hR : 0 < Real.sqrt (H*(M:ℝ)) := by positivity
  have hne : t ≠ u := by
    intro h
    subst u
    simp only [sub_self, abs_zero] at hfar
    linarith
  unfold atkinsonPrefixGapMajorant
  rw [if_neg hne]
  rcases lt_or_gt_of_ne hne with htu | hut
  · simp only [max_eq_right htu.le, min_eq_left htu.le,
      abs_of_neg (sub_neg.mpr htu), neg_sub] at hfar ⊢
    exact atkinsonOrderedPrefixGapMajorant_le_far hH htH hHt htu hM hfar
  · simp only [max_eq_left hut.le, min_eq_right hut.le,
      abs_of_pos (sub_pos.mpr hut)] at hfar ⊢
    exact atkinsonOrderedPrefixGapMajorant_le_far hH huH hHu hut hM hfar

end TaoTrudgianYang2025
