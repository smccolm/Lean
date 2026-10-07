import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # A continuous real function with no interior zero stays in one closed half-line -/

namespace Dubon2026

open Set

theorem continuousOn_constant_sign_of_no_interior_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hz : ∀ x ∈ Ioo a b, f x ≠ 0) :
    (∀ x ∈ Icc a b, 0 ≤ f x) ∨ (∀ x ∈ Icc a b, f x ≤ 0) := by
  by_cases hn : ∃ x ∈ Icc a b, f x < 0
  · obtain ⟨x, hx, hxneg⟩ := hn
    right
    intro y hy
    by_contra h
    have hypos : 0 < f y := lt_of_not_ge h
    by_cases hxy : x ≤ y
    · obtain ⟨t, ht, hft⟩ := intermediate_value_Ioo hxy
        (hf.mono (Icc_subset_Icc hx.1 hy.2)) ⟨hxneg, hypos⟩
      exact hz t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩ hft
    · obtain ⟨t, ht, hft⟩ := intermediate_value_Ioo' (le_of_not_ge hxy)
        (hf.mono (Icc_subset_Icc hy.1 hx.2)) ⟨hxneg, hypos⟩
      exact hz t ⟨hy.1.trans_lt ht.1, ht.2.trans_le hx.2⟩ hft
  · left
    intro x hx
    exact le_of_not_gt (fun h => hn ⟨x, hx, h⟩)

end Dubon2026
