import TaoTrudgianYang2025.SargosPlanarIntegral

/-!
# Kernel-weighted planar mean square bounded by the actual near-pair count

Coefficients are arbitrary complex numbers of norm at most one on the
finite source set. The integral estimate is derived from the Gram
expansion and exact compact Fourier support, not assumed as input.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

theorem norm_sargosPlanarGramTerm_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z₁ z₂ : ℂ} (hz₁ : ‖z₁‖ ≤ 1) (hz₂ : ‖z₂‖ ≤ 1)
    (c d ξ η : ℝ) :
    ‖(z₁*conj z₂)*(∫ α : ℝ, ∫ γ : ℝ, sargosPlanarKernelTerm a b c d ξ η α γ)‖ ≤
      if |ξ| ≤ a ∧ |η| ≤ b then 1 else 0 := by
  classical
  by_cases h : |ξ| ≤ a ∧ |η| ≤ b
  · rw [if_pos h,norm_mul]
    have hz : ‖z₁*conj z₂‖ ≤ 1 := by
      rw [norm_mul,Complex.norm_conj]
      nlinarith [norm_nonneg z₁,norm_nonneg z₂]
    have hk := norm_integral_sargosPlanarKernelTerm_le_one ha hb c d ξ η
    exact (mul_le_mul hz hk (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · have hcut : a ≤ |ξ| ∨ b ≤ |η| := by
      by_cases hx : |ξ| ≤ a
      · right
        have hy : ¬|η| ≤ b := fun hy => h ⟨hx,hy⟩
        exact (lt_of_not_ge hy).le
      · exact Or.inl (lt_of_not_ge hx).le
    rw [integral_sargosPlanarKernelTerm_eq_zero ha hb hcut c d,mul_zero,norm_zero,if_neg h]

theorem sargosWeightedPlanarIntegral_le_nearPairs {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u v : ι → ℝ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ, sargosWeightedPlanarIntegrand S z u v a b c d α γ) ≤
      ((sargosNearPairs S u v a b).card : ℝ) := by
  classical
  have hn : 0 ≤ ∫ α : ℝ, ∫ γ : ℝ,
      sargosWeightedPlanarIntegrand S z u v a b c d α γ := by
    apply integral_nonneg
    intro α
    apply integral_nonneg
    intro γ
    exact sargosWeightedPlanarIntegrand_nonneg S z u v ha.le hb.le c d α γ
  calc
    _ = ‖((∫ α : ℝ, ∫ γ : ℝ,
        sargosWeightedPlanarIntegrand S z u v a b c d α γ : ℝ) : ℂ)‖ :=
      (Complex.norm_of_nonneg hn).symm
    _ = ‖∑ p ∈ S ×ˢ S, (z p.1*conj (z p.2))*
        ∫ α : ℝ, ∫ γ : ℝ,
          sargosPlanarKernelTerm a b c d (u p.1-u p.2) (v p.1-v p.2) α γ‖ := by
      rw [integral_sargosWeightedPlanarIntegrand_eq_gram S z u v ha hb c d]
    _ ≤ ∑ p ∈ S ×ˢ S, ‖(z p.1*conj (z p.2))*
        ∫ α : ℝ, ∫ γ : ℝ,
          sargosPlanarKernelTerm a b c d (u p.1-u p.2) (v p.1-v p.2) α γ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ S ×ˢ S,
        if |u p.1-u p.2| ≤ a ∧ |v p.1-v p.2| ≤ b then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpI := Finset.mem_product.mp hp
      exact norm_sargosPlanarGramTerm_le ha hb (hz p.1 hpI.1) (hz p.2 hpI.2)
        c d (u p.1-u p.2) (v p.1-v p.2)
    _ = _ := by
      simp only [sargosNearPairs,Finset.card_eq_sum_ones,Nat.cast_sum,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> norm_num

end TaoTrudgianYang2025
