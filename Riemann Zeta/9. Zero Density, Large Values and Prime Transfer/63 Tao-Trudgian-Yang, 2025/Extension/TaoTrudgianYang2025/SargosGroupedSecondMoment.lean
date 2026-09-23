import TaoTrudgianYang2025.SargosFiniteFrequencyGram
import Mathlib.Algebra.Order.Chebyshev

/-! Cauchy grouping by an actual finite frequency map. -/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargos_grouped_second_moment {ι κ μ : Type*}
    [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]
    (T : Finset ι) (K : Finset κ) (J : Finset μ) (v : ι → κ)
    (hv : ∀ t ∈ T, v t ∈ K) (F : μ → ι → ℂ) :
    (∑ m ∈ J, ‖∑ t ∈ T, F m t‖)^2 ≤
      (J.card:ℝ)*K.card*
        ∑ q ∈ (T ×ˢ T).filter (fun q => v q.1=v q.2),
          ‖∑ m ∈ J, F m q.1*conj (F m q.2)‖ := by
  let G : μ × κ → ℝ := fun p => ‖∑ t ∈ T with v t=p.2, F p.1 t‖
  have hn : 0 ≤ ∑ m ∈ J, ‖∑ t ∈ T, F m t‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsplit : (∑ m ∈ J, ‖∑ t ∈ T, F m t‖) ≤ ∑ p ∈ J ×ˢ K, G p := by
    rw [Finset.sum_product]
    apply Finset.sum_le_sum
    intro m hm
    have he := Finset.sum_fiberwise_of_maps_to hv (F m)
    rw [← he]
    exact norm_sum_le _ _
  have hcs := sq_sum_le_card_mul_sum_sq (s := J ×ˢ K) (f := G)
  have he : (∑ p ∈ J ×ˢ K, G p^2) =
      ∑ q ∈ (T ×ˢ T).filter (fun q => v q.1=v q.2),
        (∑ m ∈ J, F m q.1*conj (F m q.2)).re := by
    rw [Finset.sum_product]
    simp only [G]
    simp_rw [sargos_grouped_gram T K v hv]
    rw [Finset.sum_comm]
    simp only [Complex.re_sum]
  calc
    _ ≤ (∑ p ∈ J ×ˢ K, G p)^2 := pow_le_pow_left₀ hn hsplit 2
    _ ≤ ((J ×ˢ K).card:ℝ)*(∑ p ∈ J ×ˢ K, G p^2) := hcs
    _ = (J.card:ℝ)*K.card*
        ∑ q ∈ (T ×ˢ T).filter (fun q => v q.1=v q.2),
          (∑ m ∈ J, F m q.1*conj (F m q.2)).re := by
      rw [he,Finset.card_product,Nat.cast_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro q hq
      exact Complex.re_le_norm _

end TaoTrudgianYang2025
