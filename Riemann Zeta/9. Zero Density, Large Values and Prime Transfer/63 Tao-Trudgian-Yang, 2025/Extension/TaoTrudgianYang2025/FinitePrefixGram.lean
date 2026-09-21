import TaoTrudgianYang2025.AtkinsonDyadicZetaConsumer
import GuthMaynard.ClassicalLargeValues

/-!
# Finite norm-sum Gram duality

This is the coefficient/vector argument already used by the native
Montgomery--Halasz machinery. Keeping arbitrary vectors allows a different
prefix mask at every height; no common-prefix premise is introduced.
-/

noncomputable section

open Complex
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem sum_norm_coefficient_vector_sq_le_gram
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (d : ι → ℂ) (e : κ → ι → ℂ) :
    (∑ t ∈ W, ‖∑ n ∈ s, d n*e t n‖)^2 ≤
      (∑ n ∈ s, ‖d n‖^2)*
        ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (e t n)*e u n‖ := by
  let D : κ → ℂ := fun t => ∑ n ∈ s, d n*e t n
  let c : κ → ℂ := fun t => phaseAlign (D t)
  have hc : ∀ t ∈ W, ‖c t‖ ≤ 1 := fun t _ => norm_phaseAlign_le_one (D t)
  have halign : ‖∑ t ∈ W, c t*D t‖ = ∑ t ∈ W, ‖D t‖ := by
    have he : (∑ t ∈ W, c t*D t) = ((∑ t ∈ W, ‖D t‖ : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl (fun t _ => phaseAlign_mul (D t))
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hexpand : (∑ t ∈ W, c t*D t) =
      ∑ n ∈ s, d n*(∑ t ∈ W, c t*e t n) := by
    simp only [D,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hcs := norm_sum_mul_sq_le s d (fun n => ∑ t ∈ W, c t*e t n)
  rw [← hexpand,halign] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (sum_norm_sq_sum_le_gram s W c e hc) (by positivity))

theorem card_mul_lower_sq_le_coefficient_gram
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (d : ι → ℂ) (e : κ → ι → ℂ)
    {V : ℝ} (hV : 0 ≤ V)
    (hlarge : ∀ t ∈ W, V ≤ ‖∑ n ∈ s, d n*e t n‖) :
    ((W.card:ℝ)*V)^2 ≤ (∑ n ∈ s, ‖d n‖^2)*
      ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (e t n)*e u n‖ := by
  have hsum : (W.card:ℝ)*V ≤ ∑ t ∈ W, ‖∑ n ∈ s, d n*e t n‖ := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hlarge
  exact (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hV) hsum 2).trans
    (sum_norm_coefficient_vector_sq_le_gram s W d e)

theorem sum_range_prefix_mask {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {j N : ℕ} (hj : j ≤ N) :
    (∑ i ∈ Finset.range N, if i < j then f i else 0) = ∑ i ∈ Finset.range j, f i := by
  calc
    _ = ∑ i ∈ Finset.range j, if i < j then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hj)
      intro i _ hi
      simp only [Finset.mem_range] at hi
      simp [hi]
    _ = _ := Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))

end TaoTrudgianYang2025
