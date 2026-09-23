import TaoTrudgianYang2025.SargosIntervalGrid

/-! Nonnegative integral bounds for finite covers, retaining overlapping endpoints. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace TaoTrudgianYang2025

theorem sargos_lintegral_finset_union_le {A B : Type*} [MeasurableSpace A]
    (μ : Measure A) (s : Finset B) (t : B → Set A) (f : A → ℝ≥0∞) :
    (∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ) ≤ ∑ b ∈ s, ∫⁻ a in t b, f a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    simp only [Finset.set_biUnion_insert,Finset.sum_insert hb]
    exact (lintegral_union_le f (t b) (⋃ k ∈ s, t k)).trans (add_le_add le_rfl ih)

theorem sargos_lintegral_finset_cover_le {A B : Type*} [MeasurableSpace A]
    (μ : Measure A) (s : Finset B) (t : B → Set A) (f : A → ℝ≥0∞)
    {u : Set A} (hu : u ⊆ ⋃ b ∈ s, t b) :
    (∫⁻ a in u, f a ∂μ) ≤ ∑ b ∈ s, ∫⁻ a in t b, f a ∂μ :=
  (lintegral_mono_set hu).trans (sargos_lintegral_finset_union_le μ s t f)

theorem sargos_rectangle_grid_cover {a b L K h k : ℝ}
    (hh : 0 < h) (hk : 0 < k) :
    (Icc a (a+L) ×ˢ Icc b (b+K)) ⊆
      ⋃ p ∈ (Finset.range (sargosIntervalGridCount L h)).product
        (Finset.range (sargosIntervalGridCount K k)),
      (Icc (a+(p.1:ℝ)*h) (a+(p.1:ℝ)*h+h) ×ˢ
        Icc (b+(p.2:ℝ)*k) (b+(p.2:ℝ)*k+k)) := by
  intro p hp
  obtain ⟨i,hi,hx⟩ := sargosIntervalGrid_cover hh hp.1
  obtain ⟨j,hj,hy⟩ := sargosIntervalGrid_cover hk hp.2
  exact mem_iUnion.mpr ⟨(i,j),mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hi,hj⟩,hx,hy⟩⟩

end TaoTrudgianYang2025
