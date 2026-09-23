import TaoTrudgianYang2025.EnergySeparation

/-!
# Multiplicity-preserving finite cardinality partitions

The index type is retained even when different indices have equal ordinates.
Only the proved one-separation lemma permits replacing an indexed family by
its image.
-/

noncomputable section

namespace TaoTrudgianYang2025

open scoped BigOperators

theorem cardinality_eq_sum_color_fibers
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (color : ι → κ) :
    Fintype.card ι = ∑ c : κ, Fintype.card (EnergyColorFiber color c) := by
  classical
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv color).symm

theorem cardinality_le_color_count_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (color : ι → κ) (B : ℝ)
    (hB : ∀ c : κ, (Fintype.card (EnergyColorFiber color c) : ℝ) ≤ B) :
    (Fintype.card ι : ℝ) ≤ (Fintype.card κ : ℝ) * B := by
  rw [cardinality_eq_sum_color_fibers color, Nat.cast_sum]
  calc
    ∑ c : κ, (Fintype.card (EnergyColorFiber color c) : ℝ) ≤ ∑ _c : κ, B :=
      Finset.sum_le_sum (fun c _ => hB c)
    _ = (Fintype.card κ : ℝ) * B := by simp

end TaoTrudgianYang2025
