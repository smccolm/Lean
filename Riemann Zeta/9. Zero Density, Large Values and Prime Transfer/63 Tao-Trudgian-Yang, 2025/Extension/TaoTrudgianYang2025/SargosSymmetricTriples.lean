import TaoTrudgianYang2025.SargosGroupedSecondMoment
import TaoTrudgianYang2025.SargosInitialMomentTuples

/-! Literal positive-offset triples and their integer square frequencies. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosSymmetricFactor (a : ℤ → ℂ) (M H j : ℕ) (m n : ℤ) : ℂ :=
  if n ∈ sargosPositiveOffsets H j then
    sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n) else 0

def sargosSymmetricTriple (a : ℤ → ℂ) (M H j : ℕ) (m : ℤ)
    (t : SargosInitialMomentTuple H 3) : ℂ :=
  ∏ i, sargosSymmetricFactor a M H j m (t i)

theorem sargosSymmetricFactor_sum (a : ℤ → ℂ) (M H j : ℕ) (m : ℤ) :
    (∑ n ∈ Finset.Ioc (0:ℤ) H, sargosSymmetricFactor a M H j m n) =
      ∑ n ∈ sargosPositiveOffsets H j,
        sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n) := by
  have he : (Finset.Ioc (0:ℤ) H).filter (fun n => n ∈ sargosPositiveOffsets H j) =
      sargosPositiveOffsets H j := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun hn => ⟨sargosPositiveOffsets_subset H j hn,hn⟩⟩
  simp only [sargosSymmetricFactor]
  rw [← Finset.sum_filter,he]

theorem sargos_positive_symmetric_cube (a : ℤ → ℂ) (M H j : ℕ) (m : ℤ) :
    (∑ n ∈ sargosPositiveOffsets H j,
      sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n))^3 =
      ∑ t : SargosInitialMomentTuple H 3, sargosSymmetricTriple a M H j m t := by
  rw [← sargosSymmetricFactor_sum,← Finset.sum_coe_sort,Fintype.sum_pow]
  rfl

theorem sargosInitialTuple_square_bounds {H : ℕ}
    (t : SargosInitialMomentTuple H 3) :
    0 ≤ sargosInitialTuplePower 2 t ∧ sargosInitialTuplePower 2 t ≤ 3*(H:ℤ)^2 := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · calc
      _ ≤ ∑ _i : Fin 3, (H:ℤ)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hn := Finset.mem_Ioc.mp (t i).property
        exact pow_le_pow_left₀ hn.1.le hn.2 2
      _ = _ := by simp

theorem sargos_square_frequency_card (H : ℕ) :
    ((Finset.Icc (0:ℤ) (3*(H:ℤ)^2)).card:ℝ) = 3*(H:ℝ)^2+1 := by
  simp only [Int.card_Icc,sub_zero]
  have h : ((3*(H:ℤ)^2+1).toNat:ℤ) = 3*(H:ℤ)^2+1 :=
    Int.toNat_of_nonneg (by positivity)
  exact_mod_cast h

theorem sargos_square_frequency_card_le {H : ℕ} (hH : 1 ≤ H) :
    ((Finset.Icc (0:ℤ) (3*(H:ℤ)^2)).card:ℝ) ≤ 4*(H:ℝ)^2 := by
  rw [sargos_square_frequency_card]
  have h : (1:ℝ) ≤ H := by exact_mod_cast hH
  nlinarith

end TaoTrudgianYang2025
