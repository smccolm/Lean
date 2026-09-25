import TaoTrudgianYang2025.RobertSargosSourceATimesA
import TaoTrudgianYang2025.RobertSargosMixedCharacter

/-! The actual symmetric-phase array and its finite source sum.
Both the h band and the m interval are part of the coefficients. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

def robertSargosSymmetricArray (f : ℝ → ℝ) (M H : ℕ) (m h : ℤ) : ℂ :=
  if h ∈ Finset.Ico (H:ℤ) (2*H) then
    if m ∈ Finset.Icc (h+1) ((M:ℤ)-h) then
      fordAdditiveCharacter (robertSargosSymmetricDifference f m h)
    else 0
  else 0

def robertSargosSymmetricSum (f : ℝ → ℝ) (M H : ℕ) : ℂ :=
  ∑ h ∈ Finset.Ico (H:ℤ) (2*H),
    ∑ m ∈ Finset.Icc (h+1) ((M:ℤ)-h),
      fordAdditiveCharacter (robertSargosSymmetricDifference f m h)

theorem robertSargos_symmetric_array_norm (f : ℝ → ℝ) (M H : ℕ) (m h : ℤ) :
    ‖robertSargosSymmetricArray f M H m h‖ ≤ 1 := by
  unfold robertSargosSymmetricArray
  split_ifs <;> simp only [sargos_character_norm,norm_zero] <;> norm_num

theorem robertSargos_symmetric_array_support (f : ℝ → ℝ) (M H : ℕ)
    (m h : ℤ) (hout : m ∉ Finset.Icc (1:ℤ) M ∨ h ∉ Finset.Icc (1:ℤ) (2*H)) :
    robertSargosSymmetricArray f M H m h = 0 := by
  unfold robertSargosSymmetricArray
  split_ifs with hh hm
  · simp only [Finset.mem_Ico] at hh
    simp only [Finset.mem_Icc] at hm hout
    rcases hout with hout | hout <;> omega
  · rfl
  · rfl

theorem robertSargos_symmetric_array_sum (f : ℝ → ℝ) (M H : ℕ) :
    (∑ m ∈ Finset.Icc (1:ℤ) M, ∑ h ∈ Finset.Icc (1:ℤ) (2*H),
      robertSargosSymmetricArray f M H m h) = robertSargosSymmetricSum f M H := by
  classical
  rw [Finset.sum_comm]
  have hsub : Finset.Ico (H:ℤ) (2*H) ⊆ Finset.Icc (1:ℤ) (2*H) := by
    intro h hh
    have ht := Finset.mem_Ico.mp hh
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  calc
    _ = ∑ h ∈ Finset.Ico (H:ℤ) (2*H), ∑ m ∈ Finset.Icc (1:ℤ) M,
        robertSargosSymmetricArray f M H m h := by
      symm
      apply Finset.sum_subset hsub
      intro h _ hh
      apply Finset.sum_eq_zero
      intro m _
      simp only [robertSargosSymmetricArray,if_neg hh]
    _ = _ := by
      unfold robertSargosSymmetricSum
      apply Finset.sum_congr rfl
      intro h hh
      have ht := Finset.mem_Ico.mp hh
      simp only [robertSargosSymmetricArray,if_pos hh]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext m
      simp only [Finset.mem_filter,Finset.mem_Icc]
      omega

end TaoTrudgianYang2025
