import TaoTrudgianYang2025.RobertSargosCorrelationSupport

/-! Exact correlation sum on the two overlapping source intervals. -/

noncomputable section
open GafniTao
open scoped BigOperators InnerProductSpace
namespace TaoTrudgianYang2025

theorem robertSargos_h_overlap_subset (H : ℕ) (r : ℤ) :
    robertSargosHOverlap H r ⊆ Finset.Icc (1:ℤ) (2*H) := by
  intro h hh
  have ht := (mem_robertSargosHOverlap H h r).mp hh
  simp only [Finset.mem_Ico] at ht
  simp only [Finset.mem_Icc]
  constructor <;> omega

theorem robertSargos_m_overlap_subset (M H : ℕ) (h q r : ℤ)
    (hh : h ∈ robertSargosHOverlap H r) :
    robertSargosMOverlap M h q r ⊆ Finset.Icc (1:ℤ) M := by
  intro m hm
  have ht := (mem_robertSargosHOverlap H h r).mp hh
  have hu := (mem_robertSargosMOverlap M m h q r).mp hm
  simp only [Finset.mem_Ico] at ht
  simp only [Finset.mem_Icc] at hu ⊢
  constructor <;> omega

def robertSargosMixedCorrelation (f : ℝ → ℝ) (M H : ℕ) (q r : ℤ) : ℂ :=
  ∑ h ∈ robertSargosHOverlap H r, ∑ m ∈ robertSargosMOverlap M h q r,
    fordAdditiveCharacter
      (robertSargosSymmetricDifference f (m+q) h -
        robertSargosSymmetricDifference f m (h+r))

theorem robertSargos_symmetric_correlation_sum (f : ℝ → ℝ) (M H : ℕ) (q r : ℤ) :
    (∑ m ∈ Finset.Icc (1:ℤ) M, ∑ h ∈ Finset.Icc (1:ℤ) (2*H),
      ⟪robertSargosSymmetricArray f M H (m+q) h,
        robertSargosSymmetricArray f M H m (h+r)⟫_ℝ) =
      (robertSargosMixedCorrelation f M H q r).re := by
  classical
  rw [Finset.sum_comm]
  simp_rw [robertSargos_symmetric_array_inner]
  unfold robertSargosMixedCorrelation
  simp only [Complex.re_sum]
  calc
    _ = ∑ h ∈ robertSargosHOverlap H r, ∑ m ∈ Finset.Icc (1:ℤ) M,
        if h ∈ robertSargosHOverlap H r ∧ m ∈ robertSargosMOverlap M h q r then
          (fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+q) h -
              robertSargosSymmetricDifference f m (h+r))).re else 0 := by
      symm
      apply Finset.sum_subset (robertSargos_h_overlap_subset H r)
      intro h _ hh
      simp only [hh,false_and,if_false,Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [hh,true_and]
      rw [← Finset.sum_filter,
        Finset.filter_mem_eq_of_subset (robertSargos_m_overlap_subset M H h q r hh)]

end TaoTrudgianYang2025
