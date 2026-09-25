import TaoTrudgianYang2025.RobertSargosShiftBoundary
import TaoTrudgianYang2025.IntegerClosedIntervalPrefix

/-! Literal zero-r source correlations and their true positive-q endpoints. -/

noncomputable section
open Set GafniTao
namespace TaoTrudgianYang2025

def robertSargosZeroRSource (f : ℝ → ℝ) (M : ℕ) (h q : ℤ) : ℂ :=
  ∑ m ∈ robertSargosMOverlap M h q 0,
    fordAdditiveCharacter (robertSargosSymmetricDifference f (m+q) h-
      robertSargosSymmetricDifference f m h)

theorem robertSargos_zero_r_positive_interval (M : ℕ) (h q : ℤ) (hq : 0 ≤ q) :
    robertSargosMOverlap M h q 0 = Finset.Icc (h+1) ((M:ℤ)-h-q) := by
  rw [robertSargos_m_overlap_zero_source]
  rw [max_eq_left (by omega),min_eq_right (by omega)]

theorem robertSargos_zero_r_source_neg (f : ℝ → ℝ) (M : ℕ) (h q : ℤ) :
    robertSargosZeroRSource f M h (-q) = star (robertSargosZeroRSource f M h q) := by
  unfold robertSargosZeroRSource
  change _ = (starRingEnd ℂ) _
  rw [map_sum]
  symm
  apply Finset.sum_bij (fun m _ => m+q)
  · intro m hm
    simp only [robertSargos_m_overlap_zero_source,Finset.mem_Icc,max_le_iff,le_min_iff] at hm ⊢
    constructor <;> constructor <;> omega
  · intro m _ n _ he
    omega
  · intro m hm
    refine ⟨m-q,?_,by omega⟩
    simp only [robertSargos_m_overlap_zero_source,Finset.mem_Icc,max_le_iff,le_min_iff] at hm ⊢
    constructor <;> constructor <;> omega
  · intro m _
    rw [conj_fordAdditiveCharacter]
    congr 1
    simp only [Int.cast_add,Int.cast_neg,add_neg_cancel_right]
    ring

theorem norm_robertSargos_zero_r_source_neg (f : ℝ → ℝ) (M : ℕ) (h q : ℤ) :
    ‖robertSargosZeroRSource f M h (-q)‖ = ‖robertSargosZeroRSource f M h q‖ := by
  rw [robertSargos_zero_r_source_neg,norm_star]

end TaoTrudgianYang2025
