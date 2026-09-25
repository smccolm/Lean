import TaoTrudgianYang2025.RobertSargosShiftReorder

/-! Reordering preserves the inner q,h,n cancellation before taking norms. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

def robertSargosNonzeroShiftedTriple (f : ℝ → ℝ) (H Q N : ℕ) (r m : ℤ) : ℂ :=
  ∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0, ∑ h ∈ robertSargosHOverlap H r,
    ∑ n ∈ Finset.Icc (1:ℤ) N,
      ((1-|(q:ℝ)|/Q : ℝ):ℂ)*
        fordAdditiveCharacter
          (robertSargosSymmetricDifference f (m+n+q) h-
            robertSargosSymmetricDifference f (m+n) (h+r))

theorem robertSargos_nonzero_weighted_shifted_reorder (f : ℝ → ℝ) (M H Q R N : ℕ) :
    (∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0, ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
      (((1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R) : ℝ):ℂ)*
        robertSargosShiftedCorrelation f M H Q N q r) =
      (N:ℂ)⁻¹*∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
        ((1-|(r:ℝ)|/R : ℝ):ℂ)*
          ∑ m ∈ robertSargosCommonMInterval M H Q N,
            robertSargosNonzeroShiftedTriple f H Q N r m := by
  simp_rw [robertSargos_shifted_correlation_m_sum]
  simp only [robertSargosNonzeroShiftedTriple,Complex.ofReal_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro n _
  ring

end TaoTrudgianYang2025
