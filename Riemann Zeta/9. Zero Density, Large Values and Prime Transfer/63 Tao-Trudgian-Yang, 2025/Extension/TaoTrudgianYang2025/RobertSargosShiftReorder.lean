import TaoTrudgianYang2025.RobertSargosWeightedShift

/-! Reordering preserves the inner q,h,n cancellation before taking norms. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

def robertSargosShiftedTriple (f : ℝ → ℝ) (H Q N : ℕ) (r m : ℤ) : ℂ :=
  ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ h ∈ robertSargosHOverlap H r,
    ∑ n ∈ Finset.Icc (1:ℤ) N,
      ((1-|(q:ℝ)|/Q : ℝ):ℂ)*
        fordAdditiveCharacter
          (robertSargosSymmetricDifference f (m+n+q) h-
            robertSargosSymmetricDifference f (m+n) (h+r))

theorem robertSargos_shifted_correlation_m_sum (f : ℝ → ℝ) (M H Q N : ℕ) (q r : ℤ) :
    robertSargosShiftedCorrelation f M H Q N q r =
      (N:ℂ)⁻¹*∑ m ∈ robertSargosCommonMInterval M H Q N,
        ∑ h ∈ robertSargosHOverlap H r, ∑ n ∈ Finset.Icc (1:ℤ) N,
          fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+n+q) h-
              robertSargosSymmetricDifference f (m+n) (h+r)) := by
  unfold robertSargosShiftedCorrelation
  congr 1
  calc
    _ = ∑ h ∈ robertSargosHOverlap H r, ∑ n ∈ Finset.Icc (1:ℤ) N,
        ∑ m ∈ robertSargosCommonMInterval M H Q N,
          fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+n+q) h-
              robertSargosSymmetricDifference f (m+n) (h+r)) := Finset.sum_comm
    _ = ∑ h ∈ robertSargosHOverlap H r,
        ∑ m ∈ robertSargosCommonMInterval M H Q N, ∑ n ∈ Finset.Icc (1:ℤ) N,
          fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+n+q) h-
              robertSargosSymmetricDifference f (m+n) (h+r)) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem robertSargos_weighted_shifted_reorder (f : ℝ → ℝ) (M H Q R N : ℕ) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (((1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R) : ℝ):ℂ)*
        robertSargosShiftedCorrelation f M H Q N q r) =
      (N:ℂ)⁻¹*∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
        ((1-|(r:ℝ)|/R : ℝ):ℂ)*
          ∑ m ∈ robertSargosCommonMInterval M H Q N,
            robertSargosShiftedTriple f H Q N r m := by
  simp_rw [robertSargos_shifted_correlation_m_sum]
  simp only [robertSargosShiftedTriple,Complex.ofReal_mul,Finset.mul_sum]
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
