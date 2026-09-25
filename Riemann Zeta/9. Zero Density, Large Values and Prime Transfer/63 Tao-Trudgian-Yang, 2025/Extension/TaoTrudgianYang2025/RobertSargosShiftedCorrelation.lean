import TaoTrudgianYang2025.RobertSargosAverageBoundary

/-! The actual shifted mixed-phase correlation with a common m interval. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

def robertSargosShiftedCorrelation (f : ℝ → ℝ) (M H Q N : ℕ) (q r : ℤ) : ℂ :=
  (N:ℂ)⁻¹*∑ n ∈ Finset.Icc (1:ℤ) N, ∑ h ∈ robertSargosHOverlap H r,
    ∑ m ∈ robertSargosCommonMInterval M H Q N,
      fordAdditiveCharacter
        (robertSargosSymmetricDifference f (m+n+q) h-
          robertSargosSymmetricDifference f (m+n) (h+r))

theorem robertSargos_shifted_correlation_h_sum (f : ℝ → ℝ) (M H Q N : ℕ) (q r : ℤ) :
    robertSargosShiftedCorrelation f M H Q N q r =
      ∑ h ∈ robertSargosHOverlap H r, (N:ℂ)⁻¹*∑ n ∈ Finset.Icc (1:ℤ) N,
        ∑ m ∈ robertSargosCommonMInterval M H Q N,
          fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+n+q) h-
              robertSargosSymmetricDifference f (m+n) (h+r)) := by
  unfold robertSargosShiftedCorrelation
  rw [Finset.sum_comm,Finset.mul_sum]

theorem norm_robertSargos_trimmed_shift_error (f : ℝ → ℝ) (M H Q N : ℕ) (q r : ℤ)
    (hN : 0 < N) (hq : q ∈ Finset.Ioo (-(Q:ℤ)) Q) :
    ‖robertSargosTrimmedCorrelation f M H q r-
      robertSargosShiftedCorrelation f M H Q N q r‖ ≤
      (H:ℝ)*(4*(H:ℝ)+4*Q+2*N) := by
  rw [robertSargos_shifted_correlation_h_sum]
  unfold robertSargosTrimmedCorrelation
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _h ∈ robertSargosHOverlap H r, (4*(H:ℝ)+4*Q+2*N) := by
      apply Finset.sum_le_sum
      intro h hh
      have ht := norm_robertSargos_common_shift_error
        (fun m => fordAdditiveCharacter
          (robertSargosSymmetricDifference f (m+q) h-
            robertSargosSymmetricDifference f m (h+r)))
        M H Q N h q hN ((mem_robertSargosHOverlap H h r).mp hh).1 hq
        (fun m => le_of_eq (sargos_character_norm _))
      simpa only [Int.cast_add] using ht
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast robertSargos_h_overlap_card H r

end TaoTrudgianYang2025
