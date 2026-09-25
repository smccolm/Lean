import TaoTrudgianYang2025.IntegerIntervalBoundary
import TaoTrudgianYang2025.RobertSargosSymmetricATimesA

/-! The r-dependent source endpoints may be replaced only with a charged error. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem robertSargos_m_overlap_inter (M : ℕ) (h q r : ℤ) :
    robertSargosMOverlap M h q r =
      Finset.Icc (h+1-q) ((M:ℤ)-h-q) ∩
        Finset.Icc ((h+1)+r) (((M:ℤ)-h)-r) := by
  ext m
  simp only [robertSargosMOverlap,Finset.mem_Icc,Finset.mem_inter,
    max_le_iff,le_min_iff]
  omega

theorem norm_robertSargos_m_overlap_error (w : ℤ → ℂ) (M : ℕ) (h q r : ℤ)
    (hw : ∀ m ∈ Finset.Icc (h+1-q) ((M:ℤ)-h-q), ‖w m‖ ≤ 1) :
    ‖(∑ m ∈ robertSargosMOverlap M h q r, w m) -
      ∑ m ∈ robertSargosMOverlap M h q 0, w m‖ ≤ 2*|(r:ℝ)| := by
  simp only [robertSargos_m_overlap_inter,add_zero,sub_zero]
  exact norm_integer_interval_endpoint_shift w
    (Finset.Icc (h+1-q) ((M:ℤ)-h-q)) (h+1) ((M:ℤ)-h) r hw

def robertSargosTrimmedCorrelation (f : ℝ → ℝ) (M H : ℕ) (q r : ℤ) : ℂ :=
  ∑ h ∈ robertSargosHOverlap H r, ∑ m ∈ robertSargosMOverlap M h q 0,
    fordAdditiveCharacter
      (robertSargosSymmetricDifference f (m+q) h -
        robertSargosSymmetricDifference f m (h+r))

theorem robertSargos_h_overlap_card (H : ℕ) (r : ℤ) :
    (robertSargosHOverlap H r).card ≤ H := by
  have hs : robertSargosHOverlap H r ⊆ Finset.Ico (H:ℤ) (2*H) :=
    fun h hh => ((mem_robertSargosHOverlap H h r).mp hh).1
  have hc := Finset.card_le_card hs
  have hi : 2*(H:ℤ)-H = H := by omega
  simpa only [Int.card_Ico,hi,Int.toNat_natCast] using hc

theorem norm_robertSargos_correlation_endpoint_error (f : ℝ → ℝ) (M H : ℕ)
    (q r : ℤ) :
    ‖robertSargosMixedCorrelation f M H q r -
      robertSargosTrimmedCorrelation f M H q r‖ ≤ 2*(H:ℝ)*|(r:ℝ)| := by
  unfold robertSargosMixedCorrelation robertSargosTrimmedCorrelation
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ h ∈ robertSargosHOverlap H r,
        ‖(∑ m ∈ robertSargosMOverlap M h q r, fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+q) h -
              robertSargosSymmetricDifference f m (h+r))) -
          ∑ m ∈ robertSargosMOverlap M h q 0, fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+q) h -
              robertSargosSymmetricDifference f m (h+r))‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ robertSargosHOverlap H r, 2*|(r:ℝ)| := by
      apply Finset.sum_le_sum
      intro h _
      exact norm_robertSargos_m_overlap_error _ M h q r
        (fun _ _ => le_of_eq (sargos_character_norm _))
    _ ≤ 2*(H:ℝ)*|(r:ℝ)| := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hc : ((robertSargosHOverlap H r).card:ℝ) ≤ H := by
        exact_mod_cast robertSargos_h_overlap_card H r
      nlinarith [abs_nonneg (r:ℝ)]

end TaoTrudgianYang2025
