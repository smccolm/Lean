import TaoTrudgianYang2025.RobertSargosConjugateAveraging
import TaoTrudgianYang2025.RobertSargosCorrelationSupport

/-! Actual one-based symmetric-phase consumer for the initial conjugated A-process. -/

noncomputable section
open GafniTao
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace TaoTrudgianYang2025

theorem robertSargos_centered_phase_inner (f : ℝ → ℝ) (M : ℕ) (m h : ℤ)
    (hh : 0 ≤ h) :
    ⟪sargosPaddedSequence (fun n => fordAdditiveCharacter (f (n+1))) M (m+h),
      sargosPaddedSequence (fun n => fordAdditiveCharacter (f (n+1))) M (m-h)⟫_ℝ =
      if m ∈ Finset.Icc h ((M:ℤ)-h-1) then
        (fordAdditiveCharacter (robertSargosSymmetricDifference f (m+1) h)).re
      else 0 := by
  by_cases hm : m ∈ Finset.Icc h ((M:ℤ)-h-1)
  · have hp : m+h ∈ Finset.Ico (0:ℤ) M := by
      simp only [Finset.mem_Icc] at hm
      simp only [Finset.mem_Ico]
      constructor <;> omega
    have hn : m-h ∈ Finset.Ico (0:ℤ) M := by
      simp only [Finset.mem_Icc] at hm
      simp only [Finset.mem_Ico]
      constructor <;> omega
    rw [if_pos hm,sargosPaddedSequence_eq _ _ hp,sargosPaddedSequence_eq _ _ hn,
      real_inner_comm,real_inner_eq_re_inner ℂ,RCLike.inner_apply]
    change (fordAdditiveCharacter (f ((m+h:ℤ)+1)) *
      conj (fordAdditiveCharacter (f ((m-h:ℤ)+1)))).re = _
    rw [conj_fordAdditiveCharacter,← fordAdditiveCharacter_add]
    congr 2
    unfold robertSargosSymmetricDifference
    have hplus : (m:ℝ)+h+1 = (m:ℝ)+1+h := by ring
    have hminus : (m:ℝ)-h+1 = (m:ℝ)+1-h := by ring
    simp only [Int.cast_add,Int.cast_sub,hplus,hminus]
    simp only [sub_eq_add_neg]
  · rw [if_neg hm]
    by_cases hp : m+h ∈ Finset.Ico (0:ℤ) M
    · have hn : m-h ∉ Finset.Ico (0:ℤ) M := by
        simp only [Finset.mem_Icc] at hm
        simp only [Finset.mem_Ico] at hp ⊢
        omega
      rw [sargosPaddedSequence_zero _ _ hn,inner_zero_right]
    · rw [sargosPaddedSequence_zero _ _ hp,inner_zero_left]

def robertSargosSourceCenteredPhase (f : ℝ → ℝ) (M : ℕ) (h : ℤ) : ℂ :=
  ∑ m ∈ Finset.Icc (h+1) ((M:ℤ)-h),
    fordAdditiveCharacter (robertSargosSymmetricDifference f m h)

theorem robertSargos_centered_phase_sum (f : ℝ → ℝ) (M : ℕ) (h : ℤ)
    (hh : 0 ≤ h) :
    robertSargosCenteredCorrelation (fun n => fordAdditiveCharacter (f (n+1))) M h =
      (robertSargosSourceCenteredPhase f M h).re := by
  classical
  unfold robertSargosCenteredCorrelation robertSargosSourceCenteredPhase
  simp only [robertSargos_centered_phase_inner f M _ h hh,Complex.re_sum]
  rw [← Finset.sum_filter]
  have he : (Finset.Ico (0:ℤ) M).filter
      (fun m => m ∈ Finset.Icc h ((M:ℤ)-h-1)) = Finset.Icc h ((M:ℤ)-h-1) := by
    apply Finset.filter_mem_eq_of_subset
    intro m hm
    simp only [Finset.mem_Icc] at hm
    simp only [Finset.mem_Ico]
    constructor <;> omega
  rw [he]
  apply Finset.sum_bij (fun m _ => m+1)
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    constructor <;> omega
  · intro m _ n _ he'
    omega
  · intro m hm
    refine ⟨m-1,?_,by omega⟩
    simp only [Finset.mem_Icc] at hm ⊢
    constructor <;> omega
  · intro m _
    simp only [Int.cast_add,Int.cast_one]

end TaoTrudgianYang2025
