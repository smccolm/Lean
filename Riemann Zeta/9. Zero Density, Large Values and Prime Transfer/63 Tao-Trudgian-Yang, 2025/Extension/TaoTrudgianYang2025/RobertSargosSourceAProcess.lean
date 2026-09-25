import TaoTrudgianYang2025.RobertSargosSourceCenteredPhase

/-! Initial source A-process with the norm of the complete weighted symmetric sum. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

def robertSargosWeightedSymmetricPhase (f : ℝ → ℝ) (M H : ℕ) : ℂ :=
  ∑ h ∈ Finset.Ioo (0:ℤ) H,
    ((1-(h:ℝ)/H : ℝ):ℂ)*robertSargosSourceCenteredPhase f M h

theorem robertSargos_weighted_symmetric_re (f : ℝ → ℝ) (M H : ℕ) :
    (∑ h ∈ Finset.Ioo (0:ℤ) H,
      (1-(h:ℝ)/H)*robertSargosCenteredCorrelation
        (fun n => fordAdditiveCharacter (f (n+1))) M h) =
      (robertSargosWeightedSymmetricPhase f M H).re := by
  unfold robertSargosWeightedSymmetricPhase
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  apply Finset.sum_congr rfl
  intro h hh
  rw [robertSargos_centered_phase_sum f M h (le_of_lt (Finset.mem_Ioo.mp hh).1)]

theorem robertSargos_initial_source_a_process (f : ℝ → ℝ) (M H : ℕ) (hH : 0 < H) :
    ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖^2 ≤
      (((M:ℝ)+2*H)/H)*((M:ℝ)+2*‖robertSargosWeightedSymmetricPhase f M H‖) := by
  have hs := robertSargos_conjugate_a_process
    (fun n => fordAdditiveCharacter (f (n+1))) M H hH
  have hsum : (∑ n ∈ Finset.Ico (0:ℤ) M,
      fordAdditiveCharacter (f ((n:ℝ)+1))) =
      ∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m) := by
    simpa only [Int.cast_add,Int.cast_one] using
      robertSargos_sum_one_based (fun m => fordAdditiveCharacter (f m)) M
  have hd : (∑ m ∈ Finset.Ico (0:ℤ) M,
      ‖fordAdditiveCharacter (f ((m:ℝ)+1))‖^2) = (M:ℝ) := by
    simp only [sargos_character_norm,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,
      Int.card_Ico,sub_zero,Int.toNat_natCast]
  rw [hsum,hd,robertSargos_weighted_symmetric_re] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num)) _)
    (by positivity))

theorem robertSargos_initial_source_a_process_range (f : ℝ → ℝ) (M H : ℕ)
    (hH : 0 < H) (hHM : H ≤ M) :
    ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖^2 ≤
      3*(M:ℝ)^2/H+(6*(M:ℝ)/H)*‖robertSargosWeightedSymmetricPhase f M H‖ := by
  have hs := robertSargos_initial_source_a_process f M H hH
  have hp : (0:ℝ) < H := by exact_mod_cast hH
  have hm : (H:ℝ) ≤ M := by exact_mod_cast hHM
  have hc : ((M:ℝ)+2*H)/H ≤ 3*(M:ℝ)/H :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hp)
  calc
    _ ≤ (((M:ℝ)+2*H)/H)*((M:ℝ)+2*‖robertSargosWeightedSymmetricPhase f M H‖) := hs
    _ ≤ (3*(M:ℝ)/H)*((M:ℝ)+2*‖robertSargosWeightedSymmetricPhase f M H‖) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
