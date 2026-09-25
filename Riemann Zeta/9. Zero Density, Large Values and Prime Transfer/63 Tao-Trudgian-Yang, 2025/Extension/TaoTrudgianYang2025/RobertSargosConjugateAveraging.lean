import TaoTrudgianYang2025.RobertSargosConjugateGram
import TaoTrudgianYang2025.SignedEvenSum

/-! Initial conjugated A-process preserving the complete weighted correlation sum. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace TaoTrudgianYang2025

theorem robertSargos_even_gram_positive (a : ℤ → ℂ) (M H : ℕ) (hH : 0 < H) :
    (∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M,
      ‖∑ s ∈ Finset.range H, sargosPaddedSequence a M (n+2*s)‖^2) =
      (H:ℝ)*(∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2) +
      2*H*∑ h ∈ Finset.Ioo (0:ℤ) H,
        (1-(h:ℝ)/H)*robertSargosCenteredCorrelation a M h := by
  rw [robertSargos_even_gram,
    sum_signed_even (fun h => ((H-h.natAbs:ℕ):ℝ)*
      robertSargosCenteredCorrelation a M h) H hH
      (fun h => by simp only [Int.natAbs_neg,robertSargos_centered_correlation_neg])]
  simp only [Int.natAbs_zero,Nat.sub_zero,robertSargos_centered_correlation_zero]
  have hs :
      (∑ h ∈ Finset.Ioo (0:ℤ) H,
        ((H-h.natAbs:ℕ):ℝ)*robertSargosCenteredCorrelation a M h) =
      (H:ℝ)*∑ h ∈ Finset.Ioo (0:ℤ) H,
        (1-(h:ℝ)/H)*robertSargosCenteredCorrelation a M h := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have ht := Finset.mem_Ioo.mp hh
    have hi : h ∈ Finset.Ioo (-(H:ℤ)) H := Finset.mem_Ioo.mpr ⟨by omega,ht.2⟩
    have hp : (H:ℝ) ≠ 0 := by positivity
    rw [signed_shift_weight_real hi,abs_of_nonneg (by exact_mod_cast le_of_lt ht.1)]
    field_simp
  rw [hs]
  ring

theorem robertSargos_conjugate_a_process (a : ℤ → ℂ) (M H : ℕ) (hH : 0 < H) :
    ‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^2 ≤
      (((M:ℝ)+2*H)/H)*((∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2)+
        2*∑ h ∈ Finset.Ioo (0:ℤ) H,
          (1-(h:ℝ)/H)*robertSargosCenteredCorrelation a M h) := by
  have hp : (0:ℝ) < H := by exact_mod_cast hH
  have hs := sargos_even_shift_averaging a M H
  rw [robertSargos_even_gram_positive a M H hH] at hs
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hs
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).mpr
  apply (mul_le_mul_iff_right₀ hp).mp
  convert hs using 1 <;> ring

end TaoTrudgianYang2025
