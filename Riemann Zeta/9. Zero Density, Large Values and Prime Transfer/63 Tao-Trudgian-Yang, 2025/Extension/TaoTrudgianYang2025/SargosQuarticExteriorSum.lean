import TaoTrudgianYang2025.SargosQuarticSharpCore
import TaoTrudgianYang2025.IntegerFourierWindows

/-! Logarithmic sums of actual quartic modes outside the support slope interval. -/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticExterior_right_harmonic {N α γ l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hsep : l+2*η ≤ b)
    (Q : ℤ) (hQ : sargosQuarticSlope α γ (N*(b-η)) ≤ (Q : ℝ)) (L : ℕ) :
    (∑ n ∈ Finset.range L, ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η)
      N α γ ((Q : ℝ)+((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < ((n+1 : ℕ) : ℝ) := by positivity
      have hg : ((n+1 : ℕ) : ℝ) ≤
          (Q : ℝ)+((n+1 : ℕ) : ℝ)-sargosQuarticSlope α γ (N*(b-η)) := by linarith
      have h := sargosQuarticBufferedFourierMode_right_of_support hN hα hγ hη hl hb hsep
        (show sargosQuarticSlope α γ (N*(b-η)) < (Q : ℝ)+((n+1 : ℕ) : ℝ) by linarith)
      apply h.trans
      calc
        _ ≤ 4/(((n+1 : ℕ) : ℝ)*Real.pi) :=
          div_le_div_of_nonneg_left (by norm_num) (mul_pos hnpos Real.pi_pos)
            (mul_le_mul_of_nonneg_right hg Real.pi_pos.le)
        _ = _ := by ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem sargosQuarticExterior_left_harmonic {N α γ l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hsep : l+2*η ≤ b)
    (Q : ℤ) (hQ : (Q : ℝ) ≤ sargosQuarticSlope α γ (N*(l+η))) (L : ℕ) :
    (∑ n ∈ Finset.range L, ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η)
      N α γ ((Q : ℝ)-((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < ((n+1 : ℕ) : ℝ) := by positivity
      have hg : ((n+1 : ℕ) : ℝ) ≤
          sargosQuarticSlope α γ (N*(l+η))-((Q : ℝ)-((n+1 : ℕ) : ℝ)) := by linarith
      have h := sargosQuarticBufferedFourierMode_left_of_support hN hα hγ hη hl hb hsep
        (show (Q : ℝ)-((n+1 : ℕ) : ℝ) < sargosQuarticSlope α γ (N*(l+η)) by linarith)
      apply h.trans
      calc
        _ ≤ 4/(((n+1 : ℕ) : ℝ)*Real.pi) :=
          div_le_div_of_nonneg_left (by norm_num) (mul_pos hnpos Real.pi_pos)
            (mul_le_mul_of_nonneg_right hg Real.pi_pos.le)
        _ = _ := by ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem sargosQuarticExterior_blocks_log {N α γ l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hsep : l+2*η ≤ b)
    (Lminus Lplus : ℕ) :
    ‖(∑ n ∈ Finset.range Lminus,
      sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ
        ((sargosQuarticSupportLower N α γ l η : ℝ)-((n+1 : ℕ) : ℝ)))+
      (∑ n ∈ Finset.range Lplus,
      sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ
        ((sargosQuarticSupportUpper N α γ b η : ℝ)+((n+1 : ℕ) : ℝ)))‖ ≤
      (4/Real.pi)*(2+Real.log (Lminus : ℝ)+Real.log (Lplus : ℝ)) := by
  have hm := sargosQuarticExterior_left_harmonic hN hα hγ hη hl hb hsep
    (sargosQuarticSupportLower N α γ l η) (Int.floor_le _) Lminus
  have hp := sargosQuarticExterior_right_harmonic hN hα hγ hη hl hb hsep
    (sargosQuarticSupportUpper N α γ b η) (Int.le_ceil _) Lplus
  calc
    _ ≤ (4/Real.pi)*(harmonic Lminus : ℝ)+(4/Real.pi)*(harmonic Lplus : ℝ) :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_sum_le _ _).trans hm) ((norm_sum_le _ _).trans hp))
    _ ≤ (4/Real.pi)*(1+Real.log (Lminus : ℝ))+
        (4/Real.pi)*(1+Real.log (Lplus : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Lminus) (by positivity))
        (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Lplus) (by positivity))
    _ = _ := by ring

end TaoTrudgianYang2025

