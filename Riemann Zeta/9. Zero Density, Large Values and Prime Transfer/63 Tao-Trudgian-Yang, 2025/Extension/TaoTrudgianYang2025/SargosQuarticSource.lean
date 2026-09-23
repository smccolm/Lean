import TaoTrudgianYang2025.SargosPlanarWindow

/-! The literal quadratic-plus-quartic source sum and its ordered-pair square. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosSourceInterval (N : ℕ) : Finset ℤ := Finset.Ioc (N : ℤ) (2*N)

def sargosQuarticSum (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) : ℂ :=
  sargosPlanarSum (sargosSourceInterval N) z (fun n => (n : ℝ)^2) (fun n => (n : ℝ)^4) α γ

def sargosPairCoefficient (z : ℤ → ℂ) (p : ℤ × ℤ) : ℂ := z p.1*z p.2

def sargosSquarePairFrequency (p : ℤ × ℤ) : ℝ := (p.1 : ℝ)^2+(p.2 : ℝ)^2

def sargosFourthPairFrequency (p : ℤ × ℤ) : ℝ := (p.1 : ℝ)^4+(p.2 : ℝ)^4

theorem sargosQuarticSum_eq_source (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosQuarticSum N z α γ =
      ∑ n ∈ Finset.Ioc (N : ℤ) (2*N),
        z n*fordAdditiveCharacter (α*(n : ℝ)^2+γ*(n : ℝ)^4) := by
  unfold sargosQuarticSum sargosSourceInterval sargosPlanarSum
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  ring

theorem sargosQuarticSum_sq_eq_pair_sum (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosQuarticSum N z α γ^2 =
      sargosPlanarSum ((sargosSourceInterval N) ×ˢ (sargosSourceInterval N))
        (sargosPairCoefficient z) sargosSquarePairFrequency sargosFourthPairFrequency α γ := by
  unfold sargosQuarticSum sargosPlanarSum
  rw [pow_two,Finset.sum_mul_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold sargosPairCoefficient sargosSquarePairFrequency sargosFourthPairFrequency
  calc
    _ = (z i*z j)*
        (fordAdditiveCharacter ((i : ℝ)^2*α+(i : ℝ)^4*γ)*
          fordAdditiveCharacter ((j : ℝ)^2*α+(j : ℝ)^4*γ)) := by ring
    _ = _ := by
      rw [← fordAdditiveCharacter_add]
      congr 2
      ring

theorem sargosQuarticSum_norm_four_eq_pair_norm_sq (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    ‖sargosQuarticSum N z α γ‖^4 =
      ‖sargosPlanarSum ((sargosSourceInterval N) ×ˢ (sargosSourceInterval N))
        (sargosPairCoefficient z) sargosSquarePairFrequency sargosFourthPairFrequency α γ‖^2 := by
  rw [← sargosQuarticSum_sq_eq_pair_sum,norm_pow]
  ring

theorem sargosPairCoefficient_norm_le_one {N : ℕ} {z : ℤ → ℂ}
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1) {p : ℤ × ℤ}
    (hp : p ∈ (sargosSourceInterval N) ×ˢ (sargosSourceInterval N)) :
    ‖sargosPairCoefficient z p‖ ≤ 1 := by
  have hpI := Finset.mem_product.mp hp
  rw [sargosPairCoefficient,norm_mul]
  nlinarith [hz p.1 hpI.1,hz p.2 hpI.2,norm_nonneg (z p.1),norm_nonneg (z p.2)]

end TaoTrudgianYang2025
