import TaoTrudgianYang2025.PrimitiveDivisorGrowth
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Finite positive-displacement power sums, retaining and absorbing the
actual harmonic sum with an explicit epsilon-dependent constant. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem harmonic_le_rpow_loss (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N) :
    (harmonic N:ℝ) ≤ (1+1/ε)*(N:ℝ)^ε := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hone : 1 ≤ (N:ℝ)^ε := Real.one_le_rpow hN1 hε.le
  calc
    _ ≤ 1+Real.log N := harmonic_le_one_add_log N
    _ ≤ (N:ℝ)^ε+(N:ℝ)^ε/ε :=
      add_le_add hone (Real.log_le_rpow_div (Nat.cast_nonneg N) hε)
    _ = _ := by ring

theorem sum_positive_displacement_weight_le_harmonic
    {η A : ℝ} {N : ℕ} (hη : 0 ≤ η) (hA : 0 ≤ A) :
    (∑ n ∈ Finset.Icc 1 N, (n:ℝ)^η*(1+A/n)) ≤
      (N:ℝ)^η*((N:ℝ)+A*(harmonic N:ℝ)) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (N:ℝ)^η*(1+A/n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg n)
          (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hη) (by positivity)
    _ = (N:ℝ)^η*((N:ℝ)+A*(∑ n ∈ Finset.Icc 1 N, (n:ℝ)⁻¹)) := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [div_eq_mul_inv,Finset.sum_add_distrib,Finset.sum_const,
        Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one,← Finset.mul_sum]
    _ = _ := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem sum_positive_displacement_weight_le
    {ε A : ℝ} {N : ℕ} (hε : 0 < ε) (hA : 0 ≤ A) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(ε/2)*(1+A/n)) ≤
      (1+2/ε)*(N:ℝ)^ε*((N:ℝ)+A) := by
  have hη : 0 < ε/2 := by linarith
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have hpow : 1 ≤ (N:ℝ)^(ε/2) := Real.one_le_rpow hN1 hη.le
  have hconst : 1 ≤ 1+2/ε := by linarith [div_pos (by norm_num : (0:ℝ) < 2) hε]
  have hh : (harmonic N:ℝ) ≤ (1+2/ε)*(N:ℝ)^(ε/2) := by
    convert harmonic_le_rpow_loss (ε/2) hη hN using 1
    field_simp
  have hmain : (N:ℝ) ≤ (1+2/ε)*(N:ℝ)^(ε/2)*(N:ℝ) := by
    have hone : 1 ≤ (1+2/ε)*(N:ℝ)^(ε/2) :=
      one_le_mul_of_one_le_of_one_le hconst hpow
    nlinarith only [mul_le_mul_of_nonneg_right hone hNp.le]
  have hsq : (N:ℝ)^(ε/2)*(N:ℝ)^(ε/2) = (N:ℝ)^ε := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  calc
    _ ≤ (N:ℝ)^(ε/2)*((N:ℝ)+A*(harmonic N:ℝ)) :=
      sum_positive_displacement_weight_le_harmonic hη.le hA
    _ ≤ (N:ℝ)^(ε/2)*((1+2/ε)*(N:ℝ)^(ε/2)*(N:ℝ)+
        A*((1+2/ε)*(N:ℝ)^(ε/2))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hmain (mul_le_mul_of_nonneg_left hh hA)) (by positivity)
    _ = (1+2/ε)*((N:ℝ)^(ε/2)*(N:ℝ)^(ε/2))*((N:ℝ)+A) := by ring
    _ = _ := by rw [hsq]

end TaoTrudgianYang2025
