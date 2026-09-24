import TaoTrudgianYang2025.ZetaRealMomentLargeValues
import TaoTrudgianYang2025.DirichletBlockPhase
import GuthMaynard.ZetaTruncation
import GuthMaynard.LargeValuesS3

/-!
# First moment of the literal Dirichlet prefix on Re s = 1

The n=1 term contributes the interval length. Every other term is
integrated as an actual oscillatory exponential, with a harmonic loss.
-/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

def zetaOneLineTerm (n : ℕ) (t : ℝ) : ℂ :=
  (n : ℂ)^(-(1+(t : ℂ)*I))

theorem zetaOneLineTerm_eq {n : ℕ} (hn : 0 < n) (t : ℝ) :
    zetaOneLineTerm n t =
      (n : ℂ)⁻¹*Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*I) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold zetaOneLineTerm
  rw [show -(1+(t : ℂ)*I) = -1+(-(I*(t : ℂ))) by ring,
    Complex.cpow_add _ _ hn0, Complex.cpow_neg_one]
  change (n : ℂ)⁻¹*dirichletPhase n t = _
  rw [dirichletPhase_eq_exp hn]
  congr 2
  push_cast
  ring

theorem continuous_zetaOneLineTerm {n : ℕ} (hn : 0 < n) :
    Continuous (zetaOneLineTerm n) := by
  have heq : zetaOneLineTerm n = fun t =>
      (n : ℂ)⁻¹*Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*I) :=
    funext (zetaOneLineTerm_eq hn)
  rw [heq]
  fun_prop

theorem norm_integral_zetaOneLineTerm {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    ‖∫ t in a..b, zetaOneLineTerm n t‖ ≤
      (2/Real.log 2)*(n : ℝ)⁻¹ := by
  have hnp : 0 < n := by omega
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp_rw [zetaOneLineTerm_eq hnp]
  rw [intervalIntegral.integral_const_mul,norm_mul,norm_inv,Complex.norm_natCast]
  change (n : ℝ)⁻¹*‖gmPhaseIntervalKernel a b (-Real.log (n : ℝ))‖ ≤ _
  have hk := norm_gmPhaseIntervalKernel_le_two_div
    (a := a) (b := b) (neg_ne_zero.mpr hlog.ne')
  rw [abs_neg,abs_of_pos hlog] at hk
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnr
  calc
    _ ≤ (n : ℝ)⁻¹*(2/Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ ≤ (n : ℝ)⁻¹*(2/Real.log 2) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by norm_num) htwo hl)
        (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = _ := by ring

theorem norm_integral_zetaOneLinePrefix_sub_length {b : ℕ} (hb : 1 ≤ b)
    (a d : ℝ) :
    ‖(∫ t in a..d, ∑ n ∈ Finset.Icc 1 b, zetaOneLineTerm n t) -
      ((d-a : ℝ) : ℂ)‖ ≤ (2/Real.log 2)*(1+Real.log (b : ℝ)) := by
  let S := Finset.Icc 1 b
  have hOne : 1 ∈ S := Finset.mem_Icc.mpr ⟨le_rfl,hb⟩
  have heq : (∫ t in a..d, ∑ n ∈ S, zetaOneLineTerm n t) -
      ((d-a : ℝ) : ℂ) = ∑ n ∈ S.erase 1, ∫ t in a..d, zetaOneLineTerm n t := by
    rw [intervalIntegral.integral_finsetSum
      (fun n hn => (continuous_zetaOneLineTerm (by
        have hh := (Finset.mem_Icc.mp hn).1
        omega)).intervalIntegrable a d)]
    rw [← Finset.sum_erase_add S _ hOne]
    simp [zetaOneLineTerm]
  rw [heq]
  have hsum : (∑ n ∈ S.erase 1, (n : ℝ)⁻¹) ≤ (harmonic b : ℝ) := by
    have hh : (harmonic b : ℝ) = ∑ n ∈ S, (n : ℝ)⁻¹ := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,S]
    rw [hh]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  calc
    _ ≤ ∑ n ∈ S.erase 1, ‖∫ t in a..d, zetaOneLineTerm n t‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S.erase 1, (2/Real.log 2)*(n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hn
      have hnl := (Finset.mem_Icc.mp hm).1
      exact norm_integral_zetaOneLineTerm (by omega) a d
    _ = (2/Real.log 2)*∑ n ∈ S.erase 1, (n : ℝ)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ (2/Real.log 2)*(harmonic b : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log b) (by positivity)

end TaoTrudgianYang2025
