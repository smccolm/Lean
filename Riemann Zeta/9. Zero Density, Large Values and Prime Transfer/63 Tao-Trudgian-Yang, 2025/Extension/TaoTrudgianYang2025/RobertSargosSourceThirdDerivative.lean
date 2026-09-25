import TaoTrudgianYang2025.RobertSargosSourceCenteredPhase
import TaoTrudgianYang2025.RobertSargosSymmetricThirdDerivative
import TaoTrudgianYang2025.IntegerClosedIntervalPrefix

/-! The standard third-derivative estimate on the literal source interval.
The last endpoint is charged so no derivative outside [1,M] is requested. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_source_centered_third_derivative_bound
    (f : ℝ → ℝ) (M : ℕ) (h : ℤ) {C lam : ℝ}
    (hC : 1 ≤ C) (hh : 0 < h) (hlam : 0 < lam)
    (hscale : 2*(h:ℝ)*lam ≤ 1)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    ‖robertSargosSourceCenteredPhase f M h‖ ≤
      1+20*C*((M:ℝ)*(2*(h:ℝ)*lam)^((1:ℝ)/6)+
        Real.sqrt M*(2*(h:ℝ)*lam)^(-(1:ℝ)/6)) := by
  have hhr : (0:ℝ) < h := by exact_mod_cast hh
  by_cases hab : h+1 ≤ (M:ℤ)-h
  · let L := ((M:ℤ)-h-(h+1)).toNat
    have hLint : (L:ℤ) = (M:ℤ)-h-(h+1) :=
      Int.toNat_of_nonneg (by omega)
    have hLreal : (L:ℝ) = (M:ℝ)-(h:ℝ)-((h:ℝ)+1) := by exact_mod_cast hLint
    have hLM : (L:ℝ) ≤ M := by linarith
    have hp := robertSargos_symmetric_third_derivative_prefix f ((h:ℝ)+1) L
      hC hhr hlam hscale
      (a := 1) (b := M) (by linarith) (by linarith [hLreal]) hf hlo hhi
    have hmono :
        20*C*((L:ℝ)*(2*(h:ℝ)*lam)^((1:ℝ)/6)+
          Real.sqrt L*(2*(h:ℝ)*lam)^(-(1:ℝ)/6)) ≤
        20*C*((M:ℝ)*(2*(h:ℝ)*lam)^((1:ℝ)/6)+
          Real.sqrt M*(2*(h:ℝ)*lam)^(-(1:ℝ)/6)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_right hLM (by positivity))
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hLM) (by positivity))
    unfold robertSargosSourceCenteredPhase
    rw [sum_integer_Icc_eq_range_add _ _ _ hab]
    have hp' : ‖∑ n ∈ Finset.range ((M:ℤ)-h-(h+1)).toNat,
        fordAdditiveCharacter (robertSargosSymmetricDifference f (↑(h+1+(n:ℤ))) h)‖ ≤
        20*C*((M:ℝ)*(2*(h:ℝ)*lam)^((1:ℝ)/6)+
          Real.sqrt M*(2*(h:ℝ)*lam)^(-(1:ℝ)/6)) := by
      simpa only [Int.cast_add,Int.cast_one,Int.cast_natCast] using hp.trans hmono
    have he : ‖fordAdditiveCharacter
        (robertSargosSymmetricDifference f (((M:ℤ)-h:ℤ):ℝ) h)‖ = 1 := by
      simp [fordAdditiveCharacter,Complex.norm_exp]
    exact (norm_add_le _ _).trans (by linarith)
  · have he : Finset.Icc (h+1) ((M:ℤ)-h) = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [robertSargosSourceCenteredPhase,he,Finset.sum_empty,norm_zero]
    positivity

end TaoTrudgianYang2025
