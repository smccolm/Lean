import TaoTrudgianYang2025.RobertSargosZeroRPrefix
import TaoTrudgianYang2025.RobertSargosZeroRSource

/-! Second-derivative control of the literal positive-q source correlation,
with its last endpoint charged and no exterior smoothness. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_r_source_positive_bound
    (f : ℝ → ℝ) (M : ℕ) (h q : ℤ) {C lam : ℝ}
    (hC : 0 ≤ C) (hh : 0 < h) (hq : 0 < q) (hlam : 0 < lam)
    (hscale : 2*(h:ℝ)*(q:ℝ)*lam ≤ 1)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    ‖robertSargosZeroRSource f M h q‖ ≤
      1+12*(C*M*Real.sqrt (2*(h:ℝ)*(q:ℝ)*lam)+
        2/Real.sqrt (2*(h:ℝ)*(q:ℝ)*lam)) := by
  have hhr : (0:ℝ) < h := by exact_mod_cast hh
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  unfold robertSargosZeroRSource
  rw [robertSargos_zero_r_positive_interval M h q hq.le]
  by_cases hab : h+1 ≤ (M:ℤ)-h-q
  · let L := ((M:ℤ)-h-q-(h+1)).toNat
    have hLint : (L:ℤ) = (M:ℤ)-h-q-(h+1) :=
      Int.toNat_of_nonneg (by omega)
    have hLreal : (L:ℝ) = (M:ℝ)-(h:ℝ)-(q:ℝ)-((h:ℝ)+1) := by
      exact_mod_cast hLint
    have hLM : (L:ℝ) ≤ M := by linarith
    have hp := robertSargos_zero_r_second_derivative_prefix f ((h:ℝ)+1) L
      hC hhr hqr hlam hscale (a := 1) (b := M)
      (by linarith) (by linarith [hLreal]) hf hlo hhi
    have hmono :
        12*(C*L*Real.sqrt (2*(h:ℝ)*(q:ℝ)*lam)+
          2/Real.sqrt (2*(h:ℝ)*(q:ℝ)*lam)) ≤
        12*(C*M*Real.sqrt (2*(h:ℝ)*(q:ℝ)*lam)+
          2/Real.sqrt (2*(h:ℝ)*(q:ℝ)*lam)) := by
      have hb := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLM hC) (Real.sqrt_nonneg (2*(h:ℝ)*(q:ℝ)*lam))
      linarith
    rw [sum_integer_Icc_eq_range_add _ _ _ hab]
    have hp' : ‖∑ n ∈ Finset.range ((M:ℤ)-h-q-(h+1)).toNat,
        fordAdditiveCharacter
          (robertSargosSymmetricDifference f (↑(h+1+(n:ℤ))+q) h-
            robertSargosSymmetricDifference f (↑(h+1+(n:ℤ))) h)‖ ≤
        12*(C*M*Real.sqrt (2*(h:ℝ)*(q:ℝ)*lam)+
          2/Real.sqrt (2*(h:ℝ)*(q:ℝ)*lam)) := by
      simpa only [Int.cast_add,Int.cast_one,Int.cast_natCast] using hp.trans hmono
    have he : ‖fordAdditiveCharacter
        (robertSargosSymmetricDifference f (↑((M:ℤ)-h-q)+q) h-
          robertSargosSymmetricDifference f (↑((M:ℤ)-h-q)) h)‖ = 1 := by
      simp [fordAdditiveCharacter,Complex.norm_exp]
    exact (norm_add_le _ _).trans (by linarith)
  · rw [Finset.Icc_eq_empty_of_lt (by omega : (M:ℤ)-h-q < h+1),
      Finset.sum_empty,norm_zero]
    positivity

end TaoTrudgianYang2025
