import TaoTrudgianYang2025.RobertSargosZeroQFullPrefix
import TaoTrudgianYang2025.IntegerClosedIntervalPrefix
import TaoTrudgianYang2025.RobertSargosCorrelationBoundary

/-! The true zero-q source interval retains both h and h+r endpoints. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

def robertSargosZeroQSource (f : ℝ → ℝ) (M : ℕ) (h r : ℤ) : ℂ :=
  ∑ m ∈ robertSargosMOverlap M h 0 r, fordAdditiveCharacter
    (robertSargosSymmetricDifference f m h-robertSargosSymmetricDifference f m (h+r))

theorem robertSargos_zero_q_source_bound
    (f : ℝ → ℝ) (M : ℕ) (h r : ℤ) {C lam : ℝ}
    (hh : 0 ≤ h) (hhr : 0 ≤ h+r) (hr : r ≠ 0)
    (hC : 1 ≤ C) (hlam : 0 < lam) (hscale : 2*|(r:ℝ)| *lam ≤ 1)
    (hM : (2*|(r:ℝ)| *lam)^(-(1:ℝ)/2) ≤ M)
    (hslow : C*lam*((h:ℝ)^3+((h:ℝ)+r)^3)/3 ≤ C*Real.sqrt (2*|(r:ℝ)| *lam))
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    ‖robertSargosZeroQSource f M h r‖ ≤
      1+120*C*(1+2*Real.pi*C)*M*(2*|(r:ℝ)| *lam)^((1:ℝ)/12) := by
  let a := max (h+1) (h+r+1)
  let b := min ((M:ℤ)-h) ((M:ℤ)-h-r)
  have ha1 : h+1 ≤ a := le_max_left _ _
  have ha2 : h+r+1 ≤ a := le_max_right _ _
  have hb1 : b ≤ (M:ℤ)-h := min_le_left _ _
  have hb2 : b ≤ (M:ℤ)-h-r := min_le_right _ _
  have hCp : 0 ≤ C := zero_le_one.trans hC
  unfold robertSargosZeroQSource
  simp only [robertSargosMOverlap,sub_zero]
  change ‖∑ m ∈ Finset.Icc a b, fordAdditiveCharacter
    (robertSargosSymmetricDifference f m h-robertSargosSymmetricDifference f m (h+r))‖ ≤ _
  by_cases hab : a ≤ b
  · let L := (b-a).toNat
    have hLi : (L:ℤ) = b-a := Int.toNat_of_nonneg (by omega)
    have hLr : (L:ℝ) = (b:ℝ)-a := by exact_mod_cast hLi
    have hLM : (L:ℝ) ≤ M := by
      exact_mod_cast (show (L:ℤ) ≤ M by omega)
    have hp := robertSargos_zero_q_full_prefix f (a:ℝ) L
      (a := 1) (b := M) (h := (h:ℝ)) (r := (r:ℝ))
      (by exact_mod_cast hh) (by exact_mod_cast hhr) (by exact_mod_cast hr)
      hC hCp hlam hscale hLM hM hslow
      (by exact_mod_cast (show 1 ≤ a-h by omega))
      (by
        rw [hLr]
        have hc : (b:ℝ)+(h:ℝ) ≤ M := by exact_mod_cast (show b+h ≤ M by omega)
        linarith)
      (by exact_mod_cast (show 1 ≤ a-(h+r) by omega))
      (by
        rw [hLr]
        have hc : (b:ℝ)+((h:ℝ)+r) ≤ M := by exact_mod_cast (show b+(h+r) ≤ M by omega)
        linarith) hf hlo hhi
    rw [sum_integer_Icc_eq_range_add _ _ _ hab]
    have hp' : ‖∑ n ∈ Finset.range (b-a).toNat, fordAdditiveCharacter
        (robertSargosSymmetricDifference f (↑(a+(n:ℤ))) h -
          robertSargosSymmetricDifference f (↑(a+(n:ℤ))) (h+r))‖ ≤
        120*C*(1+2*Real.pi*C)*M*(2*|(r:ℝ)| *lam)^((1:ℝ)/12) := by
      simpa only [Int.cast_add,Int.cast_natCast] using hp
    have he := sargos_character_norm
      (robertSargosSymmetricDifference f b h-robertSargosSymmetricDifference f b (h+r))
    exact (norm_add_le _ _).trans (by linarith)
  · rw [Finset.Icc_eq_empty_of_lt (by omega : b < a),Finset.sum_empty,norm_zero]
    positivity

end TaoTrudgianYang2025
