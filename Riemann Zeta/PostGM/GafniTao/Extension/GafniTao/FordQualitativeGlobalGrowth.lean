import GafniTao.FordQualitativeZetaBound
import GafniTao.FordBoundedHeight

/-!
# A global qualitative Ford zeta-growth bound

This file joins the six-range exponential-sum estimate to the two elementary
alternatives in Ford's Lemma 7.1 and then uses conjugation to cover negative
heights.  The constants are deliberately qualitative: the theorem is a proved
input for the zero-free and density arguments, not a claim that Ford's
optimized numerical constant `4.45` has been recovered.
-/

open Complex

namespace GafniTao

noncomputable section

def fordQualitativeGlobalCoefficient : ℝ :=
  58.1 + fordQualitativeZetaCoefficient

def FordQualitativeGlobalZetaGrowth : Prop :=
  ∀ ⦃sigma t : ℝ⦄, 1 / 2 ≤ sigma → sigma ≤ 1 → 3 ≤ |t| →
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      fordQualitativeGlobalCoefficient *
        |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log |t| ^ (2 / 3 : ℝ)

theorem four_le_fordSourceB_three_million :
    (4 : ℝ) ≤ fordSourceB 3000000 := by
  have hsqrt : (18 : ℝ) ≤ Real.sqrt (3 * 3000000) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  unfold fordSourceB
  nlinarith

theorem fordQualitativeGlobalCoefficient_nonneg :
    0 ≤ fordQualitativeGlobalCoefficient := by
  unfold fordQualitativeGlobalCoefficient
  linarith [fordQualitativeZetaCoefficient_nonneg]

theorem norm_riemannZeta_le_ford_qualitative_positive
    {sigma t : ℝ} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ t) :
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      fordQualitativeGlobalCoefficient *
        t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) := by
  have htOne : 1 ≤ t := by linarith
  have htPos : 0 < t := by linarith
  have heta : 0 ≤ (1 - sigma) ^ (3 / 2 : ℝ) := by positivity
  have hexp :
      4 * (1 - sigma) ^ (3 / 2 : ℝ) ≤
        fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right four_le_fordSourceB_three_million heta
  have hpow :
      t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) ≤
        t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le htOne hexp
  have hlogBaseNonneg : 0 ≤ Real.log t := Real.log_nonneg htOne
  have hlogNonneg : 0 ≤ Real.log t ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg hlogBaseNonneg _
  have htargetPowNonneg :
      0 ≤ t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) := by
    positivity
  have h58 : (58.1 : ℝ) ≤ fordQualitativeGlobalCoefficient := by
    unfold fordQualitativeGlobalCoefficient
    linarith [fordQualitativeZetaCoefficient_nonneg]
  have hqual :
      fordQualitativeZetaCoefficient ≤ fordQualitativeGlobalCoefficient := by
    unfold fordQualitativeGlobalCoefficient
    norm_num
  by_cases hsigmaLow : sigma ≤ 15 / 16
  · have hraw := norm_riemannZeta_le_ford_lowSigma
      hsigmaLower hsigmaLow ht
    calc
      ‖riemannZeta (sigma + Complex.I * t)‖ ≤
          58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            Real.log t ^ (2 / 3 : ℝ) := hraw
      _ ≤ fordQualitativeGlobalCoefficient *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            Real.log t ^ (2 / 3 : ℝ) := by
        gcongr
  · have hsigmaHigh : 15 / 16 ≤ sigma := le_of_not_ge hsigmaLow
    by_cases htBounded : t ≤ (10 : ℝ) ^ 100
    · have hraw := norm_riemannZeta_le_ford_boundedHeight
        hsigmaHigh hsigmaUpper ht htBounded
      calc
        ‖riemannZeta (sigma + Complex.I * t)‖ ≤
            58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
              Real.log t ^ (2 / 3 : ℝ) := hraw
        _ ≤ fordQualitativeGlobalCoefficient *
            t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
              Real.log t ^ (2 / 3 : ℝ) := by
          gcongr
    · have htLarge : (10 : ℝ) ^ 100 ≤ t := le_of_not_ge htBounded
      have hraw := norm_riemannZeta_le_ford_qualitative
        hsigmaHigh hsigmaUpper htLarge
      have hheight :
          fordComplexHeight sigma t = sigma + Complex.I * t := by
        simp [fordComplexHeight, mul_comm]
      rw [hheight] at hraw
      exact hraw.trans (by
        gcongr)

theorem norm_riemannZeta_height_abs
    (sigma t : ℝ) :
    ‖riemannZeta (sigma + Complex.I * t)‖ =
      ‖riemannZeta (sigma + Complex.I * |t|)‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · have htNeg : t < 0 := lt_of_not_ge ht
    have habs : |t| = -t := abs_of_neg htNeg
    rw [habs]
    have hstar :
        (starRingEnd ℂ) ((sigma : ℂ) + Complex.I * (-t : ℝ)) =
          (sigma : ℂ) + Complex.I * t := by
      apply Complex.ext <;> simp
    rw [← hstar, _root_.riemannZeta_conj, Complex.norm_conj]

theorem ford_qualitative_global_zeta_growth :
    FordQualitativeGlobalZetaGrowth := by
  intro sigma t hsigmaLower hsigmaUpper ht
  have hpos : 3 ≤ |t| := ht
  rw [norm_riemannZeta_height_abs sigma t]
  exact norm_riemannZeta_le_ford_qualitative_positive
    hsigmaLower hsigmaUpper hpos

#print axioms four_le_fordSourceB_three_million
#print axioms norm_riemannZeta_le_ford_qualitative_positive
#print axioms norm_riemannZeta_height_abs
#print axioms ford_qualitative_global_zeta_growth

end

end GafniTao
