import GafniTao.FordQualitativeFiniteZeta

/-!
# The qualitative Vinogradov--Korobov zeta bound

This completes Ford's Lemma-7.3 consumer with the proved qualitative
exponential-sum constants.  The result is deliberately not labelled as
Ford's optimized numerical theorem.
-/

open Complex

namespace GafniTao

noncomputable section

def fordQualitativeZetaCoefficient : ℝ :=
  fordQualitativeCoefficient + 1 + fordTinyRemainder +
    1.569 * fordQualitativeCoefficient *
      (3000000 : ℝ) ^ ((1 : ℝ) / 3)

theorem fordQualitativeZetaCoefficient_nonneg :
    0 ≤ fordQualitativeZetaCoefficient := by
  unfold fordQualitativeZetaCoefficient
  have hC := fordQualitativeCoefficient_nonneg
  have htiny : 0 ≤ fordTinyRemainder := by
    unfold fordTinyRemainder
    positivity
  positivity

theorem norm_riemannZeta_le_ford_qualitative_expanded
    {sigma t : ℝ} (hsigmaLower : 15 / 16 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
      (fordQualitativeCoefficient + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) +
        (1.569 * fordQualitativeCoefficient *
          (3000000 : ℝ) ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) := by
  have htOne : 1 < t := by
    have hten : (1 : ℝ) < 10 := by norm_num
    have hpow : (1 : ℝ) < 10 ^ (100 : ℕ) := one_lt_pow₀ hten (by omega)
    exact hpow.trans_le ht
  have hsigmaNonneg : 0 ≤ sigma := by linarith
  let psum : ℂ :=
    ∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
      (n : ℂ) ^ (-fordComplexHeight sigma t)
  have hfinite : ‖psum‖ ≤
      1 + fordQualitativeCoefficient *
        (t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
    simpa [psum] using norm_fordPartialSum_le_qualitative
      hsigmaNonneg hsigmaUpper htOne
  have hrem : ‖riemannZeta (fordComplexHeight sigma t) - psum‖ ≤
      fordTinyRemainder := by
    simpa [psum] using norm_riemannZeta_sub_fordPartialSum_le_tiny
      hsigmaLower hsigmaUpper ht
  have hpeakNonneg :
      0 ≤ fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ) := by
    unfold fordSourceB
    positivity
  have hpower : 1 ≤
      t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.one_le_rpow htOne.le hpeakNonneg
  have hsplit : riemannZeta (fordComplexHeight sigma t) =
      psum + (riemannZeta (fordComplexHeight sigma t) - psum) := by ring
  rw [hsplit]
  calc
    ‖psum + (riemannZeta (fordComplexHeight sigma t) - psum)‖ ≤
        ‖psum‖ + ‖riemannZeta (fordComplexHeight sigma t) - psum‖ :=
      norm_add_le _ _
    _ ≤ (1 + fordQualitativeCoefficient *
        (t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3)))) + fordTinyRemainder :=
      add_le_add hfinite hrem
    _ ≤ (fordQualitativeCoefficient + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) +
        (1.569 * fordQualitativeCoefficient *
          (3000000 : ℝ) ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) := by
      have htiny : 0 ≤ fordTinyRemainder := by
        unfold fordTinyRemainder
        positivity
      have hC := fordQualitativeCoefficient_nonneg
      nlinarith [mul_nonneg (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) htiny)
        (sub_nonneg.mpr hpower)]

theorem norm_riemannZeta_le_ford_qualitative
    {sigma t : ℝ} (hsigmaLower : 15 / 16 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
      fordQualitativeZetaCoefficient *
        t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ ((2 : ℝ) / 3) := by
  have hraw := norm_riemannZeta_le_ford_qualitative_expanded
    hsigmaLower hsigmaUpper ht
  have htOne : 1 < t := by
    have hten : (1 : ℝ) < 10 := by norm_num
    exact (one_lt_pow₀ hten (by norm_num : (100 : ℕ) ≠ 0)).trans_le ht
  have hlog : 1 ≤ Real.log t := by
    have htenLog : (1 : ℝ) ≤ Real.log 10 := by
      linarith [twenty_three_tenths_lt_log_ten]
    have hbasePos : (0 : ℝ) < 10 ^ (100 : ℕ) := by positivity
    have htPos : 0 < t := hbasePos.trans_le ht
    have hlogMono : Real.log ((10 : ℝ) ^ (100 : ℕ)) ≤ Real.log t :=
      Real.strictMonoOn_log.monotoneOn hbasePos htPos ht
    rw [Real.log_pow] at hlogMono
    norm_num at hlogMono
    linarith
  have hlogPow : 1 ≤ Real.log t ^ ((2 : ℝ) / 3) :=
    Real.one_le_rpow hlog (by norm_num)
  have hpow : 0 ≤ t ^
      (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) := by positivity
  apply hraw.trans
  unfold fordQualitativeZetaCoefficient
  have htiny : 0 ≤ fordTinyRemainder := by
    unfold fordTinyRemainder
    positivity
  have hA : 0 ≤ fordQualitativeCoefficient + 1 + fordTinyRemainder := by
    exact add_nonneg
      (add_nonneg fordQualitativeCoefficient_nonneg (by norm_num)) htiny
  have hscale :
      (fordQualitativeCoefficient + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) ≤
        (fordQualitativeCoefficient + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) := by
    exact le_mul_of_one_le_right (mul_nonneg hA hpow) hlogPow
  calc
    (fordQualitativeCoefficient + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) +
        (1.569 * fordQualitativeCoefficient *
          (3000000 : ℝ) ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) ≤
      (fordQualitativeCoefficient + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) +
        (1.569 * fordQualitativeCoefficient *
          (3000000 : ℝ) ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) := add_le_add hscale le_rfl
    _ = (fordQualitativeCoefficient + 1 + fordTinyRemainder +
          1.569 * fordQualitativeCoefficient *
            (3000000 : ℝ) ^ ((1 : ℝ) / 3)) *
        t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ ((2 : ℝ) / 3) := by ring

#print axioms norm_riemannZeta_le_ford_qualitative_expanded
#print axioms norm_riemannZeta_le_ford_qualitative

end

end GafniTao
