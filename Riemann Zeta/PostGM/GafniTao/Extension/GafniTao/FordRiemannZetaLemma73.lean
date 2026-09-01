import GafniTao.FordFiniteZetaUnshifted
import GafniTao.FordLemma73Coefficient

/-!
# Ford Lemma 7.3 for ordinary Riemann zeta

This is the literal first inequality of Ford's Lemma 7.3.  The unshifted
finite estimate is paired with the `floor t + 1/2` Dadaro truncation, so no
artificial first-term loss enters the coefficient.
-/

open Complex

namespace GafniTao

noncomputable section

theorem norm_riemannZeta_le_fordLemma73_expanded
    (hFord : FordTheorem2) {sigma t : ℝ}
    (hsigmaLower : 15 / 16 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
      (9.463 + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) +
        (1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
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
      1 + 9.463 *
        (t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * 133.66 ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
    simpa [psum] using norm_fordPartialSum_le_source hFord
      hsigmaNonneg hsigmaUpper htOne
  have hrem :
      ‖riemannZeta (fordComplexHeight sigma t) - psum‖ ≤
        fordTinyRemainder := by
    simpa [psum] using norm_riemannZeta_sub_fordPartialSum_le_tiny
      hsigmaLower hsigmaUpper ht
  have hpeakNonneg :
      0 ≤ fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ) := by
    unfold fordSourceB
    positivity
  have hpower :
      1 ≤ t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.one_le_rpow htOne.le hpeakNonneg
  have hsplit :
      riemannZeta (fordComplexHeight sigma t) =
        psum + (riemannZeta (fordComplexHeight sigma t) - psum) := by ring
  rw [hsplit]
  calc
    ‖psum + (riemannZeta (fordComplexHeight sigma t) - psum)‖ ≤
        ‖psum‖ + ‖riemannZeta (fordComplexHeight sigma t) - psum‖ :=
      norm_add_le _ _
    _ ≤
        (1 + 9.463 *
          (t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            (1 + 1.569 * 133.66 ^ ((1 : ℝ) / 3) *
              Real.log t ^ ((2 : ℝ) / 3)))) + fordTinyRemainder :=
      add_le_add hfinite hrem
    _ ≤
      (9.463 + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) +
        (1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) := by
      have htiny : 0 ≤ fordTinyRemainder := by
        unfold fordTinyRemainder
        positivity
      nlinarith [mul_nonneg (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) htiny)
        (sub_nonneg.mpr hpower)]

theorem norm_riemannZeta_le_fordLemma73
    (hFord : FordTheorem2) {sigma t : ℝ}
    (hsigmaLower : 15 / 16 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
      ((9.463 + 1 + fordTinyRemainder) /
          Real.log t ^ ((2 : ℝ) / 3) +
        1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
        t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ ((2 : ℝ) / 3) := by
  have hraw := norm_riemannZeta_le_fordLemma73_expanded hFord
    hsigmaLower hsigmaUpper ht
  have htOne : 1 < t := by
    have hten : (1 : ℝ) < 10 := by norm_num
    have hpow : (1 : ℝ) < 10 ^ (100 : ℕ) := one_lt_pow₀ hten (by omega)
    exact hpow.trans_le ht
  have hlog : 0 < Real.log t := Real.log_pos htOne
  have hlogPow : 0 < Real.log t ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hlog _
  calc
    ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
      (9.463 + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) +
        (1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) := hraw
    _ = ((9.463 + 1 + fordTinyRemainder) /
          Real.log t ^ ((2 : ℝ) / 3) +
        1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
        t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ ((2 : ℝ) / 3) := by
      field_simp [hlogPow.ne']

theorem norm_riemannZeta_le_76_2
    (hFord : FordTheorem2) {sigma t : ℝ}
    (hsigmaLower : 15 / 16 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
      76.2 * t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ ((2 : ℝ) / 3) := by
  have h73 := norm_riemannZeta_le_fordLemma73 hFord
    hsigmaLower hsigmaUpper ht
  have hcoeff := fordLemma73_coefficient_le_76_2 ht
  have hpow : 0 ≤ t ^
      (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) := by positivity
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by
    have : (1 : ℝ) ≤ (10 : ℝ) ^ 100 := by norm_num
    exact this.trans ht)
  exact h73.trans (by gcongr)

#print axioms norm_riemannZeta_le_fordLemma73_expanded
#print axioms norm_riemannZeta_le_fordLemma73
#print axioms norm_riemannZeta_le_76_2

end

end GafniTao
