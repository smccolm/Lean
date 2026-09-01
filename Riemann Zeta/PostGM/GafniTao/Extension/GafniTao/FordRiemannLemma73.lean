import GafniTao.FordDadaroTinyRemainder

/-!
# Ford Lemma 7.3 for the Riemann-zeta consumer

This specializes the finite exponential-sum estimate to `u = 1` and combines
it with the now-proved Dadaro remainder.  The only remaining upstream premise
is Ford's exponential-sum Theorem 2.
-/

open Complex

namespace GafniTao

noncomputable section

theorem riemannZeta_sub_head_eq_finite_add_dadaroRemainder
    (sigma t : ℝ) :
    riemannZeta (fordComplexHeight sigma t) - fordHurwitzHead sigma 1 t =
      fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) 1 t +
        (riemannZeta (fordComplexHeight sigma t) -
          fordHurwitzFiniteApproximation sigma 1 t) := by
  unfold fordHurwitzFiniteApproximation
  ring

theorem norm_riemannZeta_sub_head_le_expanded
    (hFord : FordTheorem2) {sigma t : ℝ}
    (hsigmaLower : 15 / 16 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t) - fordHurwitzHead sigma 1 t‖ ≤
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
  have hfinite := norm_fordFiniteHurwitzSum_floor_le_source hFord
    hsigmaNonneg hsigmaUpper (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 1) htOne
  have hrem := norm_riemannZeta_sub_fordFiniteApproximation_le_tiny
    hsigmaLower hsigmaUpper ht
  have hpeakNonneg :
      0 ≤ fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ) := by
    unfold fordSourceB
    positivity
  have hpower :
      1 ≤ t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.one_le_rpow htOne.le hpeakNonneg
  rw [riemannZeta_sub_head_eq_finite_add_dadaroRemainder]
  calc
    ‖fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) 1 t +
        (riemannZeta (fordComplexHeight sigma t) -
          fordHurwitzFiniteApproximation sigma 1 t)‖ ≤
        ‖fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) 1 t‖ +
          ‖riemannZeta (fordComplexHeight sigma t) -
            fordHurwitzFiniteApproximation sigma 1 t‖ := norm_add_le _ _
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

theorem norm_riemannZeta_sub_head_le_lemma73
    (hFord : FordTheorem2) {sigma t : ℝ}
    (hsigmaLower : 15 / 16 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t) - fordHurwitzHead sigma 1 t‖ ≤
      ((9.463 + 1 + fordTinyRemainder) /
          Real.log t ^ ((2 : ℝ) / 3) +
        1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
        t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ ((2 : ℝ) / 3) := by
  have hraw := norm_riemannZeta_sub_head_le_expanded hFord
    hsigmaLower hsigmaUpper ht
  have htOne : 1 < t := by
    have hten : (1 : ℝ) < 10 := by norm_num
    have hpow : (1 : ℝ) < 10 ^ (100 : ℕ) := one_lt_pow₀ hten (by omega)
    exact hpow.trans_le ht
  have hlog : 0 < Real.log t := Real.log_pos htOne
  have hlogPow : 0 < Real.log t ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hlog _
  calc
    ‖riemannZeta (fordComplexHeight sigma t) - fordHurwitzHead sigma 1 t‖ ≤
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

#print axioms riemannZeta_sub_head_eq_finite_add_dadaroRemainder
#print axioms norm_riemannZeta_sub_head_le_expanded
#print axioms norm_riemannZeta_sub_head_le_lemma73

end

end GafniTao
