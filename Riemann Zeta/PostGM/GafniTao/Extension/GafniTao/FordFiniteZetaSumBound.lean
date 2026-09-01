import GafniTao.FordCubicSourceBound

/-!
# Ford's finite Hurwitz-zeta sum bound

This is the complete dyadic/Abel/cubic consumer in Lemma 7.3, still with an
explicit natural truncation `M` and shell count `r`.  The subsequent source
endpoint module supplies `M = floor t` and Ford's ceiling choice of `r`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordFiniteHurwitzSum (sigma : ℝ) (M : ℕ) (u t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    (((n : ℝ) + u : ℝ) : ℂ) ^
      (-((sigma : ℂ) + (t : ℂ) * I))

theorem fordFiniteHurwitzSum_eq_weighted
    {sigma u t : ℝ} {M : ℕ} (hu : 0 < u) :
    fordFiniteHurwitzSum sigma M u t =
      ∑ n ∈ Finset.Icc 1 M,
        ((n : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase n u t := by
  unfold fordFiniteHurwitzSum
  apply Finset.sum_congr rfl
  intro n _hn
  exact (fordShiftedWeightedTerm_eq_cpow hu).symm

theorem norm_ford_first_weighted_term_le_one
    {sigma u t : ℝ} (hsigma : 0 ≤ sigma) (hu : 0 < u) :
    ‖((1 : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase 1 u t‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    norm_fordShiftedLogPhase, mul_one]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

/-- The source finite sum estimate, conditional only on Ford's Theorem 2 and
the exact endpoint relations needed by the dyadic partition. -/
theorem norm_fordFiniteHurwitzSum_le_source
    (hFord : FordTheorem2)
    {sigma u t : ℝ} {M r : ℕ}
    (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (hu : 0 < u) (huOne : u ≤ 1) (ht : 1 < t)
    (hMPos : 1 ≤ M) (hMt : (M : ℝ) ≤ t) (hMpow : M ≤ 2 ^ r) :
    ‖fordFiniteHurwitzSum sigma M u t‖ ≤
      1 + 9.463 *
        (t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * 133.66 ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
  rw [fordFiniteHurwitzSum_eq_weighted hu,
    ford_sum_Icc_eq_first_add_dyadic sigma hMPos hMpow]
  have htriangle := norm_add_le
    (((1 : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase 1 u t)
    (fordDyadicWeightedShellSum sigma r M u t)
  have hfirst := norm_ford_first_weighted_term_le_one (t := t) hsigmaLower hu
  have hshell := norm_fordDyadicWeightedShellSum_le_exponent_sum hFord
    (r := r) (M := M) hsigmaLower hu huOne ht hMt
  have hcubic := fordCubicExpSum_le_source hsigmaUpper
    (by norm_num : (0 : ℝ) < 133.66) ht r
  calc
    ‖((1 : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase 1 u t +
        fordDyadicWeightedShellSum sigma r M u t‖ ≤
        ‖((1 : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase 1 u t‖ +
          ‖fordDyadicWeightedShellSum sigma r M u t‖ := htriangle
    _ ≤ 1 + 9.463 *
          ∑ j ∈ Finset.range r,
            Real.exp (fordDyadicExponent 133.66 sigma t j) :=
      add_le_add hfirst hshell
    _ ≤ 1 + 9.463 *
        (t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * 133.66 ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
      gcongr

#print axioms fordFiniteHurwitzSum_eq_weighted
#print axioms norm_fordFiniteHurwitzSum_le_source

end

end GafniTao
