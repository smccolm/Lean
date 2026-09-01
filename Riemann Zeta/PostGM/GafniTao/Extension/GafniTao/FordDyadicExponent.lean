import GafniTao.FordDyadicDecomposition

/-!
# Ford's cubic dyadic exponent

This is the algebraic passage from the Theorem 2 power of `N=2^j` to the
literal cubic exponent `g(j)` in Lemma 7.3.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordDyadicExponent (D sigma t : ℝ) (j : ℕ) : ℝ :=
  (1 - sigma) * ((j : ℝ) * Real.log 2) -
    ((j : ℝ) * Real.log 2) ^ 3 / (D * Real.log t ^ 2)

theorem log_two_pow (j : ℕ) :
    Real.log ((2 ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log 2 := by
  rw [Nat.cast_pow, Real.log_pow]
  norm_num

theorem fordTheorem2_dyadic_power_eq_exp
    {sigma t D : ℝ} {j : ℕ}
    (ht : 1 < t) (hD : D ≠ 0) :
    ((2 ^ j : ℕ) : ℝ) ^ (-sigma) *
        (((2 ^ j : ℕ) : ℝ) ^
          (1 - 1 / (D * fordLambda (2 ^ j) t ^ 2))) =
      Real.exp (fordDyadicExponent D sigma t j) := by
  by_cases hj : j = 0
  · subst j
    simp [fordDyadicExponent]
  · have hN : 1 < 2 ^ j := by
      exact one_lt_pow₀ (by omega : 1 < (2 : ℕ)) hj
    have hlogN : Real.log (((2 ^ j : ℕ) : ℝ)) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hN))
    have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
    have hExponent :
        1 - 1 / (D * fordLambda (2 ^ j) t ^ 2) =
          1 - Real.log (((2 ^ j : ℕ) : ℝ)) ^ 2 /
            (D * Real.log t ^ 2) := by
      unfold fordLambda
      field_simp [hlogN, hlogt, hD]
    rw [hExponent]
    have hBase : 0 < (((2 ^ j : ℕ) : ℝ)) := by positivity
    rw [← Real.rpow_add hBase]
    rw [Real.rpow_def_of_pos hBase]
    congr 1
    rw [log_two_pow]
    unfold fordDyadicExponent
    ring

theorem fordDyadicRawMajorant_le_source
    {sigma u t : ℝ} {j : ℕ}
    (hsigma : 0 ≤ sigma) (hu : 0 < u) (ht : 1 < t) :
    fordDyadicRawMajorant sigma j u t ≤
      9.463 * Real.exp (fordDyadicExponent 133.66 sigma t j) := by
  have hBase : 0 < (((2 ^ j : ℕ) : ℝ)) := by positivity
  have hWeight :
      ((((2 ^ j + 1 : ℕ) : ℝ) + u) ^ (-sigma)) ≤
        (((2 ^ j : ℕ) : ℝ) ^ (-sigma)) := by
    apply Real.rpow_le_rpow_of_nonpos
    · exact hBase
    · norm_num
      linarith
    · linarith
  have hMajorantNonneg :
      0 ≤ fordTheorem2Majorant (2 ^ j) t := by
    unfold fordTheorem2Majorant
    positivity
  calc
    fordDyadicRawMajorant sigma j u t ≤
        (((2 ^ j : ℕ) : ℝ) ^ (-sigma)) *
          fordTheorem2Majorant (2 ^ j) t :=
      mul_le_mul_of_nonneg_right hWeight hMajorantNonneg
    _ = 9.463 *
        ((((2 ^ j : ℕ) : ℝ) ^ (-sigma)) *
          (((2 ^ j : ℕ) : ℝ) ^
            (1 - 1 / (133.66 * fordLambda (2 ^ j) t ^ 2)))) := by
      unfold fordTheorem2Majorant
      ring
    _ = 9.463 * Real.exp (fordDyadicExponent 133.66 sigma t j) := by
      rw [fordTheorem2_dyadic_power_eq_exp ht (by norm_num)]

theorem norm_fordDyadicWeightedShellSum_le_exponent_sum
    (hFord : FordTheorem2)
    {sigma u t : ℝ} {r M : ℕ}
    (hsigma : 0 ≤ sigma) (hu : 0 < u) (huOne : u ≤ 1)
    (ht : 1 < t) (hMt : (M : ℝ) ≤ t) :
    ‖fordDyadicWeightedShellSum sigma r M u t‖ ≤
      9.463 * ∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent 133.66 sigma t j) := by
  refine (norm_fordDyadicWeightedShellSum_le_raw_sum hFord
    hsigma hu huOne hMt).trans ?_
  calc
    (∑ j ∈ Finset.range r, fordDyadicRawMajorant sigma j u t) ≤
        ∑ j ∈ Finset.range r,
          9.463 * Real.exp (fordDyadicExponent 133.66 sigma t j) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact fordDyadicRawMajorant_le_source hsigma hu ht
    _ = 9.463 * ∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent 133.66 sigma t j) := by
      rw [Finset.mul_sum]

#print axioms log_two_pow
#print axioms fordTheorem2_dyadic_power_eq_exp
#print axioms fordDyadicRawMajorant_le_source
#print axioms norm_fordDyadicWeightedShellSum_le_exponent_sum

end

end GafniTao
