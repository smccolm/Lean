import GafniTao.ClassicalBinaryShellExtraction
import RiemannZeta.GuthMaynard.TypeIFiniteWindow

/-!
# Unit-coefficient normalization of the binary shell detector

The classical detector returns fixed-line coefficients containing the factor
`n^{-sigma}`.  Heath--Brown's mean-value inequalities require coefficients of
modulus at most one and a threshold on the `N^sigma` scale.  This file proves
that normalization for both source signs and, separately, proves the exact
sharp-mollifier normalization at its selected Type-II scale.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Signed version of the source Type-I normalization. -/
noncomputable def signedNormalizedClassicalTypeICoeff
    (A N : Nat) (sigma : Real) (sign : Fin 2) (n : Nat) : Complex :=
  if sign = 0 then
    conjugateCoeffs (normalizedClassicalTypeICoeff A N sigma) n
  else
    normalizedClassicalTypeICoeff A N sigma n

theorem signedNormalizedClassicalTypeICoeff_eq_scale
    (A N : Nat) (sigma : Real) (sign : Fin 2) :
    signedNormalizedClassicalTypeICoeff A N sigma sign =
      fun n => (((N : Real) ^ sigma : Real) : Complex) *
        signedClassicalLongCoeff A sigma sign n := by
  funext n
  fin_cases sign <;>
    simp [signedNormalizedClassicalTypeICoeff,
      signedClassicalLongCoeff, normalizedClassicalTypeICoeff,
      conjugateCoeffs]

theorem sourceDirichletPoly_signedNormalizedClassicalTypeICoeff
    (A N : Nat) (sigma t : Real) (sign : Fin 2) :
    sourceDirichletPoly N
        (signedNormalizedClassicalTypeICoeff A N sigma sign) t =
      (((N : Real) ^ sigma : Real) : Complex) *
        sourceDirichletPoly N (signedClassicalLongCoeff A sigma sign) t := by
  rw [signedNormalizedClassicalTypeICoeff_eq_scale]
  unfold sourceDirichletPoly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem norm_signedNormalizedClassicalTypeICoeff_le_one
    (A N : Nat) (sigma : Real) (sign : Fin 2)
    (hN : 0 < N) (hsigma : 0 ≤ sigma) :
    ∀ n ∈ dyadicInterval N,
      ‖signedNormalizedClassicalTypeICoeff A N sigma sign n‖ ≤ 1 := by
  intro n hn
  by_cases hsign : sign = 0
  · subst sign
    rw [show signedNormalizedClassicalTypeICoeff A N sigma 0 n =
          conjugateCoeffs (normalizedClassicalTypeICoeff A N sigma) n by
        simp [signedNormalizedClassicalTypeICoeff]]
    rw [norm_conjugateCoeffs]
    exact norm_normalizedClassicalTypeICoeff_le_one A N sigma hN hsigma n hn
  · simpa [signedNormalizedClassicalTypeICoeff, hsign] using
      norm_normalizedClassicalTypeICoeff_le_one A N sigma hN hsigma n hn

theorem signedNormalizedClassicalTypeICoeff_large
    (A N : Nat) (sigma t L : Real) (sign : Fin 2) (hN : 0 < N)
    (hLarge : L ≤
      ‖sourceDirichletPoly N (signedClassicalLongCoeff A sigma sign) t‖) :
    (N : Real) ^ sigma * L ≤
      ‖sourceDirichletPoly N
        (signedNormalizedClassicalTypeICoeff A N sigma sign) t‖ := by
  rw [sourceDirichletPoly_signedNormalizedClassicalTypeICoeff,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by exact_mod_cast hN.le) _)]
  exact mul_le_mul_of_nonneg_left hLarge
    (Real.rpow_nonneg (by exact_mod_cast hN.le) _)

/-- Signed Type-II coefficients normalized at one actual selected length. -/
noncomputable def signedNormalizedClassicalTypeIICoeff
    (Y X N : Nat) (sigma eta C : Real) (sign : Fin 2) (n : Nat) : Complex :=
  if sign = 0 then
    conjugateCoeffs
      (normalizedSharpMollifiedLineCoeff Y X N sigma eta C) n
  else
    normalizedSharpMollifiedLineCoeff Y X N sigma eta C n

theorem signedNormalizedClassicalTypeIICoeff_eq_div
    (Y X N : Nat) (sigma eta C : Real) (sign : Fin 2) :
    signedNormalizedClassicalTypeIICoeff Y X N sigma eta C sign =
      fun n => signedSharpMollifiedLineCoeff Y X sigma sign n /
        ((C * (2 * N : Real) ^ eta * (N : Real) ^ (-sigma) : Real) :
          Complex) := by
  funext n
  fin_cases sign <;>
    simp [signedNormalizedClassicalTypeIICoeff,
      signedSharpMollifiedLineCoeff, normalizedSharpMollifiedLineCoeff,
      conjugateCoeffs]

theorem sourceDirichletPoly_signedNormalizedClassicalTypeIICoeff
    (Y X N : Nat) (sigma eta C t : Real) (sign : Fin 2) :
    sourceDirichletPoly N
        (signedNormalizedClassicalTypeIICoeff Y X N sigma eta C sign) t =
      sourceDirichletPoly N (signedSharpMollifiedLineCoeff Y X sigma sign) t /
        ((C * (2 * N : Real) ^ eta * (N : Real) ^ (-sigma) : Real) :
          Complex) := by
  rw [signedNormalizedClassicalTypeIICoeff_eq_div]
  unfold sourceDirichletPoly
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  rw [div_mul_eq_mul_div]

theorem norm_signedNormalizedClassicalTypeIICoeff_le_one
    (Y X N : Nat) (sigma eta C : Real) (sign : Fin 2)
    (hN : 0 < N) (hsigma : 0 ≤ sigma) (heta : 0 ≤ eta) (hC : 0 < C)
    (hCoeff : ∀ n : Nat, 0 < n →
      ‖sharpMollifiedCoeff Y X n‖ ≤ C * (n : Real) ^ eta) :
    ∀ n ∈ dyadicInterval N,
      ‖signedNormalizedClassicalTypeIICoeff
        Y X N sigma eta C sign n‖ ≤ 1 := by
  intro n hn
  by_cases hsign : sign = 0
  · subst sign
    rw [show signedNormalizedClassicalTypeIICoeff
            Y X N sigma eta C 0 n =
          conjugateCoeffs
            (normalizedSharpMollifiedLineCoeff Y X N sigma eta C) n by
        simp [signedNormalizedClassicalTypeIICoeff]]
    rw [norm_conjugateCoeffs]
    exact norm_normalizedSharpMollifiedLineCoeff_le_one
      Y X N n sigma eta C hN hsigma heta hC hCoeff hn
  · simpa [signedNormalizedClassicalTypeIICoeff, hsign] using
      norm_normalizedSharpMollifiedLineCoeff_le_one
        Y X N n sigma eta C hN hsigma heta hC hCoeff hn

theorem signedNormalizedClassicalTypeIICoeff_large
    (Y X N : Nat) (sigma eta C t L : Real) (sign : Fin 2)
    (hN : 0 < N) (hC : 0 < C)
    (hLarge : L ≤
      ‖sourceDirichletPoly N
        (signedSharpMollifiedLineCoeff Y X sigma sign) t‖) :
    L / (C * (2 * N : Real) ^ eta * (N : Real) ^ (-sigma)) ≤
      ‖sourceDirichletPoly N
        (signedNormalizedClassicalTypeIICoeff
          Y X N sigma eta C sign) t‖ := by
  have hScale : 0 < C * (2 * N : Real) ^ eta *
      (N : Real) ^ (-sigma) := by
    have hNReal : (0 : Real) < N := by exact_mod_cast hN
    positivity
  rw [sourceDirichletPoly_signedNormalizedClassicalTypeIICoeff,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hScale]
  exact div_le_div_of_nonneg_right hLarge hScale.le

#print axioms norm_signedNormalizedClassicalTypeICoeff_le_one
#print axioms signedNormalizedClassicalTypeICoeff_large
#print axioms norm_signedNormalizedClassicalTypeIICoeff_le_one
#print axioms signedNormalizedClassicalTypeIICoeff_large

end


end GafniTao
