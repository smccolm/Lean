import Dubon2026.LocalInducedDiagonalValues

/-! # The genuine Borel-integral factorization of the original nonzero upper Hecke branch -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- The actual upper translation times inverse second diagonal has a literal lower-Borel and swap-unipotent factorization for every two original nonzero field units. -/
theorem gl2_upper_inverse_diagonal_factor {F : Type*} [Field F] (a q : Fˣ) :
    toGL (ringUpperUnipotent (-a.val)) * gl2UnitDiagonalPair 1 q⁻¹ =
      (toGL (ringLowerUnipotent (-(a⁻¹).val)) * gl2UnitDiagonalPair (-a * q⁻¹) a⁻¹) *
        (toGL (ringUpperUnipotent (-(q * a⁻¹).val)) * gl2CoordinateSwap) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2UnitDiagonalPair, ringUpperUnipotent, ringLowerUnipotent, toGL,
      gl2CoordinateSwap, Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
  field_simp

/-- An original integral local unit has character value one under its negative as well. -/
theorem finitePlaceUnramifiedCharacter_neg_integral (v : HeightOneSpectrum ℤ) (z : ℂˣ)
    (a : (v.adicCompletion ℚ)ˣ)
    (ha : a.val ∈ v.adicCompletionIntegers ℚ)
    (hai : a.inv ∈ v.adicCompletionIntegers ℚ) : finitePlaceUnramifiedCharacter v z (-a) = 1 := by
  apply finitePlaceUnramifiedCharacter_integral
  · exact (v.adicCompletionIntegers ℚ).toSubring.neg_mem ha
  · exact (v.adicCompletionIntegers ℚ).toSubring.neg_mem hai

/-- The actual unipotent-swap factor is an original integral matrix whenever its original parameters have the indicated genuine integrality. -/
theorem finitePlace_upper_inverse_factor_integral (v : HeightOneSpectrum ℤ)
    (a q : (v.adicCompletion ℚ)ˣ)
    (hai : a.inv ∈ v.adicCompletionIntegers ℚ)
    (hq : q.val ∈ v.adicCompletionIntegers ℚ) :
    toGL (ringUpperUnipotent (-(q * a⁻¹).val)) * gl2CoordinateSwap ∈ finitePlaceGL2Gamma0 1 v := by
  apply (finitePlaceGL2Gamma0 1 v).mul_mem
  · apply finitePlace_upperUnipotent_integral
    exact (v.adicCompletionIntegers ℚ).toSubring.neg_mem
      ((v.adicCompletionIntegers ℚ).toSubring.mul_mem hq hai)
  · exact finitePlace_coordinateSwap_integral v

end
end Dubon2026
