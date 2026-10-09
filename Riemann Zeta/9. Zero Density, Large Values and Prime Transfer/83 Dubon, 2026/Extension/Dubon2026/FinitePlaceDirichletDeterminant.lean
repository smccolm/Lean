import Dubon2026.FiniteIdeleCharacterUniformizer
import Dubon2026.FinitePlaceLevel

/-! # Genuine local determinant characters and their actual level-group values -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The determinant character of the actual local matrix group, using its genuine original finite-idele insertion. -/
def finitePlaceDirichletDeterminant {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (v : HeightOneSpectrum ℤ) :
    GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) →* ℂ :=
  (finiteIdeleDirichletCharacter χ).comp ((finiteAdeleLocalUnitHom v).comp GeneralLinearGroup.det)

/-- The original local determinant character evaluates the actual inserted determinant. -/
theorem finitePlaceDirichletDeterminant_apply {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    finitePlaceDirichletDeterminant χ v g =
      finiteIdeleDirichletCharacter χ (finiteAdeleLocalUnit v (GeneralLinearGroup.det g)) := rfl

/-- The determinant of an actual integral local level matrix is integral in the original local field. -/
theorem finitePlaceGL2Gamma0_det_integral (N : ℕ) (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (hg : g ∈ finitePlaceGL2Gamma0 N v) :
    (GeneralLinearGroup.det g).val ∈ v.adicCompletionIntegers ℚ := by
  change g.val.det ∈ v.adicCompletionIntegers ℚ
  rw [Matrix.det_fin_two]
  exact (v.adicCompletionIntegers ℚ).toSubring.sub_mem
    ((v.adicCompletionIntegers ℚ).toSubring.mul_mem (hg.1.1 0 0) (hg.1.1 1 1))
    ((v.adicCompletionIntegers ℚ).toSubring.mul_mem (hg.1.1 0 1) (hg.1.1 1 0))

/-- Away from the actual Dirichlet modulus, the constructed determinant character is trivial on the original local level group. -/
theorem finitePlaceDirichletDeterminant_level {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (N : ℕ) (v : HeightOneSpectrum ℤ)
    (hD : (D : ℤ) ∉ v.asIdeal) (g : finitePlaceGL2Gamma0 N v) :
    finitePlaceDirichletDeterminant χ v g.val = 1 := by
  apply finiteIdeleDirichletCharacter_local_integral χ v hD
  · exact finitePlaceGL2Gamma0_det_integral N v g.val g.property
  · have h := finitePlaceGL2Gamma0_det_integral N v g.val⁻¹
      ((finitePlaceGL2Gamma0 N v).inv_mem g.property)
    simpa only [map_inv] using h

end
end Dubon2026
