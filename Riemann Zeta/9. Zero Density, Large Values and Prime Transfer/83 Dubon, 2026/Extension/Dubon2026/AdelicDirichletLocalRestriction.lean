import Dubon2026.AdelicDirichletDeterminant
import Dubon2026.FinitePlaceDirichletDeterminant
import Dubon2026.AdelicCyclicFiniteSmooth

/-! # Exact local restriction of the original full adelic determinant character -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix

/-- The actual real idele coordinate of an adelic determinant is the determinant of the original real matrix coordinate. -/
theorem rationalIdeleRealHom_det (g : RationalAdelicGL2) :
    rationalIdeleRealHom (GeneralLinearGroup.det g) =
      GeneralLinearGroup.det (rationalAdelicGL2RealFiniteEquiv g).1 := by
  exact (GeneralLinearGroup.map_det ((RingHom.fst ℝ (FiniteAdeleRing ℤ ℚ)).comp
    rationalAdeleRealFiniteRingEquiv.toRingHom) g).symm

/-- The actual finite idele coordinate of an adelic determinant is the determinant of the original finite matrix coordinate. -/
theorem rationalIdeleFiniteHom_det (g : RationalAdelicGL2) :
    rationalIdeleFiniteHom (GeneralLinearGroup.det g) =
      GeneralLinearGroup.det (rationalAdelicGL2RealFiniteEquiv g).2 := by
  exact (GeneralLinearGroup.map_det ((RingHom.snd ℝ (FiniteAdeleRing ℤ ℚ)).comp
    rationalAdeleRealFiniteRingEquiv.toRingHom) g).symm

/-- Restricting the original full determinant character to the genuine finite subgroup gives precisely the original finite determinant character. -/
theorem adelicDirichletDeterminant_finite {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicDirichletDeterminant χ (rationalAdelicFiniteGL2Embedding g) =
      finiteIdeleDirichletCharacter χ (GeneralLinearGroup.det g) := by
  rw [adelicDirichletDeterminant_apply, adelicDirichletCharacter_apply,
    rationalIdeleRealHom_det, rationalIdeleFiniteHom_det, rationalAdelicFiniteGL2Embedding_coordinates]
  simp only [map_one, one_mul]

/-- The full adelic determinant character restricts to the character of the actual local matrix and original local determinant insertion. -/
theorem adelicDirichletDeterminant_local {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    adelicDirichletDeterminant χ (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) =
      finitePlaceDirichletDeterminant χ v g := by
  rw [adelicDirichletDeterminant_finite, finiteAdelicLocalGL2_det]
  rfl

end
end Dubon2026
