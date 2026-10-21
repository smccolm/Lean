import Dubon2026.SourceOriginalGaloisFinite
import Dubon2026.SourceCurveCoordinateExchange

/-! DUB-17/18 -> global residue identity -> auxiliary Galois local geometry.
The actual normal closure is finite over the image of the original j-field,
and hence over any transcendental coordinate. Native adjoin-algebra maps
and restriction of scalars supply the first bridge; the existing proved
transcendence-coordinate exchange supplies the second.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The original transcendental j-coordinate in its actual normal closure. -/
def originalGaloisJ : originalGaloisClosure N L :=
  algebraMap (modularFunctionFieldOver N L) (originalGaloisClosure N L) (jOver N L)

theorem finite_originalGaloisClosure_over_coordinate :
    FiniteDimensional (IntermediateField.adjoin L {originalGaloisJ N L})
      (originalGaloisClosure N L) := by
  haveI := finite_originalGaloisClosure_over_j N L
  letI : Algebra (IntermediateField.adjoin L {jOver N L})
      (IntermediateField.adjoin L {originalGaloisJ N L}) :=
    (IntermediateField.RingHom.adjoinAlgebraMap (A := L)
      (C := originalGaloisClosure N L) (jOver N L)).toAlgebra
  letI : SMul (IntermediateField.adjoin L {jOver N L})
      (IntermediateField.adjoin L {originalGaloisJ N L}) :=
    (inferInstance : Algebra (IntermediateField.adjoin L {jOver N L})
      (IntermediateField.adjoin L {originalGaloisJ N L})).toSMul
  letI : IsScalarTower (IntermediateField.adjoin L {jOver N L})
      (IntermediateField.adjoin L {originalGaloisJ N L}) (originalGaloisClosure N L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin L {jOver N L})
    (IntermediateField.adjoin L {originalGaloisJ N L}) (originalGaloisClosure N L)

theorem finite_originalGaloisClosure_over_transcendental
    {t : originalGaloisClosure N L} (ht : Transcendental L t) :
    FiniteDimensional (IntermediateField.adjoin L {t}) (originalGaloisClosure N L) := by
  let F := originalGaloisClosure N L
  let J := IntermediateField.adjoin L ({originalGaloisJ N L} : Set F)
  let T := IntermediateField.adjoin L ({t} : Set F)
  letI : Algebra L J := J.toSubalgebra.algebra
  letI : Algebra L T := T.toSubalgebra.algebra
  haveI : FiniteDimensional J F := finite_originalGaloisClosure_over_coordinate N L
  haveI : Algebra.IsAlgebraic J F := Algebra.IsAlgebraic.of_finite J F
  haveI : Algebra.IsAlgebraic T F :=
    SourceCurve.isAlgebraic_adjoin_of_transcendental (originalGaloisJ N L) ht
  haveI : Algebra.EssFiniteType L F := essFiniteType_originalGaloisClosure N L
  haveI : Algebra.EssFiniteType T F := Algebra.EssFiniteType.of_comp L T F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end
end Dubon2026.SourceFunctionField
