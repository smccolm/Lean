import Dubon2026.SourceCurveFiniteCoordinateResidues
import Dubon2026.SourceCurveSeparatingPrincipalDivisor
import Dubon2026.SourceRationalSeparatingCoordinates

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal-divisor
degree zero -> auxiliary Galois field. The original finite separating
coordinate remains finite and separating after a finite separable extension.
Native adjoinAlgebraMap and scalar towers avoid reconstructing a new field
equivalence. This supplies actual finite divisors and closed residues upstairs. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem finite_separable_mapped_coordinate
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (t : F) [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    FiniteDimensional K⟮algebraMap F E t⟯ E ∧ Algebra.IsSeparable K⟮algebraMap F E t⟯ E := by
  haveI : FiniteDimensional K⟮t⟯ E := Module.Finite.trans F E
  haveI : Algebra.IsSeparable K⟮t⟯ E := Algebra.IsSeparable.trans K⟮t⟯ F E
  letI : Algebra K⟮t⟯ K⟮algebraMap F E t⟯ :=
    (IntermediateField.RingHom.adjoinAlgebraMap (A := K) (C := E) t).toAlgebra
  letI : IsScalarTower K⟮t⟯ K⟮algebraMap F E t⟯ E := IsScalarTower.of_algebraMap_eq' rfl
  exact ⟨Module.Finite.of_restrictScalars_finite K⟮t⟯ K⟮algebraMap F E t⟯ E,
    Algebra.isSeparable_tower_top_of_isSeparable K⟮t⟯ K⟮algebraMap F E t⟯ E⟩

end
end Dubon2026.SourceCurve
