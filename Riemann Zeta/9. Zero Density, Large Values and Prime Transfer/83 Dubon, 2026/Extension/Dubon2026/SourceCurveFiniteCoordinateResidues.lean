import Dubon2026.SourceCurveCoordinateExchange
import Dubon2026.SourceCurveResidueAlgebraic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal divisors ->
Galois-closure descent. The auxiliary splitting field must have the same
closed constant residues as the actual field. Finite extension of one
transcendental coordinate gives finite extension of every such coordinate,
using the existing exchange argument and native essential finite type. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem finite_over_transcendental_of_finite_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) [FiniteDimensional K⟮t⟯ F] {x : F} (hx : Transcendental K x) :
    FiniteDimensional K⟮x⟯ F := by
  let T := K⟮t⟯
  let X := K⟮x⟯
  haveI : Algebra.IsAlgebraic T F := Algebra.IsAlgebraic.of_finite T F
  haveI : Algebra.IsAlgebraic X F := isAlgebraic_adjoin_of_transcendental t hx
  haveI : Algebra.EssFiniteType K T := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton t))
  haveI : Algebra.EssFiniteType T F := inferInstance
  haveI : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K T F
  haveI : Algebra.EssFiniteType X F := Algebra.EssFiniteType.of_comp K X F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem place_residue_bijective_of_finite_coordinate
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (t : F) [FiniteDimensional K⟮t⟯ F] (v : Place K F) :
    Function.Bijective (algebraMap K v.ResidueField) := by
  haveI : Algebra.IsAlgebraic K v.ResidueField :=
    ⟨v.isAlgebraic_residue_of_finite_coordinates
      (fun _ hx => finite_over_transcendental_of_finite_coordinate t hx)⟩
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end
end Dubon2026.SourceCurve
