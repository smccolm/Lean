import Dubon2026.SourceModularCoefficientFiniteCoordinates
import Dubon2026.SourceCurveResidueAlgebraic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> original Frobenius/inertia -> reduction of the original
curve -> residue-curve geometry. The existing finite-coordinate residue
argument applies verbatim in positive characteristic. Over closed constants
it constructs residue finiteness, without assuming the curve interface. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem coeff_place_residue_isAlgebraic
    (N : ℕ) [NeZero N] (K : Type*) [Field K]
    (v : Place K (modularFunctionFieldCoeff N K)) : Algebra.IsAlgebraic K v.ResidueField :=
  ⟨v.isAlgebraic_residue_of_finite_coordinates
    (fun _ ht => finiteDimensional_coeff_over_transcendental N K ht)⟩

theorem coeff_place_residue_algebraMap_bijective
    (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
    (v : Place K (modularFunctionFieldCoeff N K)) :
    Function.Bijective (algebraMap K v.ResidueField) := by
  haveI : Algebra.IsAlgebraic K v.ResidueField := coeff_place_residue_isAlgebraic N K v
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem finite_coeff_place_residue
    (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
    (v : Place K (modularFunctionFieldCoeff N K)) : Module.Finite K v.ResidueField :=
  Module.Finite.of_surjective (Algebra.linearMap K v.ResidueField)
    (coeff_place_residue_algebraMap_bijective N K v).surjective

end
end Dubon2026.SourceFunctionField
