import Dubon2026.SourceGammaOneFunctionFieldBaseChange
import Dubon2026.SourceDifferentialExpansionInjectivity
import Dubon2026.SourceCurveFiniteCoordinateCanonical

/-! DUB-17/18 -> original all-weight adic association -> finite Gamma1
character arithmetic realization -> Picard/H1 comparison -> actual Gamma1
curve and differential realization. Apply the existing finite-coordinate
curve and canonical-divisor theorems to the original j coordinate in the
actual integral-ratio field. This supplies the algebraic prerequisites
identified in the inspected Gamma1 differential comparison, without a new
abstract curve, local residue or Riemann--Roch development. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open KaehlerDifferential SourceDifferential SourceCurve IntermediateField
open scoped MatrixGroups
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
  (L : Type*) [Field L] [Algebra ℚ L]

private local instance coefficientCharZero : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℚ L).injective

theorem D_jCoordinateOver_ne_zero :
    D L (functionFieldOver Γ L) (jCoordinateOver Γ L) ≠ 0 := by
  intro h
  have he := congrArg (diffQExp (functionFieldOver Γ L)) h
  rw [diffQExp_D, map_zero] at he
  exact qEuler_ne_zero_of_transcendental (functionFieldOver Γ L)
    (jCoordinateOver Γ L) (transcendental_jCoordinateOver Γ L) he

variable [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
include hT

theorem functionFieldOver_diffQExp_injective :
    Function.Injective (diffQExp (functionFieldOver Γ L)) := by
  letI := finiteDimensional_jCoordinateOver hT L
  exact diffQExp_injective_of_transcendental (functionFieldOver Γ L)
    (jCoordinateOver Γ L) (transcendental_jCoordinateOver Γ L)

theorem functionFieldOver_dCoordGenerates (P : Place L (functionFieldOver Γ L)) :
    P.DCoordGenerates := by
  letI := finiteDimensional_jCoordinateOver hT L
  exact finite_coordinate_place_dCoordGenerates (jCoordinateOver Γ L) P

theorem functionFieldOver_localDifferentials (P : Place L (functionFieldOver Γ L)) :
    Module.Finite P.toValuationSubring Ω[P.toValuationSubring⁄L] := by
  letI := finiteDimensional_jCoordinateOver hT L
  exact finite_coordinate_place_differentials (jCoordinateOver Γ L) P

theorem functionFieldOver_isCurveOver [IsAlgClosed L] :
    IsCurveOver L (functionFieldOver Γ L) := by
  letI := finiteDimensional_jCoordinateOver hT L
  exact isCurveOver_finite_coordinate (jCoordinateOver Γ L)
    (transcendental_jCoordinateOver Γ L) (D_jCoordinateOver_ne_zero Γ L)

theorem functionFieldOver_hasCanonicalDivisor [IsAlgClosed L] :
    HasCanonicalDivisor (K := L) (F := functionFieldOver Γ L) := by
  letI := finiteDimensional_jCoordinateOver hT L
  exact hasCanonicalDivisor_finite_coordinate (jCoordinateOver Γ L)
    (transcendental_jCoordinateOver Γ L) (D_jCoordinateOver_ne_zero Γ L)

end
end Dubon2026.SourceFunctionField.GammaOne
