import Dubon2026.SourceCurveGenusMaximum
import Dubon2026.SourceOriginalRegularFinite

/-! DUB-17/18 -> the original function-field Riemann--Roch theorem ->
global index stabilization. The literal j coordinate constructs the source
pole package using the proved finite coordinate extension and finite pole
support. The actual principal divisors, finite residues and finite divisor
spaces then bound degree minus dimension and produce a maximizing divisor.
The auxiliary integer is not yet identified with the canonical genus;
the index formula and residue duality remain subsequent obligations.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem exists_original_poleDivisorPackage :
    Nonempty (PoleDivisorPackage L (modularFunctionFieldOver N L)) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : FiniteDimensional (IntermediateField.adjoin L {jOver N L})
      (modularFunctionFieldOver N L) := finiteDimensional_original N L
  exact exists_poleDivisorPackage_of_finite_coordinate (jOver N L)
    (transcendental_jOver N L) (finite_original_divisor_support N L (jOver N L))

theorem original_degree_dimension_bounded [IsAlgClosed L] :
    RiemannGenusBounded L (modularFunctionFieldOver N L) := by
  haveI : HasPrincipalDivisors L (modularFunctionFieldOver N L) :=
    hasPrincipalDivisors_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Module.Finite L v.ResidueField :=
    finite_original_place_residue N L
  haveI := finite_original_lSpace N L (0 : Divisor L (modularFunctionFieldOver N L))
  exact riemannGenusBounded_of_poleDivisorPackage (exists_original_poleDivisorPackage N L).some

theorem original_degree_dimension_maximum [IsAlgClosed L] :
    ∃ (γ : ℤ) (D₀ : Divisor L (modularFunctionFieldOver N L)),
      RiemannGenusReachedAt γ D₀ := by
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Module.Finite L v.ResidueField :=
    finite_original_place_residue N L
  haveI := finite_original_lSpace N L (0 : Divisor L (modularFunctionFieldOver N L))
  exact exists_riemannGenusReachedAt_of_bounded (original_degree_dimension_bounded N L)

end
end Dubon2026.SourceFunctionField
