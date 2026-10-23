import Dubon2026.SourceModularCoefficientGlobalSpaces
import Dubon2026.SourceCurveSeparatingPolePackage
import Dubon2026.SourceModularCoefficientDivisorSupport
import Dubon2026.SourceCurveGlobalIndex

/-! DUB-17/18 -> good reduction -> actual residue genus comparison.
Construct the degree-minus-dimension maximum for the actual coefficient
field in every characteristic. Its parameter is proved equal to the
dimension of the existing actual adelic quotient at zero. No genus bound,
finite-space or abstract curve package is assumed by the consumers. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

theorem exists_coeff_poleDivisorPackage :
    Nonempty (PoleDivisorPackage K (modularFunctionFieldCoeff N K)) := by
  haveI := finiteDimensional_coeff_field N K
  haveI := isSeparable_coeff_field N K
  exact exists_poleDivisorPackage_of_separating_coordinate (jCoeff N K)
    (transcendental_jCoeff N K) (finite_coeff_divisor_support N K (jCoeff N K))

theorem coeff_degree_dimension_bounded : RiemannGenusBounded K (modularFunctionFieldCoeff N K) := by
  haveI := hasPrincipalDivisors_coeff_field N K
  haveI := finite_coeff_place_residue N K
  haveI := finite_coeff_lSpace N K 0
  exact riemannGenusBounded_of_poleDivisorPackage (exists_coeff_poleDivisorPackage N K).some

theorem coeff_degree_dimension_maximum :
    ∃ (γ : ℤ) (D₀ : Divisor K (modularFunctionFieldCoeff N K)),
      RiemannGenusReachedAt γ D₀ := by
  haveI := finite_coeff_place_residue N K
  haveI := finite_coeff_lSpace N K 0
  exact exists_riemannGenusReachedAt_of_bounded (coeff_degree_dimension_bounded N K)

theorem coeff_index_zero_eq_maximum {γ : ℤ}
    {D₀ : Divisor K (modularFunctionFieldCoeff N K)} (h : RiemannGenusReachedAt γ D₀) :
    (indexOfSpecialty (0 : Divisor K (modularFunctionFieldCoeff N K)) : ℤ) = γ := by
  haveI := hasPrincipalDivisors_coeff_field N K
  haveI := finite_coeff_place_residue N K
  haveI := finite_coeff_lSpace N K 0
  have he := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [ell, finrank_coeff_lSpace_zero N K, Nat.cast_one, map_zero] at he
  linarith

end
end Dubon2026.SourceFunctionField
