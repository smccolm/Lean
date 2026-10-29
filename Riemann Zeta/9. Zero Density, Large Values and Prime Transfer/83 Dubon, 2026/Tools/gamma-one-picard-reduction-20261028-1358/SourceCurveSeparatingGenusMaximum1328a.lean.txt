import Dubon2026.SourceCurveFiniteCoordinateGenusMaximum
import Dubon2026.SourceCurveLSpaceFinite

/-! DUB-17/18 -> original Gamma1 Picard specialization -> integral-chart
lifting. The original field and its positive-characteristic residue need
the same finite pole-space and genus-maximum argument. This is the native
finite-coordinate argument with separability explicit, so it applies to the
proved separating residue j. No genus equality or chart lifting is assumed. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F]

theorem finite_lSpace_of_separating_coordinate (ht : Transcendental K t)
    (D : Divisor K F) : Module.Finite K (LSpace D) := by
  haveI := hasPrincipalDivisors_closed_of_separating_coordinate t ht
  haveI : ∀ v : Place K F, Module.Finite K v.ResidueField := finite_coordinate_place_residue t
  obtain ⟨P⟩ := nonempty_place_of_separating_coordinate t ht
  haveI := finite_lSpace_zero_of_place P
  exact finite_lSpace D

theorem separating_coordinate_degree_dimension_maximum (ht : Transcendental K t) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  haveI := hasPrincipalDivisors_closed_of_separating_coordinate t ht
  haveI : ∀ v : Place K F, Module.Finite K v.ResidueField := finite_coordinate_place_residue t
  haveI := finite_lSpace_of_separating_coordinate t ht 0
  obtain ⟨pole⟩ := exists_poleDivisorPackage_of_separating_coordinate t ht
    (finite_function_support_of_separating_coordinate t ht t)
  exact exists_riemannGenusReachedAt_of_bounded (riemannGenusBounded_of_poleDivisorPackage pole)

theorem separating_coordinate_index_zero_eq_maximum (ht : Transcendental K t)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (indexOfSpecialty (0 : Divisor K F) : ℤ) = γ := by
  haveI := hasPrincipalDivisors_closed_of_separating_coordinate t ht
  haveI : ∀ v : Place K F, Module.Finite K v.ResidueField := finite_coordinate_place_residue t
  haveI := finite_lSpace_of_separating_coordinate t ht 0
  obtain ⟨P⟩ := nonempty_place_of_separating_coordinate t ht
  have he := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [ell, finrank_lSpace_zero_of_principalDivisors P, Nat.cast_one, map_zero] at he
  linarith

end
end Dubon2026.SourceCurve
