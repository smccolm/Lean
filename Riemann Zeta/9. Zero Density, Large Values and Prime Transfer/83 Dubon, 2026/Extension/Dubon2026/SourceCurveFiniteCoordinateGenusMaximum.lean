import Dubon2026.SourceCurveFiniteCoordinateGeometry
import Dubon2026.SourceCurvePrincipalGlobalConstants
import Dubon2026.SourceCurveSeparatingPolePackage
import Dubon2026.SourceCurveGlobalIndex

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer-cover genus ->
canonical degree. The existing pole package and global index theorem
supply a degree-dimension maximum and Weil rank one for the finite
coordinate of the cover. No genus boundedness or finite-space hypothesis
is retained by these consumers. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {K F : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F]

theorem finite_coordinate_degree_dimension_maximum (ht : Transcendental K t) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  letI := hasPrincipalDivisors_closed_of_separating_coordinate t ht
  letI : ∀ v : Place K F, Module.Finite K v.ResidueField := finite_coordinate_place_residue t
  obtain ⟨P⟩ := nonempty_place_of_separating_coordinate t ht
  letI := finite_lSpace_zero_of_place P
  obtain ⟨pole⟩ := exists_poleDivisorPackage_of_separating_coordinate t ht
    (finite_function_support_of_separating_coordinate t ht t)
  exact exists_riemannGenusReachedAt_of_bounded (riemannGenusBounded_of_poleDivisorPackage pole)

theorem finite_coordinate_weil_differentials_rank_one (ht : Transcendental K t) :
    letI := hasPrincipalDivisors_closed_of_separating_coordinate t ht
    WeilDifferentialRankOne (K := K) (F := F) := by
  letI := hasPrincipalDivisors_closed_of_separating_coordinate t ht
  letI : ∀ v : Place K F, Module.Finite K v.ResidueField := finite_coordinate_place_residue t
  letI := nonempty_place_of_separating_coordinate t ht
  letI := finite_lSpace_zero_of_place (Classical.choice ‹Nonempty (Place K F)›)
  obtain ⟨γ, D₀, h⟩ := finite_coordinate_degree_dimension_maximum t ht
  intro φ hφ hφ0 μ hμ
  exact weilDifferentialRankOne_of_genusReached h hφ hφ0 hμ

end
end Dubon2026.SourceCurve
