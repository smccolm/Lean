import Dubon2026.SourceCurveFiniteCoordinateCanonicalDegree
import Dubon2026.SourceCurveRegularComparison

/-! DUB-17/18 -> lifted dissection Euler count -> actual differential genus.
Reuse finite-coordinate residue duality and canonical-space comparison to
identify the analytic regular-differential dimension with the source H1 genus.
This supplies the numerical genus in the actual cover reciprocity matrix. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField KaehlerDifferential
variable {K F : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F]

theorem finite_coordinate_finrank_regular_eq_genusFF
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) :
    Module.finrank K (regularDifferentials K F) = genusFF K F := by
  letI := isCurveOver_finite_coordinate t ht hDt
  letI := hasCanonicalDivisor_finite_coordinate t ht hDt
  letI : Nontrivial Ω[F⁄K] := nontrivial_of_ne _ _ hDt
  letI : ∀ v : Place K F, v.DCoordGenerates := finite_coordinate_place_dCoordGenerates t
  rw [genusFF_eq_zero_index, finite_coordinate_index_eq_canonical_complement t ht hDt hDt,
    sub_zero]
  exact (RegularDifferentialsComparison.lSpaceCanonicalEquivRegular hDt).finrank_eq.symm

theorem finite_coordinate_canonical_degree_eq_regular_dimension
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) :
    letI := hasCanonicalDivisor_finite_coordinate t ht hDt
    ∀ {η : Ω[F⁄K]} (hη : η ≠ 0), Divisor.degree (canonicalDivisorOf hη) =
      2 * (Module.finrank K (regularDifferentials K F) : ℤ) - 2 := by
  letI := hasCanonicalDivisor_finite_coordinate t ht hDt
  intro η hη
  rw [finite_coordinate_canonical_degree_eq_genusFF t ht hDt hη,
    finite_coordinate_finrank_regular_eq_genusFF t ht hDt]

end
end Dubon2026.SourceCurve
