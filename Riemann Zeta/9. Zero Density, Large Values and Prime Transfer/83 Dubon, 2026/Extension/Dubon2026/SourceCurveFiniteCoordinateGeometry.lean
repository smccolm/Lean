import Dubon2026.SourceCurveClosedSeparatingPrincipalDivisors
import Dubon2026.SourceCurveFiniteCoordinateResidues
import Dubon2026.SourceCurveLocalFinite
import Dubon2026.SourceCurveDivisors
import Dubon2026.SourceDifferentialTranscendence

/-! DUB-17/18 -> Picard torsion injectivity -> unramified Kummer-cover
genus. The existing finite-coordinate, principal-divisor and local-chart
proofs supply the actual curve and local differential hypotheses for the
cover. Using each place's own uniformizer avoids a new two-chart finiteness
argument. These lemmas are used for the actual Kummer field in the following
consumer; canonical degree and the genus formula are separate obligations. -/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential IntermediateField
variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F]
include t

omit [CharZero K] in
theorem finite_coordinate_place_residue [IsAlgClosed K] (v : Place K F) :
    Module.Finite K v.ResidueField :=
  Module.Finite.of_surjective (Algebra.linearMap K v.ResidueField)
    (place_residue_bijective_of_finite_coordinate t v).2

theorem finite_coordinate_place_dCoordGenerates (v : Place K F) : v.DCoordGenerates := by
  have ht : Transcendental K v.uniformizer :=
    v.transcendental_of_ord_ne_zero (by rw [v.ord_uniformizer]; exact one_ne_zero)
  letI := finite_over_transcendental_of_finite_coordinate t ht
  exact ⟨SourceDifferential.span_D_eq_top_of_transcendental K v.uniformizer ht⟩

theorem finite_coordinate_place_differentials (v : Place K F) :
    Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K] := by
  have ht : Transcendental K v.uniformizer :=
    v.transcendental_of_ord_ne_zero (by rw [v.ord_uniformizer]; exact one_ne_zero)
  letI := finite_over_transcendental_of_finite_coordinate t ht
  haveI := essFiniteType_place_of_finite_coordinate v.uniformizer ht v
    (show v.uniformizer ∈ v.toValuationSubring from
      (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose.2)
  exact KaehlerDifferential.finite K v.toValuationSubring

theorem isCurveOver_finite_coordinate [IsAlgClosed K]
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) : IsCurveOver K F where
  toHasPrincipalDivisors := hasPrincipalDivisors_closed_of_separating_coordinate t ht
  finiteResidue := finite_coordinate_place_residue t
  kaehler_free_rank_one := ⟨inferInstance,
    (finrank_eq_one_iff_of_nonzero _ hDt).mpr
      (SourceDifferential.span_D_eq_top_of_transcendental K t ht)⟩

end
end Dubon2026.SourceCurve
