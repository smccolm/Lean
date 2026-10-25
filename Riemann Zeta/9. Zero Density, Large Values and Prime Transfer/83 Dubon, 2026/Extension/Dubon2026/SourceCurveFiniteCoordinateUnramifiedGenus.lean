import Dubon2026.SourceCurveFiniteCoordinateRegularGenus
import Dubon2026.SourceCurveUnramifiedCanonicalDegree

/-! DUB-17/18 -> cover dissection genus count.
The existing unramified canonical-degree identity and finite-coordinate
dimension comparison give exactly the multiplicity needed for the cover
Euler count. All residue, differential and canonical instances are derived. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField KaehlerDifferential
variable {K F E : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
variable (t : F) [FiniteDimensional K⟮t⟯ F]
  [FiniteDimensional K⟮algebraMap F E t⟯ E]

theorem finite_coordinate_euler_genus_of_unramified
    (ht : Transcendental K t) (hDt : D K F t ≠ 0)
    (htE : Transcendental K (algebraMap F E t))
    (hDtE : D K E (algebraMap F E t) ≠ 0)
    (he : ∀ w : Place K E, w.ramificationIndex (F := F) = 1) :
    2 - 2 * (Module.finrank K (regularDifferentials K E) : ℤ) =
      (Module.finrank F E : ℤ) * (2 - 2 * (Module.finrank K (regularDifferentials K F) : ℤ)) := by
  letI : Nontrivial Ω[F⁄K] := nontrivial_of_ne _ _ hDt
  letI : Nontrivial Ω[E⁄K] := nontrivial_of_ne _ _ hDtE
  letI := hasCanonicalDivisor_finite_coordinate t ht hDt
  letI := hasCanonicalDivisor_finite_coordinate (algebraMap F E t) htE hDtE
  letI : ∀ v : Place K F, v.DCoordGenerates := finite_coordinate_place_dCoordGenerates t
  letI : ∀ w : Place K E, w.DCoordGenerates := finite_coordinate_place_dCoordGenerates (algebraMap F E t)
  letI : ∀ w : Place K E, Module.Finite w.toValuationSubring Ω[w.toValuationSubring⁄K] :=
    finite_coordinate_place_differentials (algebraMap F E t)
  letI : ∀ w : Place K E, Module.Finite K w.ResidueField := finite_coordinate_place_residue (algebraMap F E t)
  letI : ∀ w : Place K E, Algebra.IsSeparable K w.ResidueField := fun _ => inferInstance
  have hmap : KaehlerDifferential.map K K F E (D K F t) ≠ 0 := by
    rw [KaehlerDifferential.map_D]
    exact hDtE
  have hcan := canonical_degree_map_of_unramified (K := K) (F := F) (E := E)
    (place_residue_bijective_of_finite_coordinate t)
    (place_residue_bijective_of_finite_coordinate (algebraMap F E t)) he hDt hmap
  have hbase := finite_coordinate_canonical_degree_eq_regular_dimension t ht hDt hDt
  have htop := finite_coordinate_canonical_degree_eq_regular_dimension (algebraMap F E t) htE hDtE hmap
  rw [hbase, htop] at hcan
  nlinarith

end
end Dubon2026.SourceCurve
