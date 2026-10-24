import Dubon2026.SourceRatFuncExtensionDifferentials
import Dubon2026.SourceCurveLocalFinite
import Dubon2026.SourceCurveIntegralDerivatives
import Dubon2026.SourceRatFuncGaloisCoordinate
import Dubon2026.SourceCurveFiniteCoordinateResidues

/-! At a positive rational-coordinate place, the existing integral chart
gives finite local differentials. The nonzero rational-coordinate
differential then forces the chosen uniformizer differential to be nonzero;
rank one gives its spanning property. This derives the local differential
instances needed by the DUB-17/18 wild estimate without a generic
uniformizer-separability development. -/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential IntermediateField
variable {K M : Type*} [Field K] [Field M]
variable [Algebra K M] [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
variable [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]
variable (v : Place K M) (hv : 0 < v.ord (algebraMap (RatFunc K) M RatFunc.X))

include hv

theorem finite_positive_rational_place_differentials :
    Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K] := by
  haveI := essFiniteType_place_of_mem_X v (v.mem_of_ord_nonneg hv.le)
  exact KaehlerDifferential.finite K v.toValuationSubring

variable [IsAlgClosed K]

theorem positive_rational_place_dCoord_ne_zero : v.dCoord ≠ 0 := by
  haveI := finite_positive_rational_place_differentials v hv
  haveI := (finite_galois_coordinateField K (M := M)).1
  have hres := place_residue_bijective_of_finite_coordinate
    (algebraMap (RatFunc K) M RatFunc.X) v
  haveI : Module.Finite K v.ResidueField :=
    Module.Finite.of_surjective (Algebra.linearMap K v.ResidueField) hres.surjective
  haveI : Algebra.IsSeparable K v.ResidueField := inferInstance
  intro h
  obtain ⟨g, _, hg⟩ := v.exists_integral_D_eq_smul_dCoord (v.mem_of_ord_nonneg hv.le)
  exact D_rationalCoordinate_ne_zero K M (by rw [hg, h, smul_zero])

theorem positive_rational_place_dCoordGenerates : v.DCoordGenerates :=
  ⟨(finrank_eq_one_iff_of_nonzero _ (positive_rational_place_dCoord_ne_zero v hv)).mp
    (finrank_rationalExtension_differentials K M)⟩

end
end Dubon2026.SourceCurve
