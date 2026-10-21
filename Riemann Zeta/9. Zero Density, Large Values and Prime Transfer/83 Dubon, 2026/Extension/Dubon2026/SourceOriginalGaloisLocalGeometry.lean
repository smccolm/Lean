import Dubon2026.SourceOriginalGaloisDifferentials
import Dubon2026.SourceCurveLocalFinite
import Dubon2026.SourceCurveResidueAlgebraic
import Dubon2026.SourceCurveCanonicalResidueData

/-! DUB-17/18 -> global residue identity -> auxiliary finite Galois geometry.
Existing finite-coordinate local charts give finite local differential
modules in the actual normal closure. Existing residue algebraicity and the
closed constant field give its actual canonical local residues. These are
the concrete local inputs required by the proved power and invariance laws.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem essFiniteType_originalGaloisClosure_place
    (v : Place L (originalGaloisClosure N L)) :
    Algebra.EssFiniteType L v.toValuationSubring := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have ht := v.transcendental_of_ord_ne_zero (by rw [v.ord_uniformizer]; exact one_ne_zero)
  haveI := finite_originalGaloisClosure_over_transcendental N L ht
  apply essFiniteType_place_of_finite_coordinate v.uniformizer ht v
  exact v.mem_of_ord_nonneg (by rw [v.ord_uniformizer]; omega)

theorem finite_originalGaloisClosure_place_differentials
    (v : Place L (originalGaloisClosure N L)) :
    Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] := by
  haveI := essFiniteType_originalGaloisClosure_place N L v
  exact KaehlerDifferential.finite L v.toValuationSubring

theorem originalGaloisClosure_place_residue_isAlgebraic
    (v : Place L (originalGaloisClosure N L)) : Algebra.IsAlgebraic L v.ResidueField :=
  ⟨v.isAlgebraic_residue_of_finite_coordinates
    (fun _ ht => finite_originalGaloisClosure_over_transcendental N L ht)⟩

theorem originalGaloisClosure_place_residue_bijective [IsAlgClosed L]
    (v : Place L (originalGaloisClosure N L)) :
    Function.Bijective (algebraMap L v.ResidueField) := by
  haveI := originalGaloisClosure_place_residue_isAlgebraic N L v
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The actual canonical local residues of the literal normal-closure field. -/
def originalGaloisCanonicalLocalResidueData [IsAlgClosed L]
    (v : Place L (originalGaloisClosure N L)) : v.CanonicalLocalResidueDataK :=
  v.canonicalLocalResidueData (originalGaloisClosure_place_residue_bijective N L v).surjective

end
end Dubon2026.SourceFunctionField
