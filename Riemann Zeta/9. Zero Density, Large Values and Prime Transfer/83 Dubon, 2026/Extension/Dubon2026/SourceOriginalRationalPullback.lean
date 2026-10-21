import Dubon2026.SourceCurveResiduePullback
import Dubon2026.SourceCurveResidueRestrictionConstants
import Dubon2026.SourceCurveRestrictionOrders
import Dubon2026.SourceOriginalLocalResidues
import Dubon2026.SourceOriginalIntegralDerivatives

/-! DUB-17/18 -> original regular differential dimension -> global residue
identity -> finite-extension comparison. For the actual finite extension
L(j) into the original modular function field, restriction of every original
place has rational residue field and the local residue pullback scales by
the actual order of its mapped uniformizer. All local geometric inputs are
derived. SourceOriginalGaloisResidueDescent supplies the global pullback
comparison used for descent from the actual Galois closure.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The existing subalgebra action of constants on the literal j-subfield. -/
local instance originalJCoordinateAlgebra :
    Algebra L (IntermediateField.adjoin L {jOver N L}) :=
  (IntermediateField.adjoin L {jOver N L}).toSubalgebra.algebra

/-- Integrality of the already proved actual finite extension over j. -/
local instance originalJCoordinateIntegral :
    Algebra.IsIntegral (IntermediateField.adjoin L {jOver N L})
      (modularFunctionFieldOver N L) := by
  haveI := finiteDimensional_original N L
  exact Algebra.IsIntegral.of_finite _ _

/-- Restriction of an actual original place to the literal rational j-subfield. -/
def originalJRestrictedPlace (w : Place L (modularFunctionFieldOver N L)) :
    Place L (IntermediateField.adjoin L {jOver N L}) := by
  exact w.restrict (IntermediateField.adjoin L {jOver N L})

theorem original_jRestricted_residue_surjective [IsAlgClosed L]
    (w : Place L (modularFunctionFieldOver N L)) :
    Function.Surjective (algebraMap L (originalJRestrictedPlace N L w).ResidueField) := by
  exact w.residue_algebraMap_surjective_restrict (F := IntermediateField.adjoin L {jOver N L})
    (original_place_residue_algebraMap_bijective N L w).surjective

theorem original_jRestricted_order_scale
    (w : Place L (modularFunctionFieldOver N L)) :
    0 < w.ord ((originalJRestrictedPlace N L w).uniformizer : modularFunctionFieldOver N L) ∧
      ∀ f : IntermediateField.adjoin L {jOver N L},
        w.ord (f : modularFunctionFieldOver N L) =
          (originalJRestrictedPlace N L w).ord f *
            w.ord ((originalJRestrictedPlace N L w).uniformizer : modularFunctionFieldOver N L) := by
  constructor
  · exact w.ord_restricted_uniformizer_pos (F := IntermediateField.adjoin L {jOver N L})
  · intro f
    exact w.ord_algebraMap_restrict f

theorem original_jRestricted_residue_pullback [IsAlgClosed L]
    (w : Place L (modularFunctionFieldOver N L))
    (g : IntermediateField.adjoin L {jOver N L}) :
    w.localResidueScalar ((g : modularFunctionFieldOver N L) *
      w.differentialCoeff (D L (modularFunctionFieldOver N L)
        ((originalJRestrictedPlace N L w).uniformizer : modularFunctionFieldOver N L))) =
      (w.ord ((originalJRestrictedPlace N L w).uniformizer : modularFunctionFieldOver N L) : L) *
        (originalJRestrictedPlace N L w).localResidueScalar g := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_original_place_differentials N L w
  haveI := original_place_residue_isAlgebraic N L w
  haveI := original_place_dCoordGenerates N L w
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  exact w.localResidueScalar_restrict_pullback
    (original_jRestricted_residue_surjective N L w)
    (original_place_residue_algebraMap_bijective N L w).surjective g

end
end Dubon2026.SourceFunctionField
