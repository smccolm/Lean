import Dubon2026.SourceCurveRegularComparison
import Dubon2026.SourceCurveGlobalConstants
import Dubon2026.SourceCurveLSpaceFinite
import Dubon2026.SourceOriginalPrincipalDivisors
import Dubon2026.SourceOriginalCanonicalDivisors

/-! DUB-17/18 -> matching cusp-form lower dimension bound -> original
regular differential dimension. The actual original field has only base
constants as global regular functions, every divisor space is finite, and
the actual canonical divisor identifies its divisor space with regular
differentials. Thus the original regular differential space is finite.
Its dimension/genus formula and analytic cusp-form realization remain open.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem original_lSpace_zero_eq_range :
    LSpace (0 : Divisor L (modularFunctionFieldOver N L)) =
      LinearMap.range (Algebra.linearMap L (modularFunctionFieldOver N L)) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  exact lSpace_zero_eq_range
    (fun _ ht => finiteDimensional_original_over_transcendental N L ht)

theorem finite_original_lSpace (D : Divisor L (modularFunctionFieldOver N L)) :
    Module.Finite L (LSpace D) := by
  haveI : Module.Finite L (LSpace (0 : Divisor L (modularFunctionFieldOver N L))) := by
    rw [original_lSpace_zero_eq_range N L]
    infer_instance
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Module.Finite L v.ResidueField :=
    finite_original_place_residue N L
  exact finite_lSpace D

/-- The actual j-canonical divisor space and original regular differentials. -/
def originalCanonicalSpaceEquivRegular :
    LSpace (originalCanonicalDivisor N L (D_jOver_ne_zero N L)) ≃ₗ[L]
      regularDifferentials L (modularFunctionFieldOver N L) := by
  haveI : IsCurveOver L (modularFunctionFieldOver N L) := isCurveOver_original N L
  haveI : HasCanonicalDivisor (K := L) (F := modularFunctionFieldOver N L) :=
    hasCanonicalDivisor_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  have hD : canonicalDivisorOf (D_jOver_ne_zero N L) =
      originalCanonicalDivisor N L (D_jOver_ne_zero N L) := by
    ext v
    rw [canonicalDivisorOf_apply, originalCanonicalDivisor_apply]
  rw [← hD]
  exact RegularDifferentialsComparison.lSpaceCanonicalEquivRegular (D_jOver_ne_zero N L)

theorem finite_original_regularDifferentials :
    Module.Finite L (regularDifferentials L (modularFunctionFieldOver N L)) := by
  haveI := finite_original_lSpace N L
    (originalCanonicalDivisor N L (D_jOver_ne_zero N L))
  exact Module.Finite.equiv (originalCanonicalSpaceEquivRegular N L)

theorem finrank_original_regularDifferentials_eq_canonicalSpace :
    Module.finrank L (regularDifferentials L (modularFunctionFieldOver N L)) =
      Module.finrank L (LSpace (originalCanonicalDivisor N L (D_jOver_ne_zero N L))) :=
  (originalCanonicalSpaceEquivRegular N L).finrank_eq.symm

end
end Dubon2026.SourceFunctionField
