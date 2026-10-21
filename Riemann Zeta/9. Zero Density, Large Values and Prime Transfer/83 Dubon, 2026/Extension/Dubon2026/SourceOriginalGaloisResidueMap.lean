import Dubon2026.SourceOriginalGaloisLocalGeometry
import Dubon2026.SourceOriginalGaloisPrincipalDivisors
import Dubon2026.SourceCurveDifferentialSupport
import Dubon2026.SourceCurveGlobalResidueMap

/-! DUB-17/18 -> original global residue identity -> finite Galois averaging.
Only the finite support of the actual auxiliary dj differential is required
to build its global residue functional. Existing different-ideal support and
principal support theorems supply it; no auxiliary canonical-divisor or
Riemann--Roch package is assumed or constructed here.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The native constant-field module action used by the actual residue functional. -/
instance originalGaloisConstantsModule : Module L (originalGaloisClosure N L) :=
  @Algebra.toModule L (originalGaloisClosure N L) _ _ (originalGaloisClosureConstantsAlgebra N L)

theorem finite_originalGaloisClosure_D_j_support :
    {v : Place L (originalGaloisClosure N L) |
      v.ordDifferential (D L (originalGaloisClosure N L) (originalGaloisJ N L)) ≠ 0}.Finite := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_originalGaloisClosure_over_coordinate N L
  haveI : ∀ v : Place L (originalGaloisClosure N L),
      Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] :=
    finite_originalGaloisClosure_place_differentials N L
  haveI : ∀ v : Place L (originalGaloisClosure N L), Algebra.IsSeparable L v.ResidueField :=
    fun v => by
      haveI := originalGaloisClosure_place_residue_isAlgebraic N L v
      infer_instance
  haveI : ∀ v : Place L (originalGaloisClosure N L), v.DCoordGenerates :=
    originalGaloisClosure_place_dCoordGenerates N L
  haveI : Nontrivial Ω[originalGaloisClosure N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_originalGaloisClosure_differentials N L)
  apply finite_differential_support_of_finite_coordinate (originalGaloisJ N L)
    (transcendental_originalGaloisClosure_j N L)
  exact (finite_originalGaloisClosure_divisor_support N L (originalGaloisJ N L)).subset
    fun _ hv => ne_of_lt hv

/-- The actual global residue sum for dj on the literal auxiliary normal closure. -/
def originalGaloisResidueMap [IsAlgClosed L] : originalGaloisClosure N L →ₗ[L] L :=
  globalResidueLinearMap (originalGaloisCanonicalLocalResidueData N L)
    (D L (originalGaloisClosure N L) (originalGaloisJ N L))
    (finite_originalGaloisClosure_divisor_support N L)
    (finite_originalGaloisClosure_D_j_support N L)

theorem originalGaloisResidueMap_apply [IsAlgClosed L] (f : originalGaloisClosure N L) :
    originalGaloisResidueMap N L f =
      ∑ᶠ v : Place L (originalGaloisClosure N L),
        kaehlerResidueTermKFam (originalGaloisCanonicalLocalResidueData N L)
          (D L (originalGaloisClosure N L) (originalGaloisJ N L))
          (diagonalHom L (originalGaloisClosure N L) f) v := rfl

end
end Dubon2026.SourceFunctionField
