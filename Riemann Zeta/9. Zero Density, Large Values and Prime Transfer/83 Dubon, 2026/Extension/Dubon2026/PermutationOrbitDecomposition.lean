import Dubon2026.FiniteProductCohomology
import Dubon2026.TransitivePermutationCohomology

/-! # The actual finite permutation representation decomposed into its orbits

The existing disjoint-orbit equivalence gives an integer-linear and
equivariant decomposition into the original orbit representations. This
connects the actual basis coordinates of DUB-17's S-unit permutation
sublattice to the computed transitive factors, without supplied orbit
decomposition or cohomological assumptions.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]

/-- The actual coordinatewise decomposition of functions into functions on the original orbits. -/
def permutationOrbitLinearEquiv :
    (ι → R) ≃ₗ[R] (∀ ω : MulAction.orbitRel.Quotient G ι, ω.orbit → R) :=
  (LinearEquiv.funCongrLeft R R (MulAction.selfEquivSigmaOrbits' G ι).symm).trans
    (LinearEquiv.piCurry R (fun (ω : MulAction.orbitRel.Quotient G ι) (_ : ω.orbit) => R))

/-- Original orbit decomposition is literal restriction to each orbit. -/
theorem permutationOrbitLinearEquiv_apply (x : ι → R)
    (ω : MulAction.orbitRel.Quotient G ι) (j : ω.orbit) :
    permutationOrbitLinearEquiv R G ι x ω j = x j.val := rfl

/-- The original permutation representation is isomorphic to the actual product of its original orbit representations. -/
def permutationOrbitRepIso :
    permutationCoordinateRep R G ι ≅
      originalPiRep (fun ω : MulAction.orbitRel.Quotient G ι =>
        permutationCoordinateRep R G ω.orbit) := by
  apply Rep.mkIso
  refine Representation.Equiv.mk (permutationOrbitLinearEquiv R G ι) ?_
  intro g
  apply LinearMap.ext
  intro x
  funext ω j
  rfl

/-- The actual representation decomposition restricts to each original orbit. -/
theorem permutationOrbitRepIso_hom_apply (x : ι → R)
    (ω : MulAction.orbitRel.Quotient G ι) (j : ω.orbit) :
    (permutationOrbitRepIso R G ι).hom.hom x ω j = x j.val := rfl

end
end Dubon2026
