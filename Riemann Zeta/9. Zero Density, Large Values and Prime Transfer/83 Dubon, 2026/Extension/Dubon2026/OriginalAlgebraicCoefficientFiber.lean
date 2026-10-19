import Dubon2026.OriginalCoefficientAutomaticContinuity
import Dubon2026.OriginalCoefficientFramedEquivalence

/-! Automatic continuity identifies the actual algebraic residue fiber
with the original continuous fiber. This permits the two actual
universal rings to be compared despite their differently presented
maximal-adic topologies. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- Forgetting continuity loses no genuine residue-preserving map
between coefficient rings with their proved maximal-adic topologies. -/
def originalAlgebraicContinuousCoefficientFiberEquiv
    {O R A : Type*} [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
    [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
    (hR : (inferInstance : TopologicalSpace R) = (maximalIdeal R).adicTopology)
    (hA : (inferInstance : TopologicalSpace A) = (maximalIdeal A).adicTopology)
    (eR : ResidueField R ≃ₐ[O] ResidueField O)
    (eA : ResidueField A ≃ₐ[O] ResidueField O) :
    {f : R →ₐ[O] A // (localCoefficientReduction eA).comp f = localCoefficientReduction eR} ≃
      OriginalContinuousCoefficientFiber eR eA where
  toFun f := ⟨f.val, originalCoefficientMap_continuous_of_topology_eq hR hA eR eA f.val f.property,
    f.property⟩
  invFun f := ⟨f.val, f.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end Dubon2026
