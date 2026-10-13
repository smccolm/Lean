import Dubon2026.SUnitExtendedLatticeGaloisEquivariance
import Dubon2026.SUnitLogarithmicRepresentation

/-! # The original integral diagonal extension in the existing representations

The exact Galois-equivariant lattice equivalence becomes an isomorphism
from the product of the original logarithmic lattice and the trivial
integer representation to the original permutation-stable extended
lattice. The existing cohomology functor preserves this actual isomorphism.
This is DUB-17's required original diagonal-factor comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original Galois place-permutation representation restricted to the actual extended lattice. -/
def sUnitExtendedLogRep : Rep ℤ Gal(L/K) := by
  letI := sUnitExtendedLogLatticeAction K L S hS
  exact Rep.ofDistribMulAction ℤ Gal(L/K) (sUnitExtendedLogLattice L S)

/-- The product of the actual original logarithmic-lattice representation and the trivial integer diagonal. -/
def sUnitLogProductRep : Rep ℤ Gal(L/K) :=
  Rep.of ((sUnitLogLatticeRep K L S hS).ρ.prod (Rep.trivial ℤ Gal(L/K) ℤ).ρ)

/-- The exact original diagonal splitting gives an isomorphism of the actual integer Galois representations. -/
def sUnitExtendedProductRepIso : sUnitLogProductRep K L S hS ≅ sUnitExtendedLogRep K L S hS :=
  Rep.mkIso (Representation.Equiv.mk (sUnitExtendedLatticeProductEquiv L S) (by
    intro σ
    apply LinearMap.ext
    intro x
    exact sUnitLatticeProdIntToExtended_galois K L S hS σ x))

/-- The representation isomorphism is the exact original integral inverse coordinate splitting. -/
theorem sUnitExtendedProductRepIso_hom_apply (x : sUnitFullLogLattice L S × ℤ) :
    (sUnitExtendedProductRepIso K L S hS).hom.hom x = sUnitLatticeProdIntToExtended L S x := rfl

/-- The actual original diagonal representation isomorphism induces an isomorphism in original cohomology. -/
def sUnitExtendedProductCohomologyIso (n : ℕ) :
    groupCohomology (sUnitLogProductRep K L S hS) n ≅
      groupCohomology (sUnitExtendedLogRep K L S hS) n :=
  (groupCohomology.functor ℤ Gal(L/K) n).mapIso (sUnitExtendedProductRepIso K L S hS)

end
end Dubon2026
