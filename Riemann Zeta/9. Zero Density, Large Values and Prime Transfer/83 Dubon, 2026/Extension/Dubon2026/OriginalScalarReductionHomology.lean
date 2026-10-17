import Dubon2026.OriginalScalarReductionSequence

/-! # First homology of the actual scalar reduction

For an original torsion-free coefficient with injective coinvariant
norm and zero first homology, multiplication by a nonzero scalar stays
injective on coinvariants. The genuine homology sequence therefore
kills first homology of its literal reduction. This is the mod-p input
for the fundamental kernel's projectivity on DUB-17's duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- The literal reduction of the original torsion-free coefficient has zero first homology when the original norm on coinvariants is injective and its first homology vanishes. -/
theorem originalScalarReduction_first_homology_zero
    {k G : Type} [CommRing k] [IsDomain k] [Group G] [Fintype G]
    (A : Rep.{0} k G) [Module.IsTorsionFree k A] (m : k) (hm : m ≠ 0)
    (hnorm : OriginalNormCoinvariantInjective A)
    (hfirst : Limits.IsZero (groupHomology A 1)) :
    Limits.IsZero (groupHomology (originalScalarReduction A m) 1) := by
  have hX := originalScalarReduction_shortExact A m hm
  exact originalQuotient_first_homology_zero_of_coinvariant_inclusion hX hfirst
    (originalCoinvariantMap_injective_of_norm (originalScalarMultiplication A m)
      ((Rep.mono_iff_injective _).mp hX.mono_f) hnorm)

end
end Dubon2026
