import Dubon2026.OriginalPrimeCoinvariantIsomorphism
import Dubon2026.OriginalCoinvariantSectionComparison
import Dubon2026.OriginalPrimeCoinvariantSection

/-! # The original prime-torsion coefficient is actually coinduced

Prime-field lifting constructs the section of the original coinvariant
map. Its actual trace comparison is bijective on coinvariants; zero
target first homology makes that comparison an isomorphism. This is
the required mod-p classification for the actual fundamental kernel on
DUB-17's integral projectivity route, without a supplied induced model.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- A genuine p-torsion coefficient of a finite p-group with zero first homology is isomorphic to the actual coinduction of its own original coinvariant module. -/
theorem originalPrimeCoefficient_coinduced_iso
    {G : Type} [Group G] [Fintype G] (A : Rep.{0} ℤ G)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (hp : ∀ x : A, p • x = 0) (hfirst : Limits.IsZero (groupHomology A 1)) :
    Nonempty (A ≅ originalCoinducedFunctionRep (originalCoinvariantTrivialRep A)) := by
  obtain ⟨T, hT⟩ := originalPrimeCoinvariant_exists_linear_section A p hp
  have hpC (c : A.ρ.Coinvariants) : p • c = 0 := by
    obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective A.ρ c
    rw [← map_nsmul, hp, map_zero]
  have hpF (x : originalCoinducedFunctionRep (originalCoinvariantTrivialRep A)) : p • x = 0 := by
    apply Subtype.ext
    funext g
    exact hpC (x.val g)
  have hi := originalPrimeCoefficient_isIso_of_coinvariants
    (originalCoinvariantSectionComparison A T) p hG hpF hp
    ⟨originalCoinvariantSectionComparison_coinvariant_injective A T hT,
      originalCoinvariantSectionComparison_coinvariant_surjective A T hT⟩ hfirst
  exact ⟨(@asIso _ _ _ _ (originalCoinvariantSectionComparison A T) hi).symm⟩

end
end Dubon2026
