import Dubon2026.OriginalPrimeCoinvariantSurjectivity
import Dubon2026.OriginalKernelCoinvariantVanishing

/-! # The actual prime-torsion comparison is an isomorphism

Surjectivity is detected on original coinvariants. The target's zero
first homology and coinvariant injectivity kill the literal kernel's
coinvariants; p-group detection then kills that kernel itself. This is
the concrete criterion for the mod-p comparison used in DUB-17's
integral projectivity proof, with no assumed module classification.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- A genuine map of original p-torsion coefficients is an isomorphism when it is bijective on actual coinvariants and the original target has zero first homology. -/
theorem originalPrimeCoefficient_isIso_of_coinvariants
    {G : Type} [Group G] [Finite G] {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (hpA : ∀ x : A, p • x = 0) (hpB : ∀ x : B, p • x = 0)
    (hcoin : Function.Bijective (Representation.Coinvariants.map A.ρ B.ρ f.hom))
    (hfirst : Limits.IsZero (groupHomology B 1)) : IsIso f := by
  have hs := originalPrimeCoefficient_surjective_of_coinvariants f p hG hpB hcoin.2
  have hpK (x : originalCoefficientKernel f) : p • x = 0 := by
    apply Subtype.ext
    exact hpA x.val
  have hK (x : originalCoefficientKernel f) : x = 0 :=
    originalIntegralPrime_zero_of_coinvariants (originalCoefficientKernel f) p hG hpK
      (originalCoefficientKernel_coinvariants_zero f hs hcoin.1 hfirst) x
  have hi : Function.Injective f.hom := by
    intro a b hab
    have hz := hK ⟨a - b, by
      change f.hom (a - b) = 0
      rw [map_sub, hab, sub_self]⟩
    exact sub_eq_zero.mp (congrArg Subtype.val hz)
  haveI : Mono f := (Rep.mono_iff_injective f).mpr hi
  haveI : Epi f := (Rep.epi_iff_surjective f).mpr hs
  exact isIso_of_mono_of_epi f

end
end Dubon2026
