import Dubon2026.OriginalIntegralPrimeCoinvariants
import Dubon2026.OriginalCoefficientRangeQuotient

/-! # Actual surjectivity detected by prime-torsion coinvariants

The original comparison map's literal cokernel is killed by p. Its
coinvariants vanish when the original coinvariant map is surjective,
so finite p-group detection kills that cokernel. This removes the
surjectivity input from the mod-p comparison on DUB-17's duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Surjectivity on actual coinvariants implies surjectivity of the original map into a p-torsion coefficient of a finite p-group. -/
theorem originalPrimeCoefficient_surjective_of_coinvariants
    {G : Type} [Group G] [Finite G] {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (hp : ∀ x : B, p • x = 0)
    (hcoin : Function.Surjective (Representation.Coinvariants.map A.ρ B.ρ f.hom)) :
    Function.Surjective f.hom := by
  let Q := originalCoefficientRangeQuotient f
  have hQp (x : Q) : p • x = 0 := by
    obtain ⟨b, rfl⟩ := (LinearMap.range f.hom.toLinearMap).mkQ_surjective x
    exact (map_nsmul (LinearMap.range f.hom.toLinearMap).mkQ p b).symm.trans
      (congrArg (LinearMap.range f.hom.toLinearMap).mkQ (hp b) |>.trans (map_zero _))
  have hQ (x : Q) : x = 0 := originalIntegralPrime_zero_of_coinvariants Q p hG hQp
    (originalCoefficientRangeQuotient_coinvariants_zero f hcoin) x
  intro b
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f.hom.toLinearMap)).mp
    (hQ ((LinearMap.range f.hom.toLinearMap).mkQ b))

end
end Dubon2026
