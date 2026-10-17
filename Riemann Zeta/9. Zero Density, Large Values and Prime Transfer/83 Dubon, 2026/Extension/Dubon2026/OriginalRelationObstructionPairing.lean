import Dubon2026.OriginalRelationExtensionObstruction
import Dubon2026.RationalCyclicInvariant
import Dubon2026.CoinducedCohomologyTrace

/-! # The actual relation obstruction as a rational-circle pairing

Compose the original connecting obstruction with an actual class invariant.
Its two additive variables are the finite relation morphism and H1 class.
This is the finite pairing needed to compare DUB-17's relation criterion
with the scalar-valued duality argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {G : Type} [Group G] (B C : Rep ℤ G)

/-- The original H1 inherits the coefficient's actual annihilator. -/
theorem originalH1_nsmul_zero (p : ℕ) (hB : ∀ b : B, p • b = 0)
    (y : groupCohomology B 1) : p • y = 0 := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H1π B)).mp inferInstance y
  have hz : p • z = 0 := by
    apply Subtype.ext
    funext g
    exact hB (z g)
  rw [← map_nsmul, hz, map_zero]

/-- The actual obstruction followed by the original invariant, additive
in both its relation morphism and original cohomology class. -/
def originalRelationInvariantPairing
    (inv : groupCohomology C 2 →+ AddCircle (1 : ℚ)) :
    (originalRelationModule B ⟶ C) →+ (groupCohomology B 1 →+ AddCircle (1 : ℚ)) where
  toFun φ := inv.comp (originalRelationExtensionObstruction B C φ).hom.toAddMonoidHom
  map_zero' := by
    unfold originalRelationExtensionObstruction
    erw [CategoryTheory.Functor.map_zero, Limits.comp_zero]
    ext y
    simp
  map_add' φ ψ := by
    unfold originalRelationExtensionObstruction
    erw [CategoryTheory.Functor.map_add, Preadditive.comp_add]
    ext y
    simp

/-- An injective actual invariant preserves detection of the original obstruction. -/
theorem originalRelationInvariantPairing_eq_zero_iff
    (inv : groupCohomology C 2 →+ AddCircle (1 : ℚ)) (hi : Function.Injective inv)
    (φ : originalRelationModule B ⟶ C) (y : groupCohomology B 1) :
    originalRelationInvariantPairing B C inv φ y = 0 ↔
      (originalRelationExtensionObstruction B C φ).hom y = 0 := by
  change inv _ = 0 ↔ _
  exact hi.eq_iff' (map_zero inv)

end
end Dubon2026
