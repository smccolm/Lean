import Dubon2026.FiniteCoinducedCoefficientAction

/-! # Reconstruction of the original coinduced coefficient from coset values

The inverse retains the existing coinduced object, rather than replacing it by
a product. It lets the already proved termwise coset identities construct the
continuous Shapiro comparison required by DUB-17's local duality route.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- Reconstruct the original equivariant function from its actual coset values. -/
def coinducedCosetReconstruct :
    (G ⧸ S → A) →ₗ[R] Rep.coind S.subtype (Rep.res S.subtype A) where
  toFun F := ⟨fun g => A.ρ g (F (QuotientGroup.mk g⁻¹)), by
    intro s g
    have hq : QuotientGroup.mk ((s : G) * g)⁻¹ = (QuotientGroup.mk g⁻¹ : G ⧸ S) := by
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      simpa only [inv_inv, mul_inv_cancel_right] using s.property
    change A.ρ ((s : G) * g) (F (QuotientGroup.mk ((s : G) * g)⁻¹)) =
      A.ρ (s : G) (A.ρ g (F (QuotientGroup.mk g⁻¹)))
    rw [hq, map_mul]
    rfl⟩
  map_add' F H := by
    apply Subtype.ext
    funext g
    exact (A.ρ g).map_add _ _
  map_smul' r F := by
    apply Subtype.ext
    funext g
    exact (A.ρ g).map_smul r _

/-- Reconstruction recovers every original coset value exactly. -/
theorem coinducedCosetValues_reconstruct (F : G ⧸ S → A) :
    coinducedCosetValues A S (coinducedCosetReconstruct A S F) = F := by
  funext q
  induction q using QuotientGroup.induction_on with
  | H g =>
    change A.ρ g (A.ρ g⁻¹ (F (QuotientGroup.mk g⁻¹⁻¹))) = F (QuotientGroup.mk g)
    rw [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- Original coinduced coefficients are recovered from their own actual values. -/
theorem coinducedCosetReconstruct_values
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) :
    coinducedCosetReconstruct A S (coinducedCosetValues A S f) = f := by
  apply coinducedCosetValues_injective A S
  exact coinducedCosetValues_reconstruct A S _

/-- The exact original coinduced coefficient space has its explicit coset
coordinate equivalence, with both inverse identities proved. -/
def coinducedCosetValuesEquiv :
    Rep.coind S.subtype (Rep.res S.subtype A) ≃ₗ[R] (G ⧸ S → A) :=
  { coinducedCosetValues A S with
    invFun := coinducedCosetReconstruct A S
    left_inv := coinducedCosetReconstruct_values A S
    right_inv := coinducedCosetValues_reconstruct A S }

end
end Dubon2026
