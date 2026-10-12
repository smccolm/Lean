import Dubon2026.CharacterDualCoefficientSequence
import Dubon2026.CoinducedCosetReconstruction

/-! # The actual character dual of finite coinduced coefficients

The original coset-value equivalence and the pinned finite-product dual
equivalence identify the actual character dual. The literal finite coset sum
is retained for the cup/corestriction comparison needed by DUB-17's local
finite-module duality argument.
-/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)
  [Fintype (G ⧸ S)] (χ : G →* k)

/-- The actual dual of the original coinduced coefficient, obtained from
original coset coordinates and the pinned finite-product dual equivalence. -/
def coinducedCharacterDualEquiv :
    Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)) ≃ₗ[k]
      characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ := by
  classical
  exact (coinducedCosetValuesEquiv (characterDualCoefficientRep A χ) S).trans
    ((LinearMap.lsum k (fun _ : G ⧸ S => A) k).trans (coinducedCosetValuesEquiv A S).dualMap)

/-- Actual coinduced character duality is precisely the original finite sum
of evaluations at matching untwisted coset values. -/
theorem coinducedCharacterDualEquiv_apply
    (ℓ : Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) :
    coinducedCharacterDualEquiv A S χ ℓ f =
      ∑ q : G ⧸ S, (coinducedCosetValues (characterDualCoefficientRep A χ) S ℓ q)
        (coinducedCosetValues A S f q) := by
  simp only [coinducedCharacterDualEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rfl

/-- The actual coinduced evaluation pairing into the original character line. -/
def coinducedCharacterPairing :
    Rep.coind S.subtype (Rep.res S.subtype A) →ₗ[k]
      Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)) →ₗ[k]
        coefficientCharacterRep χ :=
  (coinducedCharacterDualEquiv A S χ).toLinearMap.flip

/-- The original finite coset pairing has exactly the required character
equivariance; the proof reindexes actual cosets by the original group action. -/
theorem coinducedCharacterPairing_equivariant (g : G)
    (f : Rep.coind S.subtype (Rep.res S.subtype A))
    (ℓ : Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))) :
    coinducedCharacterPairing A S χ
        ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ g f)
        ((Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))).ρ g ℓ) =
      (coefficientCharacterRep χ).ρ g (coinducedCharacterPairing A S χ f ℓ) := by
  change coinducedCharacterDualEquiv A S χ _ _ = χ g * coinducedCharacterDualEquiv A S χ ℓ f
  rw [coinducedCharacterDualEquiv_apply, coinducedCharacterDualEquiv_apply, Finset.mul_sum]
  calc
    _ = ∑ q : G ⧸ S, χ g *
        (coinducedCosetValues (characterDualCoefficientRep A χ) S ℓ (g⁻¹ • q))
          (coinducedCosetValues A S f (g⁻¹ • q)) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [coinducedCosetValues_action, coinducedCosetValues_action]
      exact characterDualEvaluation_equivariant A χ g _ _
    _ = _ := Equiv.sum_comp (MulAction.toPerm g⁻¹)
      (fun q : G ⧸ S => χ g * (coinducedCosetValues (characterDualCoefficientRep A χ) S ℓ q)
        (coinducedCosetValues A S f q))

/-- The explicit actual dual equivalence intertwines the original character
dual action, so it can be used in the existing continuous coefficient maps. -/
theorem coinducedCharacterDualEquiv_equivariant (g : G)
    (ℓ : Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))) :
    coinducedCharacterDualEquiv A S χ
      ((Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))).ρ g ℓ) =
        (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ).ρ g
          (coinducedCharacterDualEquiv A S χ ℓ) := by
  apply LinearMap.ext
  intro f
  have he := coinducedCharacterPairing_equivariant A S χ g
    ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ g⁻¹ f) ℓ
  rw [Representation.self_inv_apply] at he
  exact he

end
end Dubon2026
