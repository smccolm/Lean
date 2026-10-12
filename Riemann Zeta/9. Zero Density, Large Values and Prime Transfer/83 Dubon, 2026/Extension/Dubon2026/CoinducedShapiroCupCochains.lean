import Dubon2026.CoinducedShapiroCupTerms
import Dubon2026.EquivariantCocycleCup

/-! # The exact original Shapiro cup and corestriction cochain

Summing the proved matching terms over genuine cosets gives equality of the
original two-cochains. This is the comparison that DUB-17's local duality
argument needs, before passing through the existing continuous H2 quotient.
-/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)
  [Fintype (G ⧸ S)] (χ : G →* k)

/-- The cup of actual Shapiro one-cochains, with the actual coinduced dual
pairing, equals the original finite trace of the subgroup cup cochain. -/
theorem coinducedShapiroCup_cochain (f : S → A) (u : S → characterDualCoefficientRep A χ) :
    (fun z : G × G => coinducedCharacterPairing A S χ
      (coinducedShapiroOne A S f z.1)
      ((Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))).ρ z.1
        (coinducedShapiroOne (characterDualCoefficientRep A χ) S u z.2))) =
      cosetTraceTwo (coefficientCharacterRep χ) S
        (fun z : S × S => characterDualEvaluation A χ (f z.1)
          ((characterDualCoefficientRep A χ).ρ (z.1 : G) (u z.2))) := by
  funext z
  rcases z with ⟨g, h⟩
  change coinducedCharacterDualEquiv A S χ _ _ = _
  rw [coinducedCharacterDualEquiv_apply]
  have he := Equiv.sum_comp (MulAction.toPerm (g * h))
    (fun q : G ⧸ S =>
      (coinducedCosetValues (characterDualCoefficientRep A χ) S
        ((Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))).ρ g
          (coinducedShapiroOne (characterDualCoefficientRep A χ) S u h)) q)
        (coinducedCosetValues A S (coinducedShapiroOne A S f g) q))
  rw [← he]
  exact Finset.sum_congr rfl (fun q _ => coinducedShapiroCup_values A S χ f u g h q)

end
end Dubon2026
