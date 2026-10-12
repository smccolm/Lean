import Dubon2026.CoinducedCharacterDuality
import Dubon2026.CoinducedShapiroDifferentials

/-! # The actual termwise Shapiro cup/corestriction identity

The same subgroup transitions occur in both original Shapiro factors. Their
character-valued evaluation is exactly the original two-cochain trace term.
This is the coefficient and cochain compatibility needed to transfer local
Kummer duality through the proved continuous Shapiro maps for DUB-17.
-/

namespace Dubon2026
noncomputable section

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)
  (χ : G →* k)

/-- Matching original one-cochain trace terms pair to the exact original
two-cochain trace term, with its character action and subgroup transitions. -/
theorem coinducedShapiroCup_traceTerm (f : S → A) (u : S → characterDualCoefficientRep A χ)
    (g h : G) (q : G ⧸ S) :
    characterDualEvaluation A χ (cosetTraceOneTerm A S f g (h • q))
      ((characterDualCoefficientRep A χ).ρ g
        (cosetTraceOneTerm (characterDualCoefficientRep A χ) S u h q)) =
      cosetTraceTwoTerm (coefficientCharacterRep χ) S
        (fun z : S × S => characterDualEvaluation A χ (f z.1)
          ((characterDualCoefficientRep A χ).ρ (z.1 : G) (u z.2))) g h q := by
  dsimp only [cosetTraceOneTerm, cosetTraceTwoTerm]
  have hf : g * (h • q).out =
      (g • h • q).out * (cosetTransition S g (h • q) : G) :=
    (cosetTransition_factor S g (h • q)).symm
  rw [← Module.End.mul_apply, ← map_mul, hf, map_mul, Module.End.mul_apply]
  exact characterDualEvaluation_equivariant A χ (g • h • q).out _ _

/-- Original coset values of both Shapiro factors at a jointly translated
coset are precisely the two matching terms of the cup trace. -/
theorem coinducedShapiroCup_values (f : S → A) (u : S → characterDualCoefficientRep A χ)
    (g h : G) (q : G ⧸ S) :
    (coinducedCosetValues (characterDualCoefficientRep A χ) S
      ((Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))).ρ g
        (coinducedShapiroOne (characterDualCoefficientRep A χ) S u h)) ((g * h) • q))
      (coinducedCosetValues A S (coinducedShapiroOne A S f g) ((g * h) • q)) =
    cosetTraceTwoTerm (coefficientCharacterRep χ) S
      (fun z : S × S => characterDualEvaluation A χ (f z.1)
        ((characterDualCoefficientRep A χ).ρ (z.1 : G) (u z.2))) g h q := by
  rw [coinducedCosetValues_action, coinducedShapiroOne_values, coinducedShapiroOne_values]
  simp only [mul_smul, inv_smul_smul]
  exact coinducedShapiroCup_traceTerm A S χ f u g h q

end
end Dubon2026
