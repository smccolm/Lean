import Dubon2026.CharacterDualCoefficientSequence

/-! # The actual character dual of the original trivial coefficient line

The pinned evaluation-at-one equivalence identifies the scalar dual with the
original character line. Its literal pairing formula is needed to connect
DUB-17's scalar base cup to the existing integer-linear Kummer cup.
-/

namespace Dubon2026
noncomputable section

variable {k G : Type} [Field k] [Group G] (χ : G →* k)

/-- The actual character dual of the trivial line is the same original
character line, through the pinned evaluation-at-one linear equivalence. -/
def characterDualTrivialLineEquiv :
    characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ ≃ₗ[k]
      coefficientCharacterRep χ :=
  LinearMap.ringLmapEquivSelf k k k

/-- The original scalar dual equivalence is literal evaluation at one. -/
theorem characterDualTrivialLineEquiv_apply
    (ℓ : characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ) :
    characterDualTrivialLineEquiv χ ℓ = ℓ 1 := rfl

/-- The evaluation equivalence preserves the actual character dual action. -/
theorem characterDualTrivialLineEquiv_equivariant (g : G)
    (ℓ : characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ) :
    characterDualTrivialLineEquiv χ
      ((characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ).ρ g ℓ) =
        (coefficientCharacterRep χ).ρ g (characterDualTrivialLineEquiv χ ℓ) := by
  change χ g * ℓ (1 * 1) = χ g * ℓ 1
  rw [one_mul]

/-- The actual scalar evaluation pairing retains precisely multiplication
of the original coefficient and the original evaluation-at-one coordinate. -/
theorem characterDualTrivialLine_pairing (x : k)
    (ℓ : characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ) :
    characterDualEvaluation (coefficientCharacterRep (1 : G →* k)) χ x ℓ =
      x * characterDualTrivialLineEquiv χ ℓ := by
  have he := ℓ.map_smul x (1 : k)
  change ℓ (x * 1) = x * ℓ 1 at he
  simpa only [mul_one] using he

end
end Dubon2026
