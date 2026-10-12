import Dubon2026.CoinducedInvariantEquiv
import Dubon2026.CoinducedCharacterDuality

/-! # The original H2/H0 Shapiro pairing on actual cochains

The literal induced dual pairing of an original degree-two Shapiro cochain
and a degree-zero Shapiro value equals the original scalar coset trace.
This is the induced endpoint compatibility needed for DUB-17 local duality.
-/

namespace Dubon2026
noncomputable section
open scoped BigOperators

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G)
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k)

/-- The original induced dual H2/H0 evaluation is exactly the original
scalar coset trace before passing to any cohomology quotient. -/
theorem coinducedShapiroTwoZero_pairing (c : S × S → characterDualCoefficientRep A χ)
    (w : A) (g h : G) :
    coinducedCharacterPairing A S χ (coinducedShapiroZero A S w)
      (coinducedShapiroTwo (characterDualCoefficientRep A χ) S c (g, h)) =
      cosetTraceTwo (coefficientCharacterRep χ) S
        (fun z => characterDualEvaluation A χ w (c z)) (g, h) := by
  change coinducedCharacterDualEquiv A S χ _ _ = _
  rw [coinducedCharacterDualEquiv_apply, coinducedShapiroZero_values, coinducedShapiroTwo_values]
  calc
    _ = ∑ q : G ⧸ S,
        (cosetTraceTwoTerm (characterDualCoefficientRep A χ) S c g h q)
          (A.ρ (g • h • q).out w) := by
      simpa only [MulAction.toPerm_apply, mul_inv_rev, mul_smul, inv_smul_smul] using
        (Equiv.sum_comp (MulAction.toPerm (g * h))
          (fun q : G ⧸ S =>
            (cosetTraceTwoTerm (characterDualCoefficientRep A χ) S c g h ((g * h)⁻¹ • q))
              (A.ρ q.out w))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      exact characterDualEvaluation_equivariant A χ (g • h • q).out w
        (c (cosetTransition S g (h • q), cosetTransition S h q))

end
end Dubon2026
