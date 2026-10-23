import Dubon2026.SourceEllipticOddShortQuotient
import Dubon2026.SourceEllipticOddCharTwoActualDiscriminant
import Dubon2026.SourceEllipticOddCharTwoSupersingular
import Dubon2026.SourceEllipticOddVariableSummingSet
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-! Assemble odd quotient discriminants using the native normal forms.
The pinned characteristic-two ordinary normal form replaces the reference's
custom normalization construction. Actual variable-change equivalences and
finite-set transport connect all characteristic cases to the original model.
This discharges model normalization before field descent and odd quotient
ellipticity in the DUB-17 / DUB-18 cyclic-product and inertia-census chain. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve Dubon2026.SourceEllipticVariableChange
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

theorem odd_discriminant_of_variableChange (C : VariableChange K) (W : WeierstrassCurve K)
    {n : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hchanged : (veluQuotient (C • W)
        (oddOrderSummingSet (C • W) ((variableChangeAddEquiv C W.toAffine).symm Q) n)).Δ *
      (∏ P ∈ oddOrderSummingSet (C • W) ((variableChangeAddEquiv C W.toAffine).symm Q) n,
        veluU (C • W) P.1 P.2) ^ 4 = (C • W).Δ ^ (2 * n + 1)) :
    (veluQuotient W (oddOrderSummingSet W Q n)).Δ *
      (∏ P ∈ oddOrderSummingSet W Q n, veluU W P.1 P.2) ^ 4 = W.Δ ^ (2 * n + 1) := by
  rw [variableChange_oddOrderSummingSet C W hQ] at hchanged
  exact (identity_variableChange_iff C W (oddOrderSummingSet W Q n) n
    (card_oddOrderSummingSet hQ)).mp hchanged

theorem odd_quotient_discriminant_of_isAlgClosed [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ}
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient W (oddOrderSummingSet W Q n)).Δ *
      (∏ P ∈ oddOrderSummingSet W Q n, veluU W P.1 P.2) ^ 4 = W.Δ ^ (2 * n + 1) := by
  by_cases h2 : (2 : K) = 0
  · by_cases ha₁ : W.a₁ = 0
    · exact CharTwo.char_two_a₁_zero W h2 ha₁ Q hQ
    · letI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
      let C := W.toCharTwoJNeZeroNF ha₁
      haveI : (C • W).IsCharTwoJNeZeroNF := W.toCharTwoJNeZeroNF_spec ha₁
      apply odd_discriminant_of_variableChange C W Q hQ
      apply CharTwo.odd_quotient_discriminant_of_ordinary_model h2 (C • W)
        (a₁_of_isCharTwoJNeZeroNF _) (a₃_of_isCharTwoJNeZeroNF _)
        (a₄_of_isCharTwoJNeZeroNF _)
      rwa [AddEquiv.addOrderOf_eq]
  · letI : Invertible (2 : K) := invertibleOfNonzero h2
    let C := W.toCharNeTwoNF
    haveI : (C • W).IsCharNeTwoNF := W.toCharNeTwoNF_spec
    apply odd_discriminant_of_variableChange C W Q hQ
    apply odd_quotient_discriminant_of_short_model h2 (C • W)
      (a₁_of_isCharNeTwoNF _) (a₃_of_isCharNeTwoNF _)
    rwa [AddEquiv.addOrderOf_eq]

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
