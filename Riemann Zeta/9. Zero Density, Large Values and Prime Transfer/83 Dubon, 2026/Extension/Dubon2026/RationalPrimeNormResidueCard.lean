import Dubon2026.RationalPrimeOriginalResidueCard
import Dubon2026.RationalPrimeUnramifiedDimension

/-! The original compatible norm retains the previously proved residue
cardinality p. Reuse of that exact original-field result supplies the exponent
in the tame Frobenius relation required by DUB-17's auxiliary local condition. -/

namespace Dubon2026

open scoped ValuativeRel

attribute [local instance] rationalPrimeLocalField_charZero rationalPrimeOriginalNorm
  rationalPrimeOriginalNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

theorem rationalPrimeOriginalNorm_integer_eq (p : ℕ) (hp : p.Prime) :
    (NormedField.valuation (K := rationalPrimeLocalField p hp)).integer =
      (ValuativeRel.valuation (rationalPrimeLocalField p hp)).integer := by
  ext x
  change ‖x‖₊ ≤ 1 ↔ ValuativeRel.valuation (rationalPrimeLocalField p hp) x ≤ 1
  have h := localFieldOriginalNorm_le_iff (rationalPrimeLocalField p hp) x 1
  simpa only [norm_one, map_one, ← NNReal.coe_le_coe, NNReal.coe_one] using h

theorem rationalPrimeOriginalNorm_residue_card (p : ℕ) (hp : p.Prime) :
    Nat.card (IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalField p hp))) = p := by
  let e : algebraicLocalIntegerRing (rationalPrimeLocalField p hp) ≃+*
      𝒪[rationalPrimeLocalField p hp] :=
    RingEquiv.subringCongr (rationalPrimeOriginalNorm_integer_eq p hp)
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).trans
    (rationalPrimeLocalField_residue_card p hp)

end Dubon2026
