import Dubon2026.SUnitPowerQuotientEmbedding
import Dubon2026.NumberFieldSUnitPowerCardinality

/-! # The original global S-unit radical quotient and its exact size

The actual subgroup is the product of original S-units and original field
nth powers. The second isomorphism theorem and proved power saturation
identify its radical quotient with the original S-unit power quotient.
This is the finite radical input to the global norm-index route for DUB-17.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- The actual S-unit quotient identifies with the radical quotient inside the original field. -/
def sUnitPowerQuotientEquivRadical {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) (hn : n ≠ 0) :
    S.unit K ⧸ (powMonoidHom (α := S.unit K) n).range ≃*
      (S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range : Subgroup Kˣ) ⧸
        ((powMonoidHom (α := Kˣ) n).range).subgroupOf
          (S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    ext x
    exact sUnit_mem_power_range_iff S n hn x)).trans
      (QuotientGroup.quotientInfEquivProdNormalQuotient (S.unit K)
        (powMonoidHom (α := Kˣ) n).range)

/-- The exact original global radical quotient has the cardinality required by Kummer preparation. -/
theorem numberField_sUnit_radicalQuotient_card
    (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : n ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card ((S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range : Subgroup Kˣ) ⧸
      ((powMonoidHom (α := Kˣ) n).range).subgroupOf
        (S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range)) =
      n ^ (Fintype.card (NumberField.InfinitePlace K) + S.ncard) := by
  rw [← Nat.card_congr (sUnitPowerQuotientEquivRadical S n hn).toEquiv]
  exact numberField_sUnit_powerQuotient_card K S hS n hn ζ hζ

end
end Dubon2026
