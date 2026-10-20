import Dubon2026.FinitePlaceParabolicPrimaryQuotient
import Dubon2026.AuxiliarySubgroupFamilyQuotient

/-! # The original auxiliary family U0/U1

The finite auxiliary factors in BLGG Section 3.6 are literal subgroups of
the product of the original completed integral matrix groups. Quotienting
those levels produces one residue-unit factor per selected place.
Identifying these factors inside the global unitary adelic level remains
a separate source-field and integral-model construction.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
variable {S : Type*} (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)

/-- The original product U0 at the selected auxiliary places. -/
abbrev finitePlaceParabolicFamilyLevelZero :=
  Subgroup.pi Set.univ fun s =>
    parabolicResidueLevelZero (Valued.integer ((v s).adicCompletion K)) (Fin.last n)

/-- The original product U1 in the same ambient integral matrix groups. -/
abbrev finitePlaceParabolicFamilyLevelOne :=
  Subgroup.pi Set.univ fun s =>
    parabolicResidueLevelOneAmbient (Valued.integer ((v s).adicCompletion K)) (Fin.last n)

/-- The original lower auxiliary level is contained in the original upper level. -/
theorem finitePlaceParabolicFamilyLevelOne_le :
    finitePlaceParabolicFamilyLevelOne K v n ≤ finitePlaceParabolicFamilyLevelZero K v n := by
  intro M hM s hs
  exact parabolicResidueLevelOneAmbient_le _ _ (hM s hs)

/-- The quotient of the actual auxiliary product levels. -/
abbrev FinitePlaceParabolicFamilyQuotient :=
  finitePlaceParabolicFamilyLevelZero K v n ⧸
    (finitePlaceParabolicFamilyLevelOne K v n).subgroupOf
      (finitePlaceParabolicFamilyLevelZero K v n)

/-- The literal family quotient is the product of the original local quotients. -/
def finitePlaceParabolicFamilyQuotientEquiv :
    FinitePlaceParabolicFamilyQuotient K v n ≃*
      (∀ s, FinitePlaceParabolicQuotient K (v s) n) :=
  auxiliarySubgroupFamilyQuotientEquiv _ _

/-- The original family quotient multiplication is commutative. -/
instance finitePlaceParabolicFamilyQuotientCommGroup :
    CommGroup (FinitePlaceParabolicFamilyQuotient K v n) :=
  { (inferInstance : Group (FinitePlaceParabolicFamilyQuotient K v n)) with
    mul_comm := fun x y => (finitePlaceParabolicFamilyQuotientEquiv K v n).injective
      (((finitePlaceParabolicFamilyQuotientEquiv K v n).map_mul x y).trans
        ((mul_comm _ _).trans ((finitePlaceParabolicFamilyQuotientEquiv K v n).map_mul y x).symm)) }

/-- Number-field residue finiteness proves finiteness of the actual auxiliary family quotient. -/
instance finitePlaceParabolicFamilyQuotient_finite [Finite S] :
    Finite (FinitePlaceParabolicFamilyQuotient K v n) :=
  Finite.of_equiv (∀ s, FinitePlaceParabolicQuotient K (v s) n)
    (finitePlaceParabolicFamilyQuotientEquiv K v n).symm.toEquiv

/-- The original family quotient has one residue-unit factor per selected place. -/
theorem finitePlaceParabolicFamilyQuotient_card [Fintype S] :
    Nat.card (FinitePlaceParabolicFamilyQuotient K v n) =
      ∏ s, (Nat.card (𝓞 K ⧸ (v s).asIdeal) - 1) := by
  rw [Nat.card_congr (finitePlaceParabolicFamilyQuotientEquiv K v n).toEquiv, Nat.card_pi]
  exact Finset.prod_congr rfl fun s _ => finitePlaceParabolicQuotient_card K (v s) n

/-- Delta is the actual maximal primary quotient of the original auxiliary family. -/
abbrev FinitePlaceParabolicFamilyDelta :=
  FiniteCommutativePrimaryQuotient (FinitePlaceParabolicFamilyQuotient K v n)

/-- The actual auxiliary Delta is a coefficient-primary group. -/
theorem finitePlaceParabolicFamilyDelta_isPGroup (q : ℕ) :
    IsPGroup q (FinitePlaceParabolicFamilyDelta K v n q) :=
  finiteCommutativePrimaryQuotient_isPGroup (FinitePlaceParabolicFamilyQuotient K v n) q

/-- Every coefficient-primary action of the original family quotient factors uniquely through Delta. -/
theorem finitePlaceParabolicFamilyDelta_unique_factor [Finite S] (q : ℕ) [Fact q.Prime]
    {H : Type*} [Group H] (hH : IsPGroup q H)
    (θ : FinitePlaceParabolicFamilyQuotient K v n →* H) :
    ∃! η : FinitePlaceParabolicFamilyDelta K v n q →* H,
      η.comp (QuotientGroup.mk'
        (finiteCommutativePrimaryKernel (FinitePlaceParabolicFamilyQuotient K v n) q)) = θ :=
  finiteCommutativePrimaryQuotient_unique_factor (FinitePlaceParabolicFamilyQuotient K v n) q hH θ

end
end Dubon2026
