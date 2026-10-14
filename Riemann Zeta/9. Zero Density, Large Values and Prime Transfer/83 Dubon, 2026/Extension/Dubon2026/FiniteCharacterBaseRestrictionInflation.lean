import Dubon2026.GaloisCarryNormCorestriction
import Dubon2026.ContinuousFiniteCharacterCarryInflation

/-! # Original finite characters commute with actual change of fixed base

The two continuous characters are compared on the literal field embeddings.
This supplies the original finite-stage consumer of the norm/carry invariant
identity, needed for local reciprocity in DUB-17's cyclotomic calculation.
-/
namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω]
  (L : FiniteGaloisIntermediateField K Ω) (M : FiniteGaloisIntermediateField E Ω)
  [Algebra K M] [IsScalarTower K E M]
  [Algebra L M] [IsScalarTower K L M] [IsScalarTower L M Ω]

omit [IsGalois E Ω] in
/-- Literal original field restriction commutes with both finite-stage restriction and change of fixed base. -/
theorem finiteGaloisRestriction_baseChange (g : Gal(Ω/E)) :
    AlgEquiv.restrictNormalHom L (galoisBaseChangeRestriction K E Ω Ω g) =
      galoisBaseChangeRestriction K E L M (AlgEquiv.restrictNormalHom M g) := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L Ω).injective
  calc
    algebraMap L Ω ((AlgEquiv.restrictNormalHom L
        (galoisBaseChangeRestriction K E Ω Ω g)) x) =
        galoisBaseChangeRestriction K E Ω Ω g (algebraMap L Ω x) :=
      AlgEquiv.restrictNormal_commutes _ L x
    _ = g (algebraMap L Ω x) := galoisBaseChangeRestriction_commutes K E Ω Ω g _
    _ = g (algebraMap M Ω (algebraMap L M x)) := by
      rw [← IsScalarTower.algebraMap_apply L M Ω]
    _ = algebraMap M Ω ((AlgEquiv.restrictNormalHom M g) (algebraMap L M x)) :=
      (AlgEquiv.restrictNormal_commutes g M _).symm
    _ = algebraMap M Ω (algebraMap L M
        (galoisBaseChangeRestriction K E L M (AlgEquiv.restrictNormalHom M g) x)) :=
      congrArg (algebraMap M Ω) (galoisBaseChangeRestriction_commutes K E L M _ x).symm
    _ = algebraMap L Ω
        (galoisBaseChangeRestriction K E L M (AlgEquiv.restrictNormalHom M g) x) :=
      (IsScalarTower.algebraMap_apply L M Ω _).symm

omit [IsGalois E Ω] in
/-- Inflating then restricting an original finite character equals inflating its literal finite-field base restriction. -/
theorem finiteGaloisCharacterInflation_baseRestriction
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) :
    galoisFiniteBaseCharacterRestriction K Ω E (finiteGaloisCharacterInflation L χ) =
      finiteGaloisCharacterInflation M (χ.comp (galoisBaseChangeRestriction K E L M)) := by
  ext g
  exact congrArg χ (finiteGaloisRestriction_baseChange K Ω E L M g)

end
end Dubon2026
