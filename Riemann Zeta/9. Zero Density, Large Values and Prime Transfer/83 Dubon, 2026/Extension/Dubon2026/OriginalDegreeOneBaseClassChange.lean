import Dubon2026.OriginalDegreeOneBaseClassRestriction
import Dubon2026.OriginalClassBaseChangeInflationRestriction

/-! # Faithful original class transport to the normalization-field realization

Actual finite class inflation is already injective. A degree-one change
of the fixed field is an isomorphism on H2. Their proved composition is
the literal class base-change map needed to realize DUB-17's Sylow class.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K E L M : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]

/-- The actual full-class base change is injective when the fixed field
is replaced by its degree-one image. No invariant or pairing premise is used. -/
theorem originalFullClassFieldBaseChangeH2_injective_of_base_degree_one
    (hd : Module.finrank K E = 1) :
    Function.Injective (groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (originalFullClassFieldBaseChangeRepHom K E L M) 2) := by
  haveI : IsIso (originalIdeleClassTowerH2Restriction K E M) :=
    originalIdeleClassTowerH2Restriction_isIso_of_degree_one K E M hd
  have hi := (asIso (originalIdeleClassTowerH2Restriction K E M)).toLinearEquiv.injective
  intro x y h
  apply originalIdeleClassH2Inflation_injective K L M
  apply hi
  exact (originalFullClassFieldBaseChangeH2_eq_restriction_inflation K E L M x).symm.trans
    (h.trans (originalFullClassFieldBaseChangeH2_eq_restriction_inflation K E L M y))

end
end Dubon2026
