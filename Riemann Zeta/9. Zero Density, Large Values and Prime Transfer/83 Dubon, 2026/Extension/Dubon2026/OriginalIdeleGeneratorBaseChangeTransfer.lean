import Dubon2026.OriginalClassGeneratorTowerTransfer
import Dubon2026.OriginalClassBaseChangeInflationRestriction

/-! # Transfer the constructed idele witness through the actual tower maps

The exact class-projection square and tower comparison turn the proved
scaled base-change vanishing into the required restriction vanishing.
The same source full-order class then yields the target generator. This
is the map-level assembly needed on DUB-17's arbitrary-stage route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K E] [IsGalois K L] [IsGalois K M]

/-- An actual full-idele witness whose source class has full auxiliary order and whose scaled base change has zero class image supplies an original target H2 generator; the tower restriction premise is derived. -/
theorem originalIdeleClass_generator_of_idele_baseChange_zero
    (n' : ℕ) (hn : Module.finrank K E ∣ n') (hn'0 : n' ≠ 0)
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : addOrderOf ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalFullClassRepHom K L) x) = n')
    (hz : (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)
      ((n' / Module.finrank K E) • originalFullIdeleBaseChangeH2 K E L M x) = 0) :
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = Module.finrank K E ∧
      Submodule.span ℤ {y} = ⊤ ∧
      groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (originalIdeleClassTowerInclusion K E M) 2 y =
        (n' / Module.finrank K E) •
          groupCohomology.map (AlgEquiv.restrictNormalHom L)
            (originalIdeleClassTowerInclusion K L M) 2
            ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) := by
  exact originalIdeleClass_tower_generator_from_auxiliary K E L M n' hn hn'0
    ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) hx
    ((originalFullIdeleBaseChange_scaled_class_eq_restriction_inflation
      K E L M (n' / Module.finrank K E) x).symm.trans hz)

end
end Dubon2026
