import Dubon2026.OriginalClassDivisorOrderTransfer
import Dubon2026.OriginalClassBaseChangeInflationRestriction

/-! # Transfer a prescribed order from the same full-idele witness

This discharges the indicated prime-power order obligation inside DUB-17's
mixed-degree full-order class construction. The original field and cohomology
maps are retained. No general cyclic auxiliary extension is required.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E L M : Type) [Field K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K E] [IsGalois K L] [IsGalois K M]

/-- An actual full-idele witness whose source class has full auxiliary order and whose scaled base change has zero class image supplies an original target H2 class of the prescribed order; the tower restriction premise is derived. -/
theorem originalIdeleClass_order_of_idele_baseChange_zero
    (d n' : ℕ) (hd0 : d ≠ 0) (hn : d ∣ n') (hn'0 : n' ≠ 0)
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : addOrderOf ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalFullClassRepHom K L) x) = n')
    (hz : (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)
      ((n' / d) • originalFullIdeleBaseChangeH2 K E L M x) = 0) :
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf y = d ∧
      groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (originalIdeleClassTowerInclusion K E M) 2 y =
        (n' / d) •
          groupCohomology.map (AlgEquiv.restrictNormalHom L)
            (originalIdeleClassTowerInclusion K L M) 2
            ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) := by
  exact originalIdeleClass_tower_order_from_auxiliary K E L M d n' hd0 hn hn'0
    ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) hx
    ((originalFullIdeleBaseChange_scaled_class_eq_restriction_inflation
      K E L M (n' / d) x).symm.trans hz)

end
end Dubon2026
