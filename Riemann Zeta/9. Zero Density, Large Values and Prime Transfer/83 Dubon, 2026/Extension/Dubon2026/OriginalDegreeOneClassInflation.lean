import Dubon2026.OriginalIdeleClassH2InflationRestriction
import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology

/-! # Return a class through its actual degree-one field realization

The original finite H2 bound kills the relative H2 for a degree-one upper
extension. The existing inflation-restriction theorem therefore descends
every class, retaining its order by faithful inflation. This supplies the
field-realization edge of DUB-17's mixed-degree full-order construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E L : Type) [Field K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K E] [IsGalois K L]

/-- Actual class H2 inflation is surjective across a degree-one upper
field realization, by vanishing of its original relative class H2. -/
theorem originalIdeleClassH2Inflation_surjective_of_degree_one
    (hdegree : Module.finrank E L = 1) :
    Function.Surjective (groupCohomology.map (AlgEquiv.restrictNormalHom E)
      (originalIdeleClassTowerInclusion K E L) 2) := by
  letI : FiniteDimensional E L := FiniteDimensional.right K E L
  letI : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  have hc := (originalIdeleClass_finiteGalois_second_card_dvd E L).2
  rw [hdegree, Nat.dvd_one] at hc
  haveI : Subsingleton (groupCohomology (originalIdeleClassRep E L) 2) :=
    (Nat.card_eq_one_iff_unique.mp hc).1
  intro x
  exact (originalIdeleClassH2_inflation_exists_iff_restriction_zero K E L x).mpr
    (Subsingleton.elim _ _)

/-- A full-order original class on the actual degree-one realization
descends to a full-order class on the original field. -/
theorem originalIdeleClass_full_order_descends_degree_one
    (hdegree : Module.finrank E L = 1)
    (x : groupCohomology (originalIdeleClassRep K L) 2)
    (hx : addOrderOf x = Module.finrank K L) :
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf y = Module.finrank K E := by
  letI : FiniteDimensional K E := FiniteDimensional.left K E L
  letI : FiniteDimensional E L := FiniteDimensional.right K E L
  obtain ⟨y, hy⟩ := originalIdeleClassH2Inflation_surjective_of_degree_one K E L hdegree x
  let f := (groupCohomology.map (AlgEquiv.restrictNormalHom E)
    (originalIdeleClassTowerInclusion K E L) 2).hom.toAddMonoidHom
  have ho := addOrderOf_injective f (originalIdeleClassH2Inflation_injective K E L) y
  have hd := Module.finrank_mul_finrank K E L
  rw [hdegree, mul_one] at hd
  exact ⟨y, ho.symm.trans ((congrArg addOrderOf hy).trans (hx.trans hd.symm))⟩

end
end Dubon2026
