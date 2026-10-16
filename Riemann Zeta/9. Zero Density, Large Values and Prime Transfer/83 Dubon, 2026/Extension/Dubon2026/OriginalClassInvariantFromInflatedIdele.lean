import Dubon2026.OriginalVerticalIdeleClassInflation
import Dubon2026.OriginalClassH2InvariantFromGenerator

/-! # Normalize an actual class invariant through an inflated idele witness

A full-order target class generates every target class. Its prescribed
inflation is the class of a known auxiliary idele. The original projection
squares and vanishing on the principal kernel compare their canonical
totals. This directly supplies DUB-17's normalization step without a new
equivalence between entire inflation ranges.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E L M : Type) [Field K] [NumberField K]
  [Field E] [NumberField E] [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K E] [IsGalois K E] [IsGalois K L]

/-- The actual inflation identity for one full-order class, together with vertical total preservation and principal reciprocity, identifies the invariant on every original target idele class. -/
theorem originalIdeleClass_invariant_total_of_inflated_idele
    (totalE : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (totalL : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (totalM : groupCohomology (originalFullIdeleRep K M) 2 →+ AddCircle (1 : ℚ))
    (hE : ∀ x, totalM (originalFullIdeleBaseChangeH2 K K E M x) = totalE x)
    (hL : ∀ x, totalM (originalFullIdeleBaseChangeH2 K K L M x) = totalL x)
    (hkernel : ∀ x, (groupCohomology.functor ℤ Gal(M/K) 2).map
      (originalFullClassRepHom K M) x = 0 → totalM x = 0)
    (u : groupCohomology (originalIdeleClassRep K E) 2)
    (hu : addOrderOf u = Module.finrank K E)
    (y : groupCohomology (originalFullIdeleRep K L) 2)
    (hinfl : groupCohomology.map (AlgEquiv.restrictNormalHom E)
      (originalIdeleClassTowerInclusion K E M) 2 u =
        groupCohomology.map (AlgEquiv.restrictNormalHom L)
          (originalIdeleClassTowerInclusion K L M) 2
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) y))
    (invE : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ))
    (hy : invE u = totalL y) :
    ∀ x : groupCohomology (originalFullIdeleRep K E) 2,
      invE ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) x) = totalE x := by
  intro x
  let PE : groupCohomology (originalFullIdeleRep K E) 2 →+
      groupCohomology (originalIdeleClassRep K E) 2 :=
    ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E)).hom.toAddMonoidHom
  let PL : groupCohomology (originalFullIdeleRep K L) 2 →+
      groupCohomology (originalIdeleClassRep K L) 2 :=
    ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)).hom.toAddMonoidHom
  let PM : groupCohomology (originalFullIdeleRep K M) 2 →+
      groupCohomology (originalIdeleClassRep K M) 2 :=
    ((groupCohomology.functor ℤ Gal(M/K) 2).map (originalFullClassRepHom K M)).hom.toAddMonoidHom
  let iE := (groupCohomology.map (AlgEquiv.restrictNormalHom E)
    (originalIdeleClassTowerInclusion K E M) 2).hom.toAddMonoidHom
  let iL := (groupCohomology.map (AlgEquiv.restrictNormalHom L)
    (originalIdeleClassTowerInclusion K L M) 2).hom.toAddMonoidHom
  let bE := (originalFullIdeleBaseChangeH2 K K E M).hom.toAddMonoidHom
  let bL := (originalFullIdeleBaseChangeH2 K K L M).hom.toAddMonoidHom
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (originalIdeleClass_full_order_generates K E u hu (PE x))
  have hp : PM (bE x) = PM (bL (m • y)) := by
    change (groupCohomology.functor ℤ Gal(M/K) 2).map (originalFullClassRepHom K M)
        (originalFullIdeleBaseChangeH2 K K E M x) =
      (groupCohomology.functor ℤ Gal(M/K) 2).map (originalFullClassRepHom K M)
        (originalFullIdeleBaseChangeH2 K K L M (m • y))
    rw [originalFullIdeleBaseChangeH2_vertical_class, originalFullIdeleBaseChangeH2_vertical_class]
    change iE (PE x) = iL (PL (m • y))
    rw [← hm, map_zsmul, map_zsmul, map_zsmul]
    exact congrArg (fun z => m • z) hinfl
  have hz := hkernel (bE x - bL (m • y)) (by
    change PM (bE x - bL (m • y)) = 0
    rw [map_sub, hp, sub_self])
  have ht : totalM (bE x) = totalM (bL (m • y)) :=
    sub_eq_zero.mp ((map_sub totalM _ _).symm.trans hz)
  calc
    invE (PE x) = m • invE u := by rw [← hm, map_zsmul]
    _ = m • totalL y := congrArg (fun z => m • z) hy
    _ = totalL (m • y) := (map_zsmul totalL m y).symm
    _ = totalM (bL (m • y)) := (hL _).symm
    _ = totalM (bE x) := ht.symm
    _ = totalE x := hE x

end
end Dubon2026
