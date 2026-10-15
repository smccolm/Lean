import Dubon2026.OriginalSPlaceIdeleSequence

/-! # Original S-place classes inside the full classes modulo outside units

This is the injective comparison in Milne I.4.1 at the fixed finite support.
The outside-unit image and the map on S-place classes are constructed from
the actual idele coordinates. No principal-ideal or surjectivity assertion
is assumed: the remaining cokernel is a separate arithmetic obligation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

private def binaryInl {R G : Type} [CommRing R] [Group G] (A B : Rep R G) :
    A ⟶ Rep.of (A.ρ.prod B.ρ) :=
  Rep.ofHom ⟨LinearMap.inl R A B, by
    intro g
    apply LinearMap.ext
    intro x
    exact Prod.ext rfl ((B.ρ g).map_zero).symm⟩

private def binaryInr {R G : Type} [CommRing R] [Group G] (A B : Rep R G) :
    B ⟶ Rep.of (A.ρ.prod B.ρ) :=
  Rep.ofHom ⟨LinearMap.inr R A B, by
    intro g
    apply LinearMap.ext
    intro x
    exact Prod.ext ((A.ρ g).map_zero).symm rfl⟩

private theorem split_quotient_ker {R E J A B C : Type} [CommRing R]
    [AddCommGroup E] [AddCommGroup J] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R E] [Module R J] [Module R A] [Module R B] [Module R C]
    (e : J ≃ₗ[R] A × B) (p : E →ₗ[R] J) (q : J →ₗ[R] C)
    (he : ∀ x, q x = 0 ↔ ∃ y, p y = x) :
    let i := e.symm.toLinearMap.comp (LinearMap.inl R A B)
    let j := e.symm.toLinearMap.comp (LinearMap.inr R A B)
    LinearMap.ker ((LinearMap.range (q.comp j)).mkQ.comp (q.comp i)) =
      LinearMap.range ((LinearMap.fst R A B).comp (e.toLinearMap.comp p)) := by
  intro i j
  ext x
  change Submodule.Quotient.mk (q (i x)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    change q (j y) = q (i x) at hy
    have hz : q (i x - j y) = 0 := by rw [map_sub, hy, sub_self]
    obtain ⟨z, hz⟩ := (he _).mp hz
    refine ⟨z, ?_⟩
    change (e (p z)).1 = x
    rw [hz, map_sub]
    change (e (e.symm (x, 0)) - e (e.symm (0, y))).1 = x
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact sub_zero x
  · rintro ⟨z, rfl⟩
    let y := (e (p z)).2
    have hsplit : i ((e (p z)).1) + j y = p z := by
      apply e.injective
      rw [map_add]
      change e (e.symm ((e (p z)).1, 0)) + e (e.symm (0, y)) = _
      rw [e.apply_symm_apply, e.apply_symm_apply]
      exact Prod.ext (add_zero _) (zero_add _)
    have hz : q (p z) = 0 := (he _).mpr ⟨z, rfl⟩
    have hq := congrArg q hsplit
    rw [map_add, hz] at hq
    refine ⟨-y, ?_⟩
    change q (j (-y)) = q (i ((e (p z)).1))
    rw [map_neg, map_neg]
    exact (eq_neg_of_add_eq_zero_left hq).symm

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The S-place local product embedded in actual ideles by setting every outside coordinate to one. -/
def originalSPlaceSupportedInclusion :
    supportedUnrestrictedUnitRep K L S hS ⟶ originalSupportedIdeleRep K L S hS :=
  binaryInl (supportedUnrestrictedUnitRep K L S hS) (supportedOutsideUnitRep K L S hS) ≫
    (supportedIdeleLocalFactorRepIso K L S hS).inv

/-- The outside integral units embedded in actual ideles by setting the S-place coordinates to one. -/
def originalOutsideSupportedInclusion :
    supportedOutsideUnitRep K L S hS ⟶ originalSupportedIdeleRep K L S hS :=
  binaryInr (supportedUnrestrictedUnitRep K L S hS) (supportedOutsideUnitRep K L S hS) ≫
    (supportedIdeleLocalFactorRepIso K L S hS).inv

/-- The actual outside integral units mapped to the original full idele classes. -/
def originalOutsideIdeleClassRepHom :
    supportedOutsideUnitRep K L S hS ⟶ originalIdeleClassRep K L :=
  originalOutsideSupportedInclusion K L S hS ≫ originalSupportedClassRepHom K L S hS

private theorem outsideRange_stable (g : Gal(L/K)) :
    LinearMap.range (originalOutsideIdeleClassRepHom K L S hS).hom.toLinearMap ≤
      (LinearMap.range (originalOutsideIdeleClassRepHom K L S hS).hom.toLinearMap).comap
        ((originalIdeleClassRep K L).ρ g) :=
  (originalOutsideIdeleClassRepHom K L S hS).hom.range.apply_mem_toSubmodule g

/-- The original full idele classes modulo the actual outside integral units. -/
def originalIdeleClassesModOutsideRep : Rep ℤ Gal(L/K) :=
  (originalIdeleClassRep K L).quotient
    (LinearMap.range (originalOutsideIdeleClassRepHom K L S hS).hom.toLinearMap)
    (outsideRange_stable K L S hS)

/-- The literal original full-class quotient map. -/
def originalIdeleClassesModOutsideRepHom :
    originalIdeleClassRep K L ⟶ originalIdeleClassesModOutsideRep K L S hS :=
  (originalIdeleClassRep K L).mkQ
    (LinearMap.range (originalOutsideIdeleClassRepHom K L S hS).hom.toLinearMap)
    (outsideRange_stable K L S hS)

/-- The S-place local product maps to the original full classes modulo outside units. -/
def originalSPlaceToClassesModOutside :
    supportedUnrestrictedUnitRep K L S hS ⟶ originalIdeleClassesModOutsideRep K L S hS :=
  originalSPlaceSupportedInclusion K L S hS ≫
    originalSupportedClassRepHom K L S hS ≫ originalIdeleClassesModOutsideRepHom K L S hS

private theorem supportedClass_zero_iff (x : originalSupportedIdeleRep K L S hS) :
    (originalSupportedClassRepHom K L S hS).hom x = 0 ↔
      ∃ y : sUnitOriginalRep K L S hS, (originalSupportedPrincipalRepHom K L S hS).hom y = x := by
  change numberFieldSupportedIdeleClassMap L S x.toMul = 1 ↔ _
  change x.toMul ∈ (numberFieldSupportedIdeleClassMap L S).ker ↔ _
  rw [numberFieldSupportedIdeleClassMap_ker]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y.toMul, congrArg Additive.toMul hy⟩

/-- The exact kernel of the actual S-place map is the original diagonal S-unit image. -/
theorem originalSPlaceToClassesModOutside_ker :
    LinearMap.ker (originalSPlaceToClassesModOutside K L S hS).hom.toLinearMap =
      LinearMap.range (originalSPlacePrincipalRepHom K L S hS).hom.toLinearMap := by
  exact split_quotient_ker (supportedIdeleLocalFactorLinearEquiv L S)
    (originalSupportedPrincipalRepHom K L S hS).hom.toLinearMap
    (originalSupportedClassRepHom K L S hS).hom.toLinearMap
    (supportedClass_zero_iff K L S hS)

/-- The original S-place classes map to the full idele classes modulo outside units. -/
def originalSPlaceClassComparison :
    originalSPlaceIdeleClassRep K L S hS ⟶ originalIdeleClassesModOutsideRep K L S hS :=
  Rep.ofHom ⟨(LinearMap.range (originalSPlacePrincipalRepHom K L S hS).hom.toLinearMap).liftQ
    (originalSPlaceToClassesModOutside K L S hS).hom.toLinearMap
    (originalSPlaceToClassesModOutside_ker K L S hS).symm.le, by
      intro g
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H x => exact Rep.hom_comm_apply (originalSPlaceToClassesModOutside K L S hS) g x⟩

/-- The class comparison retains the literal local-product representative and original full-class map. -/
theorem originalSPlaceClassComparison_mk
    (x : supportedUnrestrictedUnitRep K L S hS) :
    (originalSPlaceClassComparison K L S hS).hom
      ((originalSPlaceIdeleClassRepHom K L S hS).hom x) =
        (originalSPlaceToClassesModOutside K L S hS).hom x := rfl

/-- The original S-place class comparison is injective at the fixed support. -/
theorem originalSPlaceClassComparison_injective :
    Function.Injective (originalSPlaceClassComparison K L S hS).hom := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _
    (originalSPlaceToClassesModOutside_ker K L S hS).le

end
end Dubon2026
