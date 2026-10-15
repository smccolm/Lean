import Dubon2026.OriginalSupportedH2Unrestricted

/-! # The source S-place idele quotient with the original diagonal S-units

Milne I.4 uses the product of completion units at S (including infinity),
with outside coordinates equal to one. The existing unrestricted factor is
precisely this group for finite S. Its actual diagonal S-unit inclusion is
injective, and its literal quotient gives the required short exact sequence.
No surjectivity onto the full idele-class group or support enlargement is used.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original S-unit diagonal in the actual S-place local unit product. -/
def originalSPlacePrincipalRepHom :
    sUnitOriginalRep K L S hS ⟶ supportedUnrestrictedUnitRep K L S hS :=
  originalSupportedPrincipalRepHom K L S hS ≫
    originalSupportedUnrestrictedProjection K L S hS

/-- At every infinite place the map is the literal original field embedding. -/
theorem originalSPlacePrincipalRepHom_infinite
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) (v : InfinitePlace L) :
    ((originalSPlacePrincipalRepHom K L S hS).hom x (Sum.inl v)).toMul.val =
      algebraMap L v.Completion x.toMul.val.val := rfl

/-- At every finite place in S the map is the literal original field embedding. -/
theorem originalSPlacePrincipalRepHom_finite
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) (v : S) :
    ((originalSPlacePrincipalRepHom K L S hS).hom x (Sum.inr v)).toMul.val =
      algebraMap L (v.val.adicCompletion L) x.toMul.val.val := rfl

/-- The actual S-place diagonal is injective, detected already at an original infinite place. -/
theorem originalSPlacePrincipalRepHom_injective :
    Function.Injective (originalSPlacePrincipalRepHom K L S hS).hom := by
  intro x y h
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have hv := congrArg (fun z => (z (Sum.inl v)).toMul.val) h
  change algebraMap L v.Completion x.toMul.val.val =
    algebraMap L v.Completion y.toMul.val.val at hv
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact (algebraMap L v.Completion).injective hv

private theorem principalRange_stable (g : Gal(L/K)) :
    LinearMap.range (originalSPlacePrincipalRepHom K L S hS).hom.toLinearMap ≤
      (LinearMap.range (originalSPlacePrincipalRepHom K L S hS).hom.toLinearMap).comap
        ((supportedUnrestrictedUnitRep K L S hS).ρ g) :=
  (originalSPlacePrincipalRepHom K L S hS).hom.range.apply_mem_toSubmodule g

/-- The actual source S-place idele classes: the local product modulo the original diagonal S-units. -/
def originalSPlaceIdeleClassRep : Rep ℤ Gal(L/K) :=
  (supportedUnrestrictedUnitRep K L S hS).quotient
    (LinearMap.range (originalSPlacePrincipalRepHom K L S hS).hom.toLinearMap)
    (principalRange_stable K L S hS)

/-- The literal quotient map to the actual S-place idele classes. -/
def originalSPlaceIdeleClassRepHom :
    supportedUnrestrictedUnitRep K L S hS ⟶ originalSPlaceIdeleClassRep K L S hS :=
  (supportedUnrestrictedUnitRep K L S hS).mkQ
    (LinearMap.range (originalSPlacePrincipalRepHom K L S hS).hom.toLinearMap)
    (principalRange_stable K L S hS)

/-- The source S-unit, S-place idele, and S-place class sequence. -/
def originalSPlaceIdeleShortComplex : ShortComplex (Rep ℤ Gal(L/K)) where
  X₁ := sUnitOriginalRep K L S hS
  X₂ := supportedUnrestrictedUnitRep K L S hS
  X₃ := originalSPlaceIdeleClassRep K L S hS
  f := originalSPlacePrincipalRepHom K L S hS
  g := originalSPlaceIdeleClassRepHom K L S hS
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- The original diagonal and literal S-place quotient form a short exact sequence at the fixed support. -/
theorem originalSPlaceIdeleShortComplex_shortExact :
    (originalSPlaceIdeleShortComplex K L S hS).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (originalSPlacePrincipalRepHom_injective K L S hS)
    epi_g := (Rep.epi_iff_surjective _).mpr ?_ }
  · apply ((originalSPlaceIdeleShortComplex K L S hS).exact_map_iff_of_faithful
      (forget₂ (Rep ℤ Gal(L/K)) (ModuleCat ℤ))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (Submodule.ker_mkQ _).symm
  · exact Submodule.mkQ_surjective _

/-- A literal S-place idele class vanishes exactly when the idele is an original diagonal S-unit. -/
theorem originalSPlaceIdeleClassRepHom_eq_zero_iff
    (x : supportedUnrestrictedUnitRep K L S hS) :
    (originalSPlaceIdeleClassRepHom K L S hS).hom x = 0 ↔
      ∃ y : sUnitOriginalRep K L S hS, (originalSPlacePrincipalRepHom K L S hS).hom y = x :=
  Submodule.Quotient.mk_eq_zero _

end
end Dubon2026
