import Dubon2026.OriginalSPlaceClassComparison

/-! # The original outside-unit and full-class exact sequence

The outside-unit inclusion has zero intersection with principal ideles,
detected at the existing infinite-place diagonal. Its literal quotient
therefore gives the finite-stage exact sequence needed to transfer the
proved class-cohomology inputs to Milne's class-formation coefficient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual outside integral units embed in the original full idele classes. -/
theorem originalOutsideIdeleClassRepHom_injective :
    Function.Injective (originalOutsideIdeleClassRepHom K L S hS).hom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  let y := (originalOutsideSupportedInclusion K L S hS).hom x
  have hy : y.toMul ∈ (numberFieldSupportedIdeleClassMap L S).ker := hx
  rw [numberFieldSupportedIdeleClassMap_ker] at hy
  obtain ⟨u, hu⟩ := hy
  have hp : (originalSupportedPrincipalRepHom K L S hS).hom (Additive.ofMul u) = y :=
    congrArg Additive.ofMul hu
  have hproj : (originalSPlacePrincipalRepHom K L S hS).hom (Additive.ofMul u) = 0 := by
    change (originalSupportedUnrestrictedProjection K L S hS).hom
      ((originalSupportedPrincipalRepHom K L S hS).hom (Additive.ofMul u)) = 0
    rw [hp]
    exact congrArg Prod.fst ((supportedIdeleLocalFactorLinearEquiv L S).apply_symm_apply (0, x))
  have hu0 : Additive.ofMul u = (0 : sUnitOriginalRep K L S hS) :=
    originalSPlacePrincipalRepHom_injective K L S hS (hproj.trans (map_zero _).symm)
  have hy0 : y = 0 := hp.symm.trans
    ((congrArg (fun z : sUnitOriginalRep K L S hS =>
      (originalSupportedPrincipalRepHom K L S hS).hom z) hu0).trans
        (originalSupportedPrincipalRepHom K L S hS).hom.toLinearMap.map_zero)
  have he := congrArg (supportedIdeleLocalFactorLinearEquiv L S) hy0
  change (supportedIdeleLocalFactorLinearEquiv L S)
    ((supportedIdeleLocalFactorLinearEquiv L S).symm (0, x)) = _ at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact congrArg Prod.snd (he.trans (supportedIdeleLocalFactorLinearEquiv L S).map_zero)

/-- The original outside units, full classes and their literal quotient. -/
def originalOutsideClassShortComplex : ShortComplex (Rep ℤ Gal(L/K)) where
  X₁ := supportedOutsideUnitRep K L S hS
  X₂ := originalIdeleClassRep K L
  X₃ := originalIdeleClassesModOutsideRep K L S hS
  f := originalOutsideIdeleClassRepHom K L S hS
  g := originalIdeleClassesModOutsideRepHom K L S hS
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- The literal full-class quotient forms a short exact sequence with the actual outside units. -/
theorem originalOutsideClassShortComplex_shortExact :
    (originalOutsideClassShortComplex K L S hS).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (originalOutsideIdeleClassRepHom_injective K L S hS)
    epi_g := (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _) }
  apply ((originalOutsideClassShortComplex K L S hS).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ Gal(L/K)) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact (Submodule.ker_mkQ _).symm

end
end Dubon2026
