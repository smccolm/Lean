import Dubon2026.OriginalOutsidePointVanishing
import Dubon2026.OriginalOutsideClassExactSequence
import Dubon2026.OriginalIdeleClassTowerCoefficients

/-! # Actual invariant class-quotient lifting and base-field descent

Outside-unit H1 vanishing makes the original quotient map surjective on
invariants. Existing full-class descent then supplies an actual base-field
class representative. This removes the invariant-lifting premise for the
class-formation coefficient on DUB-17's original global-duality route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal)

include hu

/-- Every original class-quotient H0 class lifts through the actual full-class quotient map. -/
theorem originalClassesModOutside_H0_surjective :
    Function.Surjective ((groupCohomology.functor ℤ Gal(L/K) 0).map
      (originalIdeleClassesModOutsideRepHom K L S hS)) := by
  let hX := originalOutsideClassShortComplex_shortExact K L S hS
  have hz := originalOutsideUnit_first_zero_of_unramified K L S hS hu
  have he := groupCohomology.mapShortComplex₃_exact hX (i := 0) rfl
  haveI : Epi ((groupCohomology.functor ℤ Gal(L/K) 0).map
      (originalIdeleClassesModOutsideRepHom K L S hS)) := he.epi_f (hz.eq_zero_of_tgt _)
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Every invariant original quotient class has an invariant original full-class representative. -/
theorem originalClassesModOutside_fixed_has_fixed_representative
    (x : originalIdeleClassesModOutsideRep K L S hS)
    (hx : ∀ g, (originalIdeleClassesModOutsideRep K L S hS).ρ g x = x) :
    ∃ c : originalIdeleClassRep K L,
      (originalIdeleClassesModOutsideRepHom K L S hS).hom c = x ∧
        ∀ g, (originalIdeleClassRep K L).ρ g c = c := by
  let A := originalIdeleClassRep K L
  let B := originalIdeleClassesModOutsideRep K L S hS
  let f := originalIdeleClassesModOutsideRepHom K L S hS
  let xi : B.ρ.invariants := ⟨x, hx⟩
  obtain ⟨y, hy⟩ := originalClassesModOutside_H0_surjective K L S hS hu
    ((groupCohomology.H0Iso B).inv xi)
  let yi : A.ρ.invariants := (groupCohomology.H0Iso A).hom y
  have hm : (groupCohomology.H0Iso B).hom
      ((groupCohomology.functor ℤ Gal(L/K) 0).map f y) =
      ((Rep.invariantsFunctor ℤ Gal(L/K)).map f) yi :=
    congrArg (fun t : groupCohomology A 0 ⟶ ModuleCat.of ℤ B.ρ.invariants => t y)
      (groupCohomology.map_id_comp_H0Iso_hom f)
  have hi : (groupCohomology.H0Iso B).hom ((groupCohomology.H0Iso B).inv xi) = xi :=
    (groupCohomology.H0Iso B).toLinearEquiv.apply_symm_apply xi
  rw [hy, hi] at hm
  exact ⟨yi.val, congrArg Subtype.val hm.symm, yi.property⟩

/-- An actual invariant quotient class is represented by the inclusion of a genuine base-field idele class. -/
theorem originalClassesModOutside_fixed_has_base_class
    (x : originalIdeleClassesModOutsideRep K L S hS)
    (hx : ∀ g, (originalIdeleClassesModOutsideRep K L S hS).ρ g x = x) :
    ∃ c : OriginalNumberFieldIdeleClassGroup K,
      (originalIdeleClassesModOutsideRepHom K L S hS).hom
        (Additive.ofMul (originalIdeleClassBaseChangeMap K L c)) = x := by
  obtain ⟨y, hy, hfixed⟩ :=
    originalClassesModOutside_fixed_has_fixed_representative K L S hS hu x hx
  obtain ⟨c, hc⟩ := originalIdeleClassBaseChangeMap_surjective_fixed K L y.toMul
    (fun g => congrArg Additive.toMul (hfixed g))
  refine ⟨c, ?_⟩
  exact (congrArg (fun z : OriginalNumberFieldIdeleClassGroup L =>
    (originalIdeleClassesModOutsideRepHom K L S hS).hom (Additive.ofMul z)) hc).trans hy

end
end Dubon2026
