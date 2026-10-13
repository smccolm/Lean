import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology

/-! # Global unit H2 embeds into the original idele H2

The proved vanishing of original idele-class H1 makes the actual principal
idele map injective on H2. The adjacent exact sequence identifies its
image with the kernel of the actual class map. This is the finite-stage
global-to-local obstruction sequence needed before constructing the
normalized invariant sum on DUB-17's arithmetic duality chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The actual principal idele map is injective on original global unit H2. -/
theorem originalFullPrincipalH2_injective :
    Function.Injective ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalFullPrincipalRepHom K L)) := by
  let hX := originalFullIdeleShortComplex_shortExact K L
  have hz := originalIdeleClass_finiteGalois_first_zero K L
  have he := groupCohomology.mapShortComplex₁_exact hX (i := 1) rfl
  haveI : Mono ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalFullPrincipalRepHom K L)) := he.mono_g (hz.eq_zero_of_src _)
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
/-- An original idele H2 class comes from global field units exactly when its class image vanishes. -/
theorem originalFullPrincipalH2_range_iff_class_zero
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    (∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2,
      (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) y = x) ↔
      (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x = 0 := by
  have he := (groupCohomology.mapShortComplex₂_exact
    (originalFullIdeleShortComplex_shortExact K L) 2).moduleCat_range_eq_ker
  change ((groupCohomology.functor ℤ Gal(L/K) 2).map
    (originalFullPrincipalRepHom K L)).hom.range =
      ((groupCohomology.functor ℤ Gal(L/K) 2).map
        (originalFullClassRepHom K L)).hom.ker at he
  change x ∈ ((groupCohomology.functor ℤ Gal(L/K) 2).map
    (originalFullPrincipalRepHom K L)).hom.range ↔ _
  rw [he]
  rfl

end
end Dubon2026
