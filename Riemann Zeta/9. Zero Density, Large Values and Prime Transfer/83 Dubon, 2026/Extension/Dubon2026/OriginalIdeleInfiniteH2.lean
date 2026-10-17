import Dubon2026.OriginalGlobalInfiniteH2
import Dubon2026.OriginalFullDecompositionIdeleH2Lift

/-! # Literal infinite localization of original full-idele H2

Evaluation uses the actual original decomposition action and completion.
It agrees with original global localization on principal classes and
vanishes on the same single-finite-prime lift used by the normalized
witness. These are the two exact edges required by DUB-17's real
correction and full-order original idele-class construction.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Evaluate the original full idele at its actual infinite completion. -/
def originalFullIdeleInfiniteRepHom (v : InfinitePlace L) :
    Rep.res (OriginalInfiniteDecompositionGroup K L v).subtype (originalFullIdeleRep K L) ⟶
      originalInfiniteUnitRep K L v :=
  Rep.ofHom ⟨(numberFieldIdeleInfiniteComponent L v).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    apply congrArg Additive.ofMul
    apply Units.ext
    exact numberFieldInfiniteAdeleGaloisMap_apply K L σ.val x.toMul.val.1 v v σ.property⟩

/-- Actual subgroup restriction and infinite-coordinate evaluation on
the original full-idele H2. -/
def originalFullIdeleInfiniteH2 (v : InfinitePlace L) :
    groupCohomology (originalFullIdeleRep K L) 2 ⟶
      groupCohomology (originalInfiniteUnitRep K L v) 2 :=
  groupCohomology.map (OriginalInfiniteDecompositionGroup K L v).subtype
    (originalFullIdeleInfiniteRepHom K L v) 2

/-- The principal map retains precisely the original global infinite localization. -/
theorem originalFullIdeleInfiniteH2_principal
    (v : InfinitePlace L) (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    originalFullIdeleInfiniteH2 K L v
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) =
        originalGlobalInfiniteH2 K L v x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)
    simp only [groupCohomology.H2π_comp_map_apply]
    rfl

/-- The actual single-finite-prime lift used by the normalized witness
has zero localization at every original infinite place. -/
theorem originalFullDecompositionIdeleH2Lift_infinite
    (w : HeightOneSpectrum (𝓞 L)) (hw : OriginalFiniteDecompositionGroup K L w = ⊤)
    (v : InfinitePlace L) (x : groupCohomology (originalAdicUnitRep K L w) 2) :
    originalFullIdeleInfiniteH2 K L v (originalFullDecompositionIdeleH2Lift K L w hw x) = 0 := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    simp only [originalFullIdeleInfiniteH2, originalFullDecompositionIdeleH2Lift,
      ModuleCat.comp_apply, originalCohomologyReindex, CategoryTheory.asIso_hom,
      groupCohomology.functor, groupCohomology.H2π_comp_map_apply]
    rw [← map_zero (groupCohomology.H2π (originalInfiniteUnitRep K L v)).hom]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext gh
    exact congrArg Additive.ofMul (originalIdeleSingleFinite_infinite L w _ v)

end
end Dubon2026
