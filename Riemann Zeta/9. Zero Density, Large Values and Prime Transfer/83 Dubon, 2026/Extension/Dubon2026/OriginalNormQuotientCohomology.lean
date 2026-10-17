import Dubon2026.OriginalCoefficientNormCohomology
import Dubon2026.CoinducedCohomologyTrace
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.LinearAlgebra.Quotient.Defs

/-! # The degree-two map on actual morphisms modulo norms

The missing converse norm criterion is injectivity of the genuine
cohomology map on morphisms modulo sums of conjugates. Construct that map
directly from the existing positive cohomology functor and coinduced norm
vanishing. This avoids a graded cup-product framework for the definition
and its norm compatibility. Injectivity for the arithmetic class system
is not asserted here.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (A C : Rep.{0} ℤ G)

/-- The genuine sum-of-conjugates construction preserves addition of coefficient maps. -/
def originalCoefficientNormAddHom : (A →ₗ[ℤ] C) →+ (A ⟶ C) :=
  AddMonoidHom.mk' (originalCoefficientNormMorphism A C) (by
    intro f g
    apply Rep.hom_ext
    ext x
    simp [originalCoefficientNormMorphism_apply, Rep.add_hom, Finset.sum_add_distrib])

/-- The genuine sum-of-conjugates construction is linear in its original coefficient map. -/
def originalCoefficientNormLinearMap : (A →ₗ[ℤ] C) →ₗ[ℤ] (A ⟶ C) where
  toFun := originalCoefficientNormMorphism A C
  map_add' := (originalCoefficientNormAddHom A C).map_add
  map_smul' n f := (originalCoefficientNormAddHom A C).map_zsmul n f

/-- Actual equivariant coefficient morphisms modulo literal sums of conjugates. -/
abbrev OriginalCoefficientNormQuotient :=
  (A ⟶ C) ⧸ (originalCoefficientNormLinearMap A C).range

/-- Positive cohomology defines a map on the actual quotient by norm morphisms. -/
def originalNormQuotientCohomologyMap (n : ℕ) : OriginalCoefficientNormQuotient A C →ₗ[ℤ]
    ((groupCohomology.functor ℤ G (n + 1)).obj A ⟶
      (groupCohomology.functor ℤ G (n + 1)).obj C) :=
  (originalCoefficientNormLinearMap A C).range.liftQ
    ((groupCohomology.functor ℤ G (n + 1)).mapLinearMap ℤ) (by
      rintro _ ⟨f, rfl⟩
      exact originalCoefficientNormMorphism_positive_map_zero A C f n)

/-- The quotient map evaluates to the original positive cohomology map. -/
theorem originalNormQuotientCohomologyMap_mk (n : ℕ) (φ : A ⟶ C) :
    originalNormQuotientCohomologyMap A C n (Submodule.Quotient.mk φ) =
      (groupCohomology.functor ℤ G (n + 1)).map φ := rfl

/-- A class in the actual norm quotient vanishes precisely when the original morphism has a literal norm witness. -/
theorem originalCoefficientNormQuotient_mk_eq_zero_iff (φ : A ⟶ C) :
    (Submodule.Quotient.mk φ : OriginalCoefficientNormQuotient A C) = 0 ↔
      ∃ η : A →ₗ[ℤ] C, ∀ x : A,
        φ.hom x = ∑ g : G, C.ρ g (η (A.ρ g⁻¹ x)) := by
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨η, fun x => ?_⟩
    rw [← hη]
    exact originalCoefficientNormMorphism_apply A C η x
  · rintro ⟨η, hη⟩
    refine ⟨η, Rep.hom_ext (DFunLike.ext _ _ fun x => ?_)⟩
    exact (originalCoefficientNormMorphism_apply A C η x).trans (hη x).symm

end
end Dubon2026
