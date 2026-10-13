import Dubon2026.PermutationCoordinateRepresentation
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Original cohomology of finite products of representations

The existing cochain and homology functors are additive. Their composite
therefore preserves finite products, giving an isomorphism with the
actual product of original cohomology groups. This is the required
assembly of orbit factors for DUB-17's permutation-lattice calculation.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory Limits
variable {R G ι : Type} [CommRing R] [Group G] (A : ι → Rep R G)

/-- The actual coordinatewise product of the original representations. -/
def originalPiRep : Rep R G := Rep.of {
  toFun := fun g => LinearMap.pi (fun i => (A i).ρ g ∘ₗ LinearMap.proj i)
  map_one' := by ext x i; simp
  map_mul' := by intro g h; ext x i; simp }

private def originalPiRepFan : Fan A :=
  Fan.mk (originalPiRep A) (fun i => Rep.ofHom ⟨LinearMap.proj i, by intro g; rfl⟩)

private def originalPiRepFanIsLimit : IsLimit (originalPiRepFan A) where
  lift s := Rep.ofHom ⟨LinearMap.pi (fun i => (s.π.app ⟨i⟩).hom.toLinearMap), by
    intro g
    apply LinearMap.ext
    intro x
    funext i
    exact Rep.hom_comm_apply (s.π.app ⟨i⟩) g x⟩
  fac s j := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl
  uniq s m w := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    funext i
    exact congrArg (fun f : s.pt ⟶ A i => f.hom x) (w ⟨i⟩)

variable [Fintype ι]

/-- The original coordinate product realizes the categorical product of the same original representations. -/
def originalPiRepIso : originalPiRep A ≅ ∏ᶜ A :=
  (limit.isoLimitCone ⟨_, originalPiRepFanIsLimit A⟩).symm

/-- The existing original group-cohomology functor is additive as the composite of original cochains and homology. -/
theorem original_groupCohomology_functor_additive (n : ℕ) :
    (groupCohomology.functor R G n).Additive := by
  change (groupCohomology.cochainsFunctor R G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).Additive
  infer_instance

/-- Original cohomology of the actual finite coordinate product is isomorphic to the product of the original cohomology groups. -/
def originalFinitePiCohomologyIso (n : ℕ) :
    groupCohomology (originalPiRep A) n ≅ ModuleCat.of R (∀ i, groupCohomology (A i) n) := by
  let F := groupCohomology.functor R G n
  letI : F.Additive := original_groupCohomology_functor_additive n
  exact F.mapIso (originalPiRepIso A) ≪≫ PreservesProduct.iso F A ≪≫
    ModuleCat.piIsoPi (fun i => groupCohomology (A i) n)

/-- Finite original factor cohomology gives finite original product cohomology. -/
theorem originalFinitePi_cohomology_finite (n : ℕ)
    [∀ i, Finite (groupCohomology (A i) n)] :
    Finite (groupCohomology (originalPiRep A) n) :=
  Finite.of_equiv (∀ i, groupCohomology (A i) n)
    (originalFinitePiCohomologyIso A n).symm.toLinearEquiv.toEquiv

/-- The actual finite product cohomology has the product of the original factor orders. -/
theorem originalFinitePi_cohomology_card (n : ℕ) :
    Nat.card (groupCohomology (originalPiRep A) n) =
      ∏ i, Nat.card (groupCohomology (A i) n) :=
  (Nat.card_congr (originalFinitePiCohomologyIso A n).toLinearEquiv.toEquiv).trans Nat.card_pi

end
end Dubon2026
