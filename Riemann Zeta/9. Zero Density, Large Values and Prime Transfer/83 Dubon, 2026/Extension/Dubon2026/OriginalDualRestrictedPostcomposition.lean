import Dubon2026.OriginalContravariantHomSequence

/-! Map the restricted original dual sequence to the dual of the
restricted presentation with a genuine local coefficient target. This is
the precise diagram for the global S-unit to local-unit connecting map in
DUB-17, retaining the inverse in the restricted Hom action. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV1 Rep.hV2
variable {G H R : Type} [Group G] [Group H] [CommRing R]
  (j : H →* G) (A D : Rep.{0} R G) (E : Rep.{0} R H)

/-- The actual restricted Hom maps to local Hom by literal
postcomposition with the given original coefficient morphism. -/
def originalRestrictedInternalHomPostcomposition (m : Rep.res j D ⟶ E) :
    Rep.res j ((Rep.ihom A).obj D) ⟶ (Rep.ihom (Rep.res j A)).obj E := by
  let l : Rep.res j ((Rep.ihom A).obj D) →ₗ[R] (Rep.ihom (Rep.res j A)).obj E := {
    toFun f := m.hom.toLinearMap.comp (show A →ₗ[R] D from f)
    map_add' f g := by
      apply LinearMap.ext
      intro x
      let f' : A →ₗ[R] D := f
      let g' : A →ₗ[R] D := g
      exact map_add m.hom.toLinearMap (f' x) (g' x)
    map_smul' r f := by
      apply LinearMap.ext
      intro x
      let f' : A →ₗ[R] D := f
      exact map_smul m.hom.toLinearMap r (f' x) }
  exact Rep.ofHom ⟨l, fun g => by
    apply LinearMap.ext
    intro f
    change A →ₗ[R] D at f
    apply LinearMap.ext
    intro x
    change m.hom (D.ρ (j g) (f (A.ρ (j g)⁻¹ x))) =
      E.ρ g (m.hom (f (A.ρ (j g⁻¹) x)))
    rw [← map_inv j g]
    exact Rep.hom_comm_apply m g (f (A.ρ (j g⁻¹) x))⟩

/-- The same local coefficient map gives a commuting diagram from the
restricted original dual sequence, at all three original Hom terms. -/
def originalDualRestrictedPostcomposition
    (D : Rep.{0} ℤ G) (E : Rep.{0} ℤ H)
    (X : ShortComplex (Rep.{0} ℤ G)) (m : Rep.res j D ⟶ E) :
    (originalContravariantHomShortComplex X D).map (Rep.resFunctor j) ⟶
      originalContravariantHomShortComplex (X.map (Rep.resFunctor j)) E where
  τ₁ := originalRestrictedInternalHomPostcomposition j X.X₃ D E m
  τ₂ := originalRestrictedInternalHomPostcomposition j X.X₂ D E m
  τ₃ := originalRestrictedInternalHomPostcomposition j X.X₁ D E m
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl

end
end Dubon2026
