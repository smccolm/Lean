import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # The original additive group action of a genuine linear representation -/

namespace Dubon2026
noncomputable section

variable {O G V W : Type*} [CommRing O] [Group G]
  [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]

/-- The underlying original additive group of a genuine linear representation, written multiplicatively only to consume the original Hopf point-group APIs. The linear operators themselves are unchanged. -/
def representationUnderlyingGroupAction (ρ : Representation O G V) :
    G →* MulAut (Multiplicative V) where
  toFun g := AddEquiv.toMultiplicative (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).toAddEquiv
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (ρ 1 (Multiplicative.toAdd v)) = v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (ρ (g * h) (Multiplicative.toAdd v)) =
      Multiplicative.ofAdd (ρ g (ρ h (Multiplicative.toAdd v)))
    rw [map_mul]
    rfl

/-- Every original vector is acted on by exactly the original linear representation operator. -/
theorem representationUnderlyingGroupAction_apply
    (ρ : Representation O G V) (g : G) (v : V) :
    representationUnderlyingGroupAction ρ g (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (ρ g v) := by
  rfl

/-- An original intertwining linear map is equivariant for the same original additive group actions; the map is its genuine underlying additive homomorphism. -/
theorem representationUnderlyingGroupAction_intertwining
    (ρ : Representation O G V) (τ : Representation O G W) (f : V →ₗ[O] W)
    (hf : ∀ (g : G) (v : V), f (ρ g v) = τ g (f v))
    (g : G) (v : Multiplicative V) :
    f.toAddMonoidHom.toMultiplicative (representationUnderlyingGroupAction ρ g v) =
      representationUnderlyingGroupAction τ g (f.toAddMonoidHom.toMultiplicative v) := by
  exact congrArg Multiplicative.ofAdd (hf g (Multiplicative.toAdd v))

end
end Dubon2026
