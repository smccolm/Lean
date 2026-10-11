import Mathlib.RepresentationTheory.Intertwining

/-! # Actual scalar character twists over the original coefficient ring -/

namespace Dubon2026
noncomputable section

variable {R G V W : Type} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The genuine character twist of the original coefficient representation. -/
def coefficientCharacterTwist (ρ : Representation R G V) (χ : G →* R) :
    Representation R G V where
  toFun g := χ g • ρ g
  map_one' := by rw [map_one, map_one, one_smul]
  map_mul' g h := by
    ext x
    change χ (g * h) • ρ (g * h) x = χ g • ρ g (χ h • ρ h x)
    rw [map_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]

/-- Twisting an actual intertwining equivalence uses the same original linear
equivalence and character on both sides. -/
def coefficientCharacterTwistEquiv {ρ : Representation R G V}
    {σ : Representation R G W} (e : Representation.Equiv ρ σ) (χ : G →* R) :
    Representation.Equiv (coefficientCharacterTwist ρ χ) (coefficientCharacterTwist σ χ) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' g := by
    ext x
    change e.toLinearEquiv (χ g • ρ g x) = χ g • σ g (e.toLinearEquiv x)
    rw [map_smul]
    exact congrArg (fun y => χ g • y)
      (Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g x)

/-- Linear maps into the actual one-dimensional character representation carry
precisely the contragredient action twisted by that same character. -/
theorem coefficientCharacterTwist_dual_eq_linHom
    (ρ : Representation R G V) (χ : G →* R) :
    coefficientCharacterTwist ρ.dual χ =
      Representation.linHom ρ (coefficientCharacterTwist (1 : Representation R G R) χ) := by
  ext g f x
  rfl

/-- The actual twisted dual evaluates by the original inverse action and the
character at the original group element. -/
theorem coefficientCharacterTwist_dual_apply
    (ρ : Representation R G V) (χ : G →* R) (g : G)
    (f : Module.Dual R V) (x : V) :
    coefficientCharacterTwist ρ.dual χ g f x = χ g * f (ρ g⁻¹ x) := by
  rfl

end
end Dubon2026
