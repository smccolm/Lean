import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Data.Complex.Basic

/-! # The actual character twist of a group representation -/

namespace Dubon2026

noncomputable section

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- The original representation twisted by an actual scalar group character, with no prescribed eigenvalue relation. -/
def scalarTwistRepresentation (ρ : Representation ℂ G V) (χ : G →* ℂ) : Representation ℂ G V where
  toFun g := χ g • ρ g
  map_one' := by
    rw [map_one, map_one, one_smul]
  map_mul' g h := by
    ext x
    change χ (g * h) • ρ (g * h) x = χ g • ρ g (χ h • ρ h x)
    rw [map_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]

/-- The genuine twist acts by the original operator and the actual character value at that same group element. -/
theorem scalarTwistRepresentation_apply (ρ : Representation ℂ G V) (χ : G →* ℂ) (g : G) (x : V) :
    scalarTwistRepresentation ρ χ g x = χ g • ρ g x := rfl

/-- A genuine intertwiner into a character twist satisfies the exact original twisted action equation. -/
theorem scalarTwist_intertwining_apply {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (χ : G →* ℂ)
    (T : Representation.IntertwiningMap ρ (scalarTwistRepresentation σ χ)) (g : G) (x : V) :
    T (ρ g x) = χ g • σ g (T x) :=
  Representation.IntertwiningMap.isIntertwining ρ (scalarTwistRepresentation σ χ) T g x

/-- A genuine twisted intertwiner preserves fixed vectors for every subgroup on which the actual character is trivial. -/
theorem scalarTwist_intertwining_fixed (ρ : Representation ℂ G V) (χ : G →* ℂ)
    (T : Representation.IntertwiningMap ρ (scalarTwistRepresentation ρ χ))
    (K : Subgroup G) (hχ : ∀ g : K, χ g.val = 1)
    (x : V) (hx : ∀ g : K, ρ g.val x = x) : ∀ g : K, ρ g.val (T x) = T x := by
  intro g
  have h := scalarTwist_intertwining_apply ρ ρ χ T g.val x
  rw [hx g, hχ g, one_smul] at h
  exact h.symm

end
end Dubon2026
