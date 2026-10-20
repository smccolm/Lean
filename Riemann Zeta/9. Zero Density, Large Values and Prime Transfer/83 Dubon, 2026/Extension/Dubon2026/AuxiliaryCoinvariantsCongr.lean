import Mathlib.RepresentationTheory.Coinvariants

/-! # Transport of the actual auxiliary coinvariant quotient

This uses Mathlib's induced maps on coinvariants to carry the proved
coordinate trace back to the original automorphic functions.
-/

namespace Dubon2026

noncomputable section

/-- Actual intertwining coordinates induce an isomorphism of coinvariant quotients. -/
def auxiliaryCoinvariantsCongr
    {R D X Y : Type*} [CommRing R] [Group D]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (σ : Representation R D X) (τ : Representation R D Y)
    (e : X ≃ₗ[R] Y) (he : ∀ d x, e (σ d x) = τ d (e x)) :
    σ.Coinvariants ≃ₗ[R] τ.Coinvariants := by
  let f : Representation.IntertwiningMap σ τ :=
    { toLinearMap := e.toLinearMap
      isIntertwining' := by intro d; ext x; exact he d x }
  let g : Representation.IntertwiningMap τ σ :=
    { toLinearMap := e.symm.toLinearMap
      isIntertwining' := by
        intro d
        ext y
        apply e.injective
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, he] }
  refine LinearEquiv.ofLinear (Representation.Coinvariants.map σ τ f)
    (Representation.Coinvariants.map τ σ g) ?_ ?_
  · apply Representation.Coinvariants.hom_ext
    ext y
    change Representation.Coinvariants.mk τ (e (e.symm y)) = Representation.Coinvariants.mk τ y
    rw [e.apply_symm_apply]
  · apply Representation.Coinvariants.hom_ext
    ext x
    change Representation.Coinvariants.mk σ (e.symm (e x)) = Representation.Coinvariants.mk σ x
    rw [e.symm_apply_apply]

/-- The induced quotient equivalence applies the original coordinate map to representatives. -/
theorem auxiliaryCoinvariantsCongr_mk
    {R D X Y : Type*} [CommRing R] [Group D]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (σ : Representation R D X) (τ : Representation R D Y)
    (e : X ≃ₗ[R] Y) (he : ∀ d x, e (σ d x) = τ d (e x)) (x : X) :
    auxiliaryCoinvariantsCongr σ τ e he (Representation.Coinvariants.mk σ x) =
      Representation.Coinvariants.mk τ (e x) := rfl

end
end Dubon2026
