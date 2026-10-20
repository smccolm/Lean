import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Passage from the auxiliary action to its group-algebra module

The proven intertwining equivalence of CHT auxiliary coordinates must be an
equivalence over the whole group algebra in order to transport freeness.
Mathlib supplies the extension from intertwining maps to module maps.
-/

namespace Dubon2026

noncomputable section

/-- An actual intertwining equivalence induces the full group-algebra equivalence. -/
def auxiliaryRepresentationModuleEquiv
    {R D X Y : Type*} [CommRing R] [Group D]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (σ : Representation R D X) (τ : Representation R D Y)
    (e : X ≃ₗ[R] Y) (he : ∀ d x, e (σ d x) = τ d (e x)) :
    σ.asModule ≃ₗ[MonoidAlgebra R D] τ.asModule := by
  let f : Representation.IntertwiningMap σ τ :=
    { toLinearMap := e.toLinearMap
      isIntertwining' := by intro d; ext x; exact he d x }
  let F := Representation.IntertwiningMap.equivLinearMapAsModule σ τ f
  exact LinearEquiv.ofBijective F e.bijective

/-- Freeness transfers along the actual intertwining equivalence. -/
theorem auxiliaryRepresentationModule_free
    {R D X Y : Type*} [CommRing R] [Group D]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (σ : Representation R D X) (τ : Representation R D Y)
    (e : X ≃ₗ[R] Y) (he : ∀ d x, e (σ d x) = τ d (e x))
    [Module.Free (MonoidAlgebra R D) τ.asModule] :
    Module.Free (MonoidAlgebra R D) σ.asModule :=
  Module.Free.of_equiv (auxiliaryRepresentationModuleEquiv σ τ e he).symm

end
end Dubon2026
