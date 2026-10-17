import Dubon2026.OriginalCoinducedInvariantNorms
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective

/-! # Integral extension from the actual invariant lattice

The degree-zero route to DUB-17's converse norm criterion needs to
extend a divided invariant functional. The action-defect map has
torsion-free finite image, hence projective image over the integers.
Splitting that image gives a literal retraction onto the original
invariants. No invariant splitting is assumed.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
attribute [local instance 1100] Submodule.module
variable {G : Type} [Group G] (M : Rep.{0} ℤ G)
variable [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]

/-- The original invariant lattice admits an integral linear retraction derived from the action-defect image. -/
theorem originalInvariant_linear_retraction_exists :
    ∃ r : M →ₗ[ℤ] M.ρ.invariants, ∀ x : M.ρ.invariants, r x = x := by
  letI : Module ℤ (G → M) := Pi.module G (fun _ => M) ℤ
  let D : M →ₗ[ℤ] (G → M) := LinearMap.pi fun g => M.ρ g - LinearMap.id
  have hs : Function.Surjective D.rangeRestrict := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property D.rangeRestrict
    (LinearMap.id : LinearMap.range D →ₗ[ℤ] LinearMap.range D) hs
  let r₀ : M →ₗ[ℤ] M := LinearMap.id - s.comp D.rangeRestrict
  have hr : ∀ x : M, D (r₀ x) = 0 := by
    intro x
    change D (x - s (D.rangeRestrict x)) = 0
    rw [map_sub]
    have he := congrArg (fun f : LinearMap.range D →ₗ[ℤ] LinearMap.range D =>
      (f (D.rangeRestrict x)).val) hs
    change D (s (D.rangeRestrict x)) = D x at he
    rw [he, sub_self]
  let r : M →ₗ[ℤ] M.ρ.invariants := r₀.codRestrict _ (fun x g => by
    have he := congrFun (hr x) g
    change M.ρ g (r₀ x) - r₀ x = 0 at he
    exact sub_eq_zero.mp he)
  refine ⟨r, fun x => ?_⟩
  apply Subtype.ext
  have hx : D.rangeRestrict x = 0 := by
    apply Subtype.ext
    funext g
    change M.ρ g x - x = 0
    exact sub_eq_zero.mpr (x.property g)
  change x.val - s (D.rangeRestrict x) = x.val
  rw [hx, map_zero, sub_zero]

/-- Every integral functional on the original invariant lattice extends to the original lattice. -/
theorem originalInvariant_linear_extension_exists (f : M.ρ.invariants →ₗ[ℤ] ℤ) :
    ∃ η : M →ₗ[ℤ] ℤ, ∀ x : M.ρ.invariants, η x = f x := by
  obtain ⟨r, hr⟩ := originalInvariant_linear_retraction_exists M
  exact ⟨f.comp r, fun x => congrArg f (hr x)⟩

end
end Dubon2026
