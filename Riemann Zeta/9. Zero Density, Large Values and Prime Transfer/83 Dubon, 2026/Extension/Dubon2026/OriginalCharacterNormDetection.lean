import Dubon2026.OriginalCoefficientNormCohomology
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Character detection of the original norm kernel

The degree-zero character-duality step on DUB-17's finite class/Ext route
is the annihilator identity for the literal representation norm. Pinned
injectivity of the divisible rational circle extends a functional from
the actual norm image. The resulting witness is the source's exact sum
of inverse translates. Higher-degree duality and compatibility with the
fundamental class are still separate obligations.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2

/-- A functional into an injective coefficient factors through a linear map when it annihilates its kernel. -/
theorem originalInjectiveCharacter_factor
    {k V W Q : Type} [Ring k] [AddCommGroup V] [AddCommGroup W] [AddCommGroup Q]
    [Module k V] [Module k W] [Module k Q] [Module.Injective k Q]
    (N : V →ₗ[k] W) (φ : V →ₗ[k] Q) (hφ : ∀ x, N x = 0 → φ x = 0) :
    ∃ η : W →ₗ[k] Q, ∀ x, η (N x) = φ x := by
  let q : V ⧸ LinearMap.ker N →ₗ[k] Q :=
    (LinearMap.ker N).liftQ φ (fun x hx => hφ x hx)
  let f : LinearMap.range N →ₗ[k] Q :=
    q ∘ₗ N.quotKerEquivRange.symm.toLinearMap
  obtain ⟨η, hη⟩ := Module.Injective.out (LinearMap.range N).subtype Subtype.val_injective f
  refine ⟨η, fun x => ?_⟩
  have he := hη ⟨N x, ⟨x, rfl⟩⟩
  change η (N x) = q (N.quotKerEquivRange.symm ⟨N x, ⟨x, rfl⟩⟩) at he
  rw [LinearMap.quotKerEquivRange_symm_apply_image] at he
  exact he

/-- A rational-circle character annihilates the literal norm kernel exactly when it is a sum of inverse translates of another original integral character. -/
theorem originalCharacter_norm_kernel_iff_sum
    {G : Type} [Group G] [Fintype G] (M : Rep.{0} ℤ G)
    (φ : M →ₗ[ℤ] AddCircle (1 : ℚ)) :
    (∀ x : M, M.ρ.norm x = 0 → φ x = 0) ↔
      ∃ η : M →ₗ[ℤ] AddCircle (1 : ℚ),
        ∀ x : M, φ x = ∑ g : G, η (M.ρ g⁻¹ x) := by
  have hs (η : M →ₗ[ℤ] AddCircle (1 : ℚ)) (x : M) :
      η (M.ρ.norm x) = ∑ g : G, η (M.ρ g⁻¹ x) := by
    simp only [Representation.norm, LinearMap.sum_apply, map_sum]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by
      change η (M.ρ g x) = η (M.ρ g⁻¹⁻¹ x)
      rw [inv_inv])
  constructor
  · intro hφ
    letI : Module.Injective ℤ (AddCircle (1 : ℚ)) :=
      (Module.Baer.of_divisible (AddCircle (1 : ℚ))).injective
    obtain ⟨η, hη⟩ := originalInjectiveCharacter_factor M.ρ.norm φ hφ
    exact ⟨η, fun x => (hη x).symm.trans (hs η x)⟩
  · rintro ⟨η, hη⟩ x hx
    rw [hη, ← hs, hx, map_zero]

end
end Dubon2026
