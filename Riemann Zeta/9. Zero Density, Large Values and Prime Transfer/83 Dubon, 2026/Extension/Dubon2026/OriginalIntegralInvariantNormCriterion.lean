import Dubon2026.OriginalInvariantLinearExtension
import Dubon2026.OriginalNormQuotientCohomology

/-! # Actual degree-zero integral norm detection

For the two-coinduced-shift route to DUB-17's converse norm criterion,
an equivariant functional into the original trivial integers is a
literal sum of conjugates if its values on the original invariant
lattice are divisible by the group order. The division and integral
extension are constructed, not supplied as certificates.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2 Submodule.module
variable {G : Type} [Group G] (M : Rep.{0} ℤ G)
variable [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]

/-- A divisible functional on the actual invariant lattice has an integral divided extension. -/
theorem originalIntegralInvariant_divided_extension
    (n : ℤ) (hn : n ≠ 0) (f : M.ρ.invariants →ₗ[ℤ] ℤ)
    (hf : ∀ x : M.ρ.invariants, n ∣ f x) :
    ∃ η : M →ₗ[ℤ] ℤ, ∀ x : M.ρ.invariants, n * η x = f x := by
  let L : ℤ →ₗ[ℤ] ℤ := n • LinearMap.id
  have hL : Function.Injective L := fun a b hab => mul_left_cancel₀ hn hab
  let e := LinearEquiv.ofInjective L hL
  let f₀ : M.ρ.invariants →ₗ[ℤ] LinearMap.range L := f.codRestrict _ (fun x => by
    obtain ⟨a, ha⟩ := hf x
    exact ⟨a, ha.symm⟩)
  let f₁ : M.ρ.invariants →ₗ[ℤ] ℤ := e.symm.toLinearMap.comp f₀
  obtain ⟨η, hη⟩ := originalInvariant_linear_extension_exists M f₁
  refine ⟨η, fun x => ?_⟩
  rw [hη]
  exact congrArg Subtype.val (e.apply_symm_apply (f₀ x))

variable [Fintype G]

/-- Group-order divisibility on the original invariant lattice produces a literal original coefficient norm witness. -/
theorem originalIntegralInvariant_norm_of_divisibility
    (f : M ⟶ Rep.trivial ℤ G ℤ)
    (hf : ∀ x : M.ρ.invariants, (Fintype.card G : ℤ) ∣ f.hom x) :
    ∃ η : M →ₗ[ℤ] ℤ,
      originalCoefficientNormMorphism M (Rep.trivial ℤ G ℤ) η = f := by
  have hn : (Fintype.card G : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨η, hη⟩ := originalIntegralInvariant_divided_extension M (Fintype.card G) hn
    (f.hom.toLinearMap.comp M.ρ.invariants.subtype) hf
  refine ⟨η, Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))⟩
  change (originalCoefficientNormMorphism M (Rep.trivial ℤ G ℤ) η).hom x = f.hom x
  rw [originalCoefficientNormMorphism_apply]
  change (∑ g : G, η (M.ρ g⁻¹ x)) = f.hom x
  have hsum : (∑ g : G, η (M.ρ g⁻¹ x)) = η (M.ρ.norm x) := by
    simp only [Representation.norm, LinearMap.sum_apply, map_sum]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)
  rw [hsum]
  apply mul_left_cancel₀ hn
  have he := hη ⟨M.ρ.norm x, fun g => M.ρ.self_norm_apply g x⟩
  change (Fintype.card G : ℤ) * η (M.ρ.norm x) = f.hom (M.ρ.norm x) at he
  refine he.trans ?_
  rw [originalCoefficientMorphism_norm]
  change (∑ g : G, (Rep.trivial ℤ G ℤ).ρ g) (f.hom x) = _
  rw [LinearMap.sum_apply]
  change (∑ _ : G, f.hom x) = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end
end Dubon2026
