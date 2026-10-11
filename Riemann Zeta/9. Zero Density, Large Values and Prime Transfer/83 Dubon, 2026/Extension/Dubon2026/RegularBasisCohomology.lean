import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Genuine cohomology vanishing from an original regularly permuted basis -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {R G : Type} [CommRing R] [Group G] [Fintype G]
  (A : Rep.{0} R G) (b : Module.Basis G R A)

private def regularBasisCoindLinearEquiv :
    A ≃ₗ[R] Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial R (⊥ : Subgroup G) R) where
  toFun x := ⟨fun h => b.repr x h⁻¹, by
    intro g h
    have hg : (g : G) = 1 := g.property
    simp [hg]⟩
  invFun f := b.equivFun.symm (fun g => f.val g⁻¹)
  left_inv x := by
    apply b.equivFun.injective
    ext g
    simp [Module.Basis.equivFun_apply]
  right_inv f := by
    apply Subtype.ext
    funext h
    simpa only [Module.Basis.equivFun_apply, inv_inv] using
      congrFun (b.equivFun.apply_symm_apply (fun g => f.val g⁻¹)) h⁻¹
  map_add' x y := by
    apply Subtype.ext
    funext h
    simp
  map_smul' a x := by
    apply Subtype.ext
    funext h
    simp

/-- The original displayed basis, regularly permuted by the original action,
gives an actual isomorphism with coinduction from the trivial subgroup.
Inversion of the basis index matches the two original action conventions. -/
def regularBasisCoindIso (hb : ∀ g h, A.ρ g (b h) = b (g * h)) :
    A ≅ Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial R (⊥ : Subgroup G) R) := by
  classical
  apply Rep.mkIso
  refine Representation.Equiv.mk (regularBasisCoindLinearEquiv A b) ?_
  intro g
  apply b.ext
  intro h
  apply Subtype.ext
  funext k
  change b.repr (A.ρ g (b h)) k⁻¹ = b.repr (b h) (k * g)⁻¹
  rw [hb]
  have he : g * h = k⁻¹ ↔ h = (k * g)⁻¹ := by
    rw [mul_inv_rev, eq_inv_mul_iff_mul_eq]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, he]

/-- Shapiro's actual cohomology isomorphism and vanishing for the trivial
subgroup prove every positive cohomology group of the original representation
is zero when its displayed basis is regularly permuted. -/
theorem regularBasis_groupCohomology_isZero
    (hb : ∀ g h, A.ρ g (b h) = b (g * h)) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) := by
  have h := isZero_groupCohomology_succ_of_subsingleton
    (Rep.trivial R (⊥ : Subgroup G) R) n
  exact h.of_iso (((groupCohomology.functor R G (n + 1)).mapIso
    (regularBasisCoindIso A b hb)) ≪≫
      groupCohomology.coindIso (Rep.trivial R (⊥ : Subgroup G) R) (n + 1))

end
end Dubon2026
