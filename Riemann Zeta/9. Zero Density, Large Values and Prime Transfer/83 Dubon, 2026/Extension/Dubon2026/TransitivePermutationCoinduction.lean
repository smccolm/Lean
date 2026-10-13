import Dubon2026.PermutationCoordinateRepresentation
import Mathlib.GroupTheory.GroupAction.Transitive

/-! # Original transitive permutation coordinates and stabilizer coinduction

Functions on the actual transitive orbit are identified with the existing
coinduction from its actual stabilizer. Inverse orbit coordinates match
the original action conventions. This permits the existing Shapiro
isomorphism to compute DUB-17's permutation-lattice cohomology.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  [MulAction.IsPretransitive G ι] (i : ι)

private theorem inverseOrbit_surjective : Function.Surjective (fun g : G => g⁻¹ • i) := by
  intro j
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G i j
  exact ⟨g⁻¹, by simpa using hg⟩

omit [MulAction.IsPretransitive G ι] in
private theorem stabilizerCoind_fiber
    (f : Rep.coind (MulAction.stabilizer G i).subtype
      (Rep.trivial R (MulAction.stabilizer G i) R))
    (g h : G) (he : g⁻¹ • i = h⁻¹ • i) : f.val g = f.val h := by
  have hs : g * h⁻¹ ∈ MulAction.stabilizer G i := by
    change (g * h⁻¹) • i = i
    simpa only [mul_smul, smul_inv_smul] using (congrArg (fun j => g • j) he).symm
  have hf := f.property ⟨g * h⁻¹, hs⟩ h
  simpa only [Subgroup.coe_mk, Subgroup.subtype_apply, inv_mul_cancel_right] using hf

/-- The actual inverse orbit-coordinate equivalence with the original stabilizer coinduction. -/
def transitivePermutationCoindLinearEquiv :
    (ι → R) ≃ₗ[R] Rep.coind (MulAction.stabilizer G i).subtype
      (Rep.trivial R (MulAction.stabilizer G i) R) where
  toFun x := ⟨fun g => x (g⁻¹ • i), by
    intro h g
    change x (((h : G) * g)⁻¹ • i) = x (g⁻¹ • i)
    rw [mul_inv_rev, mul_smul]
    have hh : (h : G)⁻¹ • i = i := (MulAction.stabilizer G i).inv_mem h.property
    rw [hh]⟩
  invFun f j := f.val (Function.surjInv (inverseOrbit_surjective G ι i) j)
  left_inv x := by
    funext j
    exact congrArg x (Function.surjInv_eq (inverseOrbit_surjective G ι i) j)
  right_inv f := by
    apply Subtype.ext
    funext g
    exact stabilizerCoind_fiber R G ι i f _ g
      (Function.surjInv_eq (inverseOrbit_surjective G ι i) (g⁻¹ • i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual transitive coordinate representation is isomorphic to coinduction from the actual orbit stabilizer. -/
def transitivePermutationCoindIso :
    permutationCoordinateRep R G ι ≅ Rep.coind (MulAction.stabilizer G i).subtype
      (Rep.trivial R (MulAction.stabilizer G i) R) := by
  apply Rep.mkIso
  refine Representation.Equiv.mk (transitivePermutationCoindLinearEquiv R G ι i) ?_
  intro g
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext h
  change x (g⁻¹ • h⁻¹ • i) = x ((h * g)⁻¹ • i)
  rw [mul_inv_rev, mul_smul]

/-- Existing Shapiro identifies the original transitive permutation cohomology with actual stabilizer integer cohomology. -/
def transitivePermutationCohomologyIso (n : ℕ) :
    groupCohomology (permutationCoordinateRep R G ι) n ≅
      groupCohomology (Rep.trivial R (MulAction.stabilizer G i) R) n :=
  (groupCohomology.functor R G n).mapIso (transitivePermutationCoindIso R G ι i) ≪≫
    groupCohomology.coindIso (Rep.trivial R (MulAction.stabilizer G i) R) n

/-- The representation isomorphism evaluates at the original inverse orbit coordinate. -/
theorem transitivePermutationCoindIso_hom_apply (x : ι → R) (g : G) :
    ((transitivePermutationCoindIso R G ι i).hom.hom x).val g = x (g⁻¹ • i) := rfl

end
end Dubon2026
