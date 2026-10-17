import Dubon2026.OriginalFiniteRelationModule
import Dubon2026.OriginalCoinducedInvariantAcyclicity
import Dubon2026.OriginalCoinducedSubgroupAcyclicity
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # Cohomology of the genuine finite free relation cover

Identify the actual free cover with original coinduced functions by
inverting the group coordinate. Reuse the existing subgroup coboundaries
and Shapiro theorem. This proves the relation connecting isomorphism
needed by DUB-17's finite class/Ext criterion without adding an acyclicity
certificate or reproving a general Tate-cohomology framework.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Finite G] (B : Rep ℤ G) [Finite B]

/-- The original finite free cover is the actual coinduced function representation, with the inverse group coordinate accounting for the right-translation action. -/
def originalRelationFreeCoinducedIso :
    Rep.free ℤ G B ≅ originalCoinducedFunctionRep (Rep.trivial ℤ G (B → ℤ)) :=
  Rep.mkIso {
    toFun := fun f => originalCoinducedFunction _ (fun g b => f b g⁻¹)
    invFun := fun f => Finsupp.equivFunOnFinite.symm
      (fun b => Finsupp.equivFunOnFinite.symm (fun g => f.val g⁻¹ b))
    left_inv f := by
      ext b g
      simp [originalCoinducedFunction]
    right_inv f := by
      apply Subtype.ext
      funext g b
      simp [originalCoinducedFunction]
    map_add' f h := by
      apply Subtype.ext
      rfl
    map_smul' r f := by
      apply Subtype.ext
      rfl
    isIntertwining' h := by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext g b
      change ((Representation.free ℤ G B h) f) b g⁻¹ = f b (g * h)⁻¹
      simp [Representation.free, Representation.finsupp_apply,
        Representation.leftRegular, Representation.ofMulAction, Finsupp.lsum_apply,
        mul_inv_rev]
      rw [Finsupp.sum_eq_single b]
      · rw [Finsupp.single_eq_same]
        exact Finsupp.mapDomain_equiv_apply (f := Equiv.mulLeft h) (f b) g⁻¹
      · intro c _ hcb
        simp [hcb]
      · intro _
        simp }

/-- The original finite free relation cover has zero positive group cohomology. -/
theorem originalRelationFreeCover_positive_zero (n : ℕ) :
    Limits.IsZero (groupCohomology (Rep.free ℤ G B) (n + 1)) :=
  (originalCoinducedFunction_positive_zero (Rep.trivial ℤ G (B → ℤ)) n).of_iso
    ((groupCohomology.functor ℤ G (n + 1)).mapIso (originalRelationFreeCoinducedIso B))

/-- Every actual subgroup has vanishing first and second cohomology of the original finite free cover. -/
theorem originalRelationFreeCover_subgroup_first_second_zero (S : Subgroup G) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.free ℤ G B)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.free ℤ G B)) 2) := by
  let e := (Rep.resFunctor S.subtype).mapIso (originalRelationFreeCoinducedIso B)
  exact ⟨(originalCoinducedSubgroup_first_zero (Rep.trivial ℤ G (B → ℤ)) S).of_iso
      ((groupCohomology.functor ℤ S 1).mapIso e),
    (originalCoinducedSubgroup_second_zero (Rep.trivial ℤ G (B → ℤ)) S).of_iso
      ((groupCohomology.functor ℤ S 2).mapIso e)⟩

/-- The genuine connecting map identifies H1 of the original finite coefficient with H2 of its actual integral relation module. -/
theorem originalRelationConnecting_isIso :
    IsIso (groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl) :=
  groupCohomology.isIso_δ_of_isZero (originalRelationShortComplex_shortExact B) 1
    (originalRelationFreeCover_positive_zero B 0) (originalRelationFreeCover_positive_zero B 1)

end
end Dubon2026
