import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Equal genuine Gram matrices induce an isometry on the actual algebraic spans -/

namespace Dubon2026

noncomputable section

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Equality of the original pairwise Gram entries gives equality for all actual finite linear combinations. -/
theorem gramFamily_linearCombination_inner (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) (a b : ι →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ u a) (Finsupp.linearCombination ℂ u b) =
      inner ℂ (Finsupp.linearCombination ℂ v a) (Finsupp.linearCombination ℂ v b) := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

/-- The original Gram identity proves every actual linear relation in the first family is also a relation in the second. -/
theorem gramFamily_linearCombination_ker_le (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) :
    (Finsupp.linearCombination ℂ u).ker ≤ (Finsupp.linearCombination ℂ v).ker := by
  intro a ha
  change Finsupp.linearCombination ℂ v a = 0
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← gramFamily_linearCombination_inner u v h a a]
  change Finsupp.linearCombination ℂ u a = 0 at ha
  rw [ha, inner_zero_left]

/-- The genuine relation-preserving map between the original algebraic spans, constructed by the actual quotient by linear relations. -/
def gramFamilyRangeMap (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) :
    (Finsupp.linearCombination ℂ u).range →ₗ[ℂ] F :=
  ((Finsupp.linearCombination ℂ u).ker.liftQ (Finsupp.linearCombination ℂ v)
    (gramFamily_linearCombination_ker_le u v h)).comp
      (Finsupp.linearCombination ℂ u).quotKerEquivRange.symm.toLinearMap

/-- The actual quotient construction sends each original finite linear combination to precisely the corresponding second-family combination. -/
theorem gramFamilyRangeMap_linearCombination (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) (a : ι →₀ ℂ)
    (ha : Finsupp.linearCombination ℂ u a ∈ (Finsupp.linearCombination ℂ u).range) :
    gramFamilyRangeMap u v h ⟨Finsupp.linearCombination ℂ u a, ha⟩ =
      Finsupp.linearCombination ℂ v a := by
  simp only [gramFamilyRangeMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- The actual relation-quotient map preserves every original inner product, not only individual generator norms. -/
theorem gramFamilyRangeMap_inner (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j))
    (x y : (Finsupp.linearCombination ℂ u).range) :
    inner ℂ (gramFamilyRangeMap u v h x) (gramFamilyRangeMap u v h y) = inner ℂ x y := by
  obtain ⟨x, a, rfl⟩ := x
  obtain ⟨y, b, rfl⟩ := y
  rw [gramFamilyRangeMap_linearCombination, gramFamilyRangeMap_linearCombination]
  exact (gramFamily_linearCombination_inner u v h a b).symm

/-- A faithful actual linear isometry between original family spans follows from their proved genuine Gram identity. -/
def gramFamilyRangeIsometry (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) :
    (Finsupp.linearCombination ℂ u).range →ₗᵢ[ℂ] F :=
  (gramFamilyRangeMap u v h).isometryOfInner (gramFamilyRangeMap_inner u v h)

end
end Dubon2026
