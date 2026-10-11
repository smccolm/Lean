import Dubon2026.FiniteActionUnitNorm
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # The actual action and first cohomology of an invariant unit subgroup -/

namespace Dubon2026
noncomputable section

open CategoryTheory
open scoped BigOperators

variable (G U : Type) [Group G] [CommGroup U] [MulDistribMulAction G U]
  (S : Subgroup U) (hS : ∀ (g : G) (u : U), u ∈ S → g • u ∈ S)

/-- Restrict the original action to the same invariant subgroup. -/
@[reducible]
def stableSubgroupMulDistribMulAction : MulDistribMulAction G S where
  smul g u := ⟨g • (u : U), hS g u u.property⟩
  one_smul u := Subtype.ext (one_smul G (u : U))
  mul_smul g h u := Subtype.ext (mul_smul g h (u : U))
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g u v := Subtype.ext (smul_mul' g (u : U) (v : U))

/-- The subgroup representation norm is exactly the original finite action
product after the literal coefficient inclusion. -/
theorem stableSubgroup_norm_coe [Fintype G] (v : S) :
    letI := stableSubgroupMulDistribMulAction G U S hS
    ((finiteActionUnitNorm G S v : S) : U) = finiteActionUnitNorm G U (v : U) := by
  letI := stableSubgroupMulDistribMulAction G U S hS
  change S.subtype (∏ g : G, g • v) = ∏ g : G, g • (v : U)
  rw [map_prod]
  rfl

/-- Literal original coboundary preimages identify the actual first group
cohomology as zero through Mathlib's cochain quotient map. -/
theorem stableSubgroup_firstCohomology_zero
    (hcob : ∀ c : G → U,
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S) →
        ∃ v : U, v ∈ S ∧ ∀ g, (g • v) / v = c g) :
    letI := stableSubgroupMulDistribMulAction G U S hS
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G S) 1) := by
  letI := stableSubgroupMulDistribMulAction G U S hS
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  refine groupCohomology.H1_induction_on x (fun c => ?_)
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  have hc := groupCohomology.isMulCocycle₁_of_mem_cocycles₁ (G := G) (M := S)
    (fun g => Additive.toMul (c.1 g)) c.2
  obtain ⟨v, hv, hvc⟩ := hcob
    (fun g => ((Additive.toMul (c.1 g) : S) : U))
    (fun g h => congrArg (fun z : S => (z : U)) (hc g h))
    (fun g => (Additive.toMul (c.1 g) : S).property)
  exact (groupCohomology.coboundariesOfIsMulCoboundary₁
    (G := G) (M := S)
    (f := fun g => Additive.toMul (c.1 g))
    ⟨⟨v, hv⟩, fun g => Subtype.ext (hvc g)⟩).property

/-- Original norm preimages become preimages under the norm of the actual
additive subgroup representation, with the same original representatives. -/
theorem stableSubgroup_repNorm_preimages [Fintype G]
    (hnorm : ∀ u : U, u ∈ S → (∀ g : G, g • u = u) →
      ∃ v : U, v ∈ S ∧ finiteActionUnitNorm G U v = u) :
    letI := stableSubgroupMulDistribMulAction G U S hS
    ∀ x : Rep.ofMulDistribMulAction G S,
      x ∈ (Rep.ofMulDistribMulAction G S).ρ.invariants →
        ∃ y : Rep.ofMulDistribMulAction G S,
          (Rep.ofMulDistribMulAction G S).norm.hom y = x := by
  letI := stableSubgroupMulDistribMulAction G U S hS
  intro x hx
  have hinv : ∀ g : G, g • ((Additive.toMul x : S) : U) =
      ((Additive.toMul x : S) : U) := by
    intro g
    exact congrArg (fun z : Additive S => ((Additive.toMul z : S) : U)) (hx g)
  obtain ⟨v, hv, hn⟩ := hnorm (Additive.toMul x : S) (Additive.toMul x).property hinv
  refine ⟨Additive.ofMul (⟨v, hv⟩ : S), ?_⟩
  change (Rep.ofMulDistribMulAction G S).ρ.norm (Additive.ofMul (⟨v, hv⟩ : S)) = x
  simp only [Representation.norm, LinearMap.sum_apply, Rep.ofMulDistribMulAction_ρ_apply_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((Additive.toMul (∑ g : G, Additive.ofMul (g • (⟨v, hv⟩ : S))) : S) : U) = _
  rw [toMul_sum]
  change ((finiteActionUnitNorm G S (⟨v, hv⟩ : S) : S) : U) = _
  rw [stableSubgroup_norm_coe G U S hS]
  exact hn

end
end Dubon2026
