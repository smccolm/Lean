import Dubon2026.FixedResidualRepresentationFactors

/-! # The actual residual subgroup inside the genuine fixed ambient quotient -/

namespace Dubon2026

noncomputable section

/-- The genuine common kernel is normal in the original closed subgroup with its original group structure. -/
instance closedSubgroupProPKernelNormal (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    (hK : IsClosed (K : Set G)) :
    (profiniteProPKernel p (closedSubgroupProfinite G K hK) : Subgroup K).Normal :=
  profiniteProPKernelNormal p (closedSubgroupProfinite G K hK)

/-- The original residual subgroup viewed inside the actual quotient by its fixed common kernel. -/
abbrev FixedResidualQuotientSubgroup (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    [K.Normal] (hK : IsClosed (K : Set G)) :=
  K.map (QuotientGroup.mk' (fixedResidualProPKernel p G K hK))

/-- The original residual subgroup maps to its genuine image in the fixed ambient quotient. -/
def fixedResidualQuotientRestriction (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    [K.Normal] (hK : IsClosed (K : Set G)) : K →* FixedResidualQuotientSubgroup p G K hK :=
  ((QuotientGroup.mk' (fixedResidualProPKernel p G K hK)).comp K.subtype).codRestrict _
    (fun k => Subgroup.mem_map.mpr ⟨k.val, k.property, rfl⟩)

/-- The original common kernel of the residual subgroup is killed by the actual restricted ambient projection. -/
theorem fixedResidualQuotientRestriction_kernel_le
    (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G)) :
    profiniteProPKernel p (closedSubgroupProfinite G K hK) ≤
      (fixedResidualQuotientRestriction p G K hK).ker := by
  intro k hk
  apply Subtype.ext
  change QuotientGroup.mk' (fixedResidualProPKernel p G K hK) k.val = 1
  apply (QuotientGroup.eq_one_iff k.val).mpr
  exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩

/-- The genuine pro-p quotient of the original residual subgroup maps onto its actual image in the ambient fixed quotient. -/
def fixedResidualQuotientSubgroupFactor (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    [K.Normal] (hK : IsClosed (K : Set G)) :
    K ⧸ profiniteProPKernel p (closedSubgroupProfinite G K hK) →*
      FixedResidualQuotientSubgroup p G K hK := by
  let N : Subgroup K := profiniteProPKernel p (closedSubgroupProfinite G K hK)
  letI : N.Normal := closedSubgroupProPKernelNormal p G K hK
  exact QuotientGroup.lift (G := K) N (fixedResidualQuotientRestriction p G K hK)
    (fixedResidualQuotientRestriction_kernel_le p G K hK)

/-- The actual residual quotient map is surjective onto the entire original residual image. -/
theorem fixedResidualQuotientSubgroupFactor_surjective
    (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G)) :
    Function.Surjective (fixedResidualQuotientSubgroupFactor p G K hK) := by
  intro x
  obtain ⟨k, hk, heq⟩ := x.property
  refine ⟨QuotientGroup.mk'
    (profiniteProPKernel p (closedSubgroupProfinite G K hK)) (⟨k, hk⟩ : K), ?_⟩
  exact Subtype.ext heq

/-- The original residual quotient map is continuous in the genuine source quotient and target subgroup topologies. -/
theorem fixedResidualQuotientSubgroupFactor_continuous
    (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G)) :
    Continuous (fixedResidualQuotientSubgroupFactor p G K hK) := by
  apply (QuotientGroup.isQuotientMap_mk
    (profiniteProPKernel p (closedSubgroupProfinite G K hK))).continuous_iff.mpr
  exact ((QuotientGroup.continuous_mk : Continuous
    (QuotientGroup.mk' (fixedResidualProPKernel p G K hK))).comp
      (continuous_subtype_val : Continuous (K.subtype : K → G))).subtype_mk _

/-- The original finite residual quotient remains the genuine quotient of the fixed ambient group by its actual residual image. -/
theorem fixedResidualQuotientSubgroup_finite_quotient
    (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    [Finite (G ⧸ K)] (hK : IsClosed (K : Set G)) :
    Finite ((G ⧸ fixedResidualProPKernel p G K hK) ⧸
      FixedResidualQuotientSubgroup p G K hK) := by
  let e := QuotientGroup.quotientQuotientEquivQuotient
    (fixedResidualProPKernel p G K hK) K (fixedResidualProPKernel_le p G K hK)
  exact Finite.of_equiv (G ⧸ K) e.toEquiv.symm

end
end Dubon2026
