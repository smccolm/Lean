import Dubon2026.ProfiniteProPQuotientTopology
import Dubon2026.ProfiniteProPKernelFunctoriality

/-! # The original fixed residual common kernel is normal in its ambient profinite group -/

namespace Dubon2026

noncomputable section

/-- An original closed subgroup carries its actual inherited profinite topology. -/
def closedSubgroupProfinite (G : ProfiniteGrp) (K : Subgroup G)
    (hK : IsClosed (K : Set G)) : ProfiniteGrp := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  exact ProfiniteGrp.of K

/-- The actual common p-quotient kernel of the original closed residual subgroup, viewed inside its ambient group. -/
def fixedResidualProPKernel (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    (hK : IsClosed (K : Set G)) : Subgroup G :=
  (profiniteProPKernel p (closedSubgroupProfinite G K hK)).map K.subtype

/-- The original fixed residual common kernel lies inside the original residual subgroup. -/
theorem fixedResidualProPKernel_le (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    (hK : IsClosed (K : Set G)) : fixedResidualProPKernel p G K hK ≤ K := by
  rintro _ ⟨k, _, rfl⟩
  exact k.property

/-- Continuous ambient conjugation makes the genuine common p-quotient kernel normal in the original entire group. -/
theorem fixedResidualProPKernel_normal (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    [K.Normal] (hK : IsClosed (K : Set G)) :
    (fixedResidualProPKernel p G K hK).Normal := by
  constructor
  rintro _ ⟨k, hk, rfl⟩ g
  let c : K →* K := {
    toFun := fun x => ⟨g * x.val * g⁻¹, Subgroup.Normal.conj_mem inferInstance x.val x.property g⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hc : Continuous c :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hmap := profiniteProPKernel_map_le p (closedSubgroupProfinite G K hK)
    (closedSubgroupProfinite G K hK) c hc
  refine ⟨c k, hmap ?_, rfl⟩
  exact ⟨k, hk, rfl⟩

/-- The fixed common kernel is closed in the original ambient profinite group. -/
theorem fixedResidualProPKernel_isClosed (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    (hK : IsClosed (K : Set G)) : IsClosed (fixedResidualProPKernel p G K hK : Set G) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  exact ((profiniteProPKernel_isClosed p (closedSubgroupProfinite G K hK)).isCompact.image
    continuous_subtype_val).isClosed

end
end Dubon2026
