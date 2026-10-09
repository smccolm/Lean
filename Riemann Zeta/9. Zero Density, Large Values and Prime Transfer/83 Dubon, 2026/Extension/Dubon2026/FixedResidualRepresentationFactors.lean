import Dubon2026.FixedResidualProPKernel
import Dubon2026.ProfiniteProPKernelFactors

/-! # One original residual quotient factors every actual continuous lift into a pro-p residual target -/

namespace Dubon2026

noncomputable section

/-- The actual fixed residual common kernel has the previously proved ambient normality instance. -/
instance fixedResidualProPKernelNormal (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    [K.Normal] (hK : IsClosed (K : Set G)) :
    (fixedResidualProPKernel p G K hK).Normal :=
  fixedResidualProPKernel_normal p G K hK

/-- Every original continuous representation carrying its original residual subgroup into the actual pro-p residual target kills the same fixed ambient kernel. -/
theorem fixedResidualProPKernel_le_representation_kernel
    (p : ℕ) (G H : ProfiniteGrp) (K : Subgroup G) (hK : IsClosed (K : Set G))
    (L : Subgroup H) (hL : IsClosed (L : Set H))
    (hP : profiniteProPKernel p (closedSubgroupProfinite H L hL) = ⊥)
    (f : G →* H) (hf : Continuous f) (hres : ∀ g ∈ K, f g ∈ L) :
    fixedResidualProPKernel p G K hK ≤ f.ker := by
  let restricted : K →* L :=
    (f.comp K.subtype).codRestrict L (fun g => hres g.val g.property)
  have hr : Continuous restricted :=
    (hf.comp continuous_subtype_val).subtype_mk _
  have hkill := profiniteProPKernel_le_kernel_of_target_separation p
    (closedSubgroupProfinite G K hK) (closedSubgroupProfinite H L hL) restricted hr hP
  rintro _ ⟨g, hg, rfl⟩
  exact congrArg Subtype.val (hkill hg)

/-- The original entire representation descends through a single quotient fixed by its original residual subgroup. -/
def fixedResidualRepresentationFactor
    (p : ℕ) (G H : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G))
    (L : Subgroup H) (hL : IsClosed (L : Set H))
    (hP : profiniteProPKernel p (closedSubgroupProfinite H L hL) = ⊥)
    (f : G →* H) (hf : Continuous f) (hres : ∀ g ∈ K, f g ∈ L) :
    G ⧸ fixedResidualProPKernel p G K hK →* H :=
  QuotientGroup.lift (fixedResidualProPKernel p G K hK) f
    (fixedResidualProPKernel_le_representation_kernel p G H K hK L hL hP f hf hres)

/-- Every original matrix or representation value is preserved by the genuine fixed residual factor. -/
theorem fixedResidualRepresentationFactor_mk
    (p : ℕ) (G H : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G))
    (L : Subgroup H) (hL : IsClosed (L : Set H))
    (hP : profiniteProPKernel p (closedSubgroupProfinite H L hL) = ⊥)
    (f : G →* H) (hf : Continuous f) (hres : ∀ g ∈ K, f g ∈ L) (g : G) :
    fixedResidualRepresentationFactor p G H K hK L hL hP f hf hres
      (QuotientGroup.mk' (fixedResidualProPKernel p G K hK) g) = f g := rfl

/-- The original fixed residual factor is continuous in the literal ambient quotient topology. -/
theorem fixedResidualRepresentationFactor_continuous
    (p : ℕ) (G H : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G))
    (L : Subgroup H) (hL : IsClosed (L : Set H))
    (hP : profiniteProPKernel p (closedSubgroupProfinite H L hL) = ⊥)
    (f : G →* H) (hf : Continuous f) (hres : ∀ g ∈ K, f g ∈ L) :
    Continuous (fixedResidualRepresentationFactor p G H K hK L hL hP f hf hres) := by
  apply (QuotientGroup.isQuotientMap_mk (fixedResidualProPKernel p G K hK)).continuous_iff.mpr
  exact hf

end
end Dubon2026
