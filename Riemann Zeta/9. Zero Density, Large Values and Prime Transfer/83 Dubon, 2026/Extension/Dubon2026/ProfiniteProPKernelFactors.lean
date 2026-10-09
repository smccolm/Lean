import Dubon2026.ProfiniteProPKernelFunctoriality

/-! # Actual continuous maps to separated pro-p targets kill the original common kernel -/

namespace Dubon2026

noncomputable section

/-- Continuous functoriality and actual target separation force the original common kernel into the original map kernel. -/
theorem profiniteProPKernel_le_kernel_of_target_separation
    (p : ℕ) (G H : ProfiniteGrp) (f : G →* H) (hf : Continuous f)
    (hH : profiniteProPKernel p H = ⊥) : profiniteProPKernel p G ≤ f.ker := by
  intro g hg
  have hfg := profiniteProPKernel_map_le p G H f hf (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  simpa only [hH, Subgroup.mem_bot] using hfg

/-- The original continuous map into a genuinely separated pro-p target descends through the fixed original quotient. -/
def profiniteProPContinuousFactor
    (p : ℕ) (G H : ProfiniteGrp) (f : G →* H) (hf : Continuous f)
    (hH : profiniteProPKernel p H = ⊥) : G ⧸ profiniteProPKernel p G →* H :=
  QuotientGroup.lift (profiniteProPKernel p G) f
    (profiniteProPKernel_le_kernel_of_target_separation p G H f hf hH)

/-- The genuine continuous factor preserves every original value. -/
theorem profiniteProPContinuousFactor_mk
    (p : ℕ) (G H : ProfiniteGrp) (f : G →* H) (hf : Continuous f)
    (hH : profiniteProPKernel p H = ⊥) (g : G) :
    profiniteProPContinuousFactor p G H f hf hH
      (QuotientGroup.mk' (profiniteProPKernel p G) g) = f g := rfl

/-- The actual descended map is continuous for the genuine original quotient topology. -/
theorem profiniteProPContinuousFactor_continuous
    (p : ℕ) (G H : ProfiniteGrp) (f : G →* H) (hf : Continuous f)
    (hH : profiniteProPKernel p H = ⊥) :
    Continuous (profiniteProPContinuousFactor p G H f hf hH) := by
  apply (QuotientGroup.isQuotientMap_mk (profiniteProPKernel p G)).continuous_iff.mpr
  exact hf

end
end Dubon2026
