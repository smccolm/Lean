import Dubon2026.ProfiniteProPKernelDiscreteMaps

/-! # Functoriality of the original finite p-quotient common kernel -/

namespace Dubon2026

noncomputable section

/-- Every original continuous profinite group map preserves the genuine common kernels of finite p-group quotients. -/
theorem profiniteProPKernel_map_le (p : ℕ) (G H : ProfiniteGrp)
    (f : G →* H) (hf : Continuous f) :
    (profiniteProPKernel p G).map f ≤ profiniteProPKernel p H := by
  rintro _ ⟨g, hg, rfl⟩
  apply (profiniteProPKernel_mem_iff p H (f g)).mpr
  intro U hU
  let q : H →* H ⧸ U.toSubgroup := QuotientGroup.mk' U.toSubgroup
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hk := profiniteProPKernel_le_discrete_kernel p G (q.comp f) (hq.comp hf) hU
  have hfg : q (f g) = 1 := hk hg
  exact (QuotientGroup.eq_one_iff (f g)).mp hfg

end
end Dubon2026
