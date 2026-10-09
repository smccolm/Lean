import Dubon2026.ProfiniteProPKernelDiscreteMaps
import Dubon2026.CompactPrimeQuotientSeparation

/-! # The genuine fixed common-kernel quotient has only p-group discrete quotients -/

namespace Dubon2026

noncomputable section

/-- Every original continuous discrete quotient of the actual common-kernel quotient is a p-group. -/
theorem profiniteProPQuotient_continuous_quotient_isPGroup
    (p : ℕ) (G : ProfiniteGrp)
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G ⧸ profiniteProPKernel p G →* Q) (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsPGroup p Q := by
  let α := {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}
  letI : ∀ U : α, DiscreteTopology (G ⧸ U.val.toSubgroup) :=
    fun U => QuotientGroup.discreteTopology U.val.toOpenSubgroup.isOpen
  let π : ∀ U : α, G →* G ⧸ U.val.toSubgroup :=
    fun U => QuotientGroup.mk' U.val.toSubgroup
  let q := QuotientGroup.mk' (profiniteProPKernel p G)
  apply compact_reduction_continuous_quotient_isPGroup π
    (fun _ => QuotientGroup.continuous_mk) p (fun U => U.property)
    (f.comp q) (hf.comp QuotientGroup.continuous_mk)
    (hsurj.comp (QuotientGroup.mk'_surjective _))
  intro g hg
  have hcommon : g ∈ profiniteProPKernel p G := by
    apply (profiniteProPKernel_mem_iff p G g).mpr
    intro U hU
    have hπg := (Subgroup.mem_iInf.mp hg) (⟨U, hU⟩ : α)
    exact (QuotientGroup.eq_one_iff g).mp hπg
  change f (q g) = 1
  have hqg : q g = 1 := (QuotientGroup.eq_one_iff g).mpr hcommon
  rw [hqg, map_one]

end
end Dubon2026
