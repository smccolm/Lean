import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.GroupTheory.PGroup

/-! # The actual intersection of the original finite p-quotient kernels -/

namespace Dubon2026

noncomputable section

/-- The actual common kernel of all original open normal p-group quotients of a profinite group. -/
def profiniteProPKernel (p : ℕ) (G : ProfiniteGrp) : Subgroup G :=
  ⨅ U : OpenNormalSubgroup G, ⨅ (_ : IsPGroup p (G ⧸ U.toSubgroup)), U.toSubgroup

/-- Membership is the literal intersection condition over the original finite quotient family. -/
theorem profiniteProPKernel_mem_iff (p : ℕ) (G : ProfiniteGrp) (g : G) :
    g ∈ profiniteProPKernel p G ↔
      ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) → g ∈ U := by
  simp only [profiniteProPKernel, Subgroup.mem_iInf]
  rfl

/-- The common original p-quotient kernel lies in every original open normal p-quotient kernel. -/
theorem profiniteProPKernel_le_open (p : ℕ) (G : ProfiniteGrp)
    (U : OpenNormalSubgroup G) (hU : IsPGroup p (G ⧸ U.toSubgroup)) :
    profiniteProPKernel p G ≤ U.toSubgroup := by
  intro g hg
  exact (profiniteProPKernel_mem_iff p G g).mp hg U hU

/-- The original common kernel is normal as an actual intersection of normal subgroups. -/
instance profiniteProPKernelNormal (p : ℕ) (G : ProfiniteGrp) :
    (profiniteProPKernel p G).Normal := by
  constructor
  intro n hn g
  apply (profiniteProPKernel_mem_iff p G (g * n * g⁻¹)).mpr
  intro U hU
  exact Subgroup.Normal.conj_mem U.isNormal' n
    ((profiniteProPKernel_mem_iff p G n).mp hn U hU) g

/-- The original common kernel is closed in the actual profinite topology. -/
theorem profiniteProPKernel_isClosed (p : ℕ) (G : ProfiniteGrp) :
    IsClosed (profiniteProPKernel p G : Set G) := by
  simpa only [profiniteProPKernel, Subgroup.coe_iInf] using
    isClosed_iInter (fun U : OpenNormalSubgroup G =>
      isClosed_iInter (fun _ : IsPGroup p (G ⧸ U.toSubgroup) => U.toOpenSubgroup.isClosed))

end
end Dubon2026
