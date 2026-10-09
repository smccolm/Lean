import Dubon2026.ProfiniteProPKernel
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Original continuous discrete p-group maps kill the fixed common kernel -/

namespace Dubon2026

noncomputable section

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- Every original continuous map to a discrete p-group kills the same genuine original p-quotient kernel. -/
theorem profiniteProPKernel_le_discrete_kernel (p : ℕ) (G : ProfiniteGrp)
    (f : G →* Q) (hf : Continuous f) (hQ : IsPGroup p Q) :
    profiniteProPKernel p G ≤ f.ker := by
  let U : OpenNormalSubgroup G := {
    toOpenSubgroup := ⟨f.ker, (isOpen_discrete ({1} : Set Q)).preimage hf⟩
    isNormal' := inferInstance }
  have hU : IsPGroup p (G ⧸ U.toSubgroup) :=
    hQ.of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
  exact profiniteProPKernel_le_open p G U hU

/-- The original discrete p-group map descends through the actual fixed quotient of its original profinite source. -/
def profiniteProPDiscreteFactor (p : ℕ) (G : ProfiniteGrp)
    (f : G →* Q) (hf : Continuous f) (hQ : IsPGroup p Q) :
    G ⧸ profiniteProPKernel p G →* Q :=
  QuotientGroup.lift (profiniteProPKernel p G) f
    (profiniteProPKernel_le_discrete_kernel p G f hf hQ)

/-- The genuine fixed-quotient factor retains every original value. -/
theorem profiniteProPDiscreteFactor_mk (p : ℕ) (G : ProfiniteGrp)
    (f : G →* Q) (hf : Continuous f) (hQ : IsPGroup p Q) (g : G) :
    profiniteProPDiscreteFactor p G f hf hQ
      (QuotientGroup.mk' (profiniteProPKernel p G) g) = f g := rfl

/-- The actual descended original p-group map is continuous in the genuine quotient topology. -/
theorem profiniteProPDiscreteFactor_continuous (p : ℕ) (G : ProfiniteGrp)
    (f : G →* Q) (hf : Continuous f) (hQ : IsPGroup p Q) :
    Continuous (profiniteProPDiscreteFactor p G f hf hQ) := by
  apply (QuotientGroup.isQuotientMap_mk (profiniteProPKernel p G)).continuous_iff.mpr
  exact hf

end
end Dubon2026
