import Dubon2026.ProfiniteProPQuotient

/-! # Genuine compact totally disconnected topology on the original fixed pro-p quotient -/

namespace Dubon2026

noncomputable section

/-- The literal family of original open normal subgroups with p-group quotients. -/
abbrev ProfinitePrimeQuotientIndex (p : ℕ) (G : ProfiniteGrp) :=
  {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}

/-- The actual common-kernel quotient maps into the product of its original finite p-group coordinates. -/
def profiniteProPQuotientCoordinates (p : ℕ) (G : ProfiniteGrp) :
    G ⧸ profiniteProPKernel p G →*
      ∀ U : ProfinitePrimeQuotientIndex p G, G ⧸ U.val.toSubgroup :=
  Pi.monoidHom (fun U => QuotientGroup.lift (profiniteProPKernel p G)
    (QuotientGroup.mk' U.val.toSubgroup)
    (by simpa only [QuotientGroup.ker_mk'] using
      profiniteProPKernel_le_open p G U.val U.property))

/-- The original finite p-group coordinates are continuous in the genuine fixed quotient topology. -/
theorem profiniteProPQuotientCoordinates_continuous (p : ℕ) (G : ProfiniteGrp) :
    Continuous (profiniteProPQuotientCoordinates p G) := by
  apply continuous_pi
  intro U
  apply (QuotientGroup.isQuotientMap_mk (profiniteProPKernel p G)).continuous_iff.mpr
  exact QuotientGroup.continuous_mk

/-- The original finite p-group coordinates separate every point of the genuine common-kernel quotient. -/
theorem profiniteProPQuotientCoordinates_injective (p : ℕ) (G : ProfiniteGrp) :
    Function.Injective (profiniteProPQuotientCoordinates p G) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (profiniteProPKernel p G) x
  apply (QuotientGroup.eq_one_iff g).mpr
  apply (profiniteProPKernel_mem_iff p G g).mpr
  intro U hU
  have hg := congrFun hx (⟨U, hU⟩ : ProfinitePrimeQuotientIndex p G)
  change QuotientGroup.mk' U.toSubgroup g = 1 at hg
  exact (QuotientGroup.eq_one_iff g).mp hg

/-- The actual fixed common-kernel quotient is totally disconnected in its original quotient topology. -/
theorem profiniteProPQuotient_totallyDisconnected (p : ℕ) (G : ProfiniteGrp) :
    TotallyDisconnectedSpace (G ⧸ profiniteProPKernel p G) := by
  letI : ∀ U : ProfinitePrimeQuotientIndex p G,
      DiscreteTopology (G ⧸ U.val.toSubgroup) :=
    fun U => QuotientGroup.discreteTopology U.val.toOpenSubgroup.isOpen
  refine ⟨isTotallyDisconnected_of_image
    (profiniteProPQuotientCoordinates_continuous p G).continuousOn
    (profiniteProPQuotientCoordinates_injective p G) ?_⟩
  exact isTotallyDisconnected_of_totallyDisconnectedSpace _

/-- The genuine fixed quotient of the original profinite group is bundled with its actual quotient topology. -/
def profiniteProPQuotient (p : ℕ) (G : ProfiniteGrp) : ProfiniteGrp := by
  letI : IsClosed (profiniteProPKernel p G : Set G) := profiniteProPKernel_isClosed p G
  letI := profiniteProPQuotient_totallyDisconnected p G
  exact ProfiniteGrp.of (G ⧸ profiniteProPKernel p G)

end
end Dubon2026
