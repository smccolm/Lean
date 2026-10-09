import Dubon2026.CompletedResidualCongruenceBasis
import Dubon2026.ProfiniteProPKernelFunctoriality

/-! # The actual common p-quotient kernel of the original completed residual matrix group -/

namespace Dubon2026

noncomputable section
open Matrix Set

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The original completed residual matrix kernel with its genuine proved profinite topology. -/
def completedResidualProfiniteKernel
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) : ProfiniteGrp := by
  letI := completedResidualKernel_compactSpace ρ
  exact ProfiniteGrp.of (MatrixCongruenceKernel (ι := ι)
    (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)))

/-- The genuine finite p-quotients already separate the entire original completed residual matrix kernel. -/
theorem completedResidualProfiniteKernel_commonKernel_eq_bot
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p] :
    profiniteProPKernel p (completedResidualProfiniteKernel ρ) = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  by_contra hne
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := completedResidualProfiniteKernel ρ)
    (U := ({g} : Set (completedResidualProfiniteKernel ρ))ᶜ)
    isOpen_compl_singleton (by simpa only [mem_compl_iff, mem_singleton_iff] using Ne.symm hne)
  letI : DiscreteTopology (completedResidualProfiniteKernel ρ ⧸ U.toSubgroup) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  let quotientPrimeGroup := completedResidualKernel_continuous_quotient_isPGroup
    (Q := completedResidualProfiniteKernel ρ ⧸ U.toSubgroup) ρ p hp
  have hP : IsPGroup p (completedResidualProfiniteKernel ρ ⧸ U.toSubgroup) :=
    quotientPrimeGroup (QuotientGroup.mk' U.toSubgroup) QuotientGroup.continuous_mk
      (QuotientGroup.mk'_surjective U.toSubgroup)
  have hgU := (profiniteProPKernel_mem_iff p (completedResidualProfiniteKernel ρ) g).mp hg U hP
  exact (hU hgU) rfl

end
end Dubon2026
