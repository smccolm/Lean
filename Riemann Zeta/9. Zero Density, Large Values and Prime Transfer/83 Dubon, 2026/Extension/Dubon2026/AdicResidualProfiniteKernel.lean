import Dubon2026.AdicMatrixProductEmbedding
import Dubon2026.ProfiniteCongruenceNeighborhoods
import Dubon2026.MatrixCongruenceKernelImages
import Dubon2026.CompletedResidualMatrixTopology
import Dubon2026.ProfiniteProPKernel

/-! # The genuine residual pro-p kernel over any original compact Hausdorff adic ring -/

namespace Dubon2026

noncomputable section
open Matrix Set

variable {R ι : Type*} [CommRing R] [WithIdeal R] [T2Space R] [CompactSpace R]
  [Fintype ι] [DecidableEq ι]

/-- The actual residual matrix kernel reduces to every genuine original adic power quotient. -/
def adicCongruencePowerReduction (n : ℕ) :
    MatrixCongruenceKernel (ι := ι) (WithIdeal.i : Ideal R) →*
      GeneralLinearGroup ι (R ⧸ (WithIdeal.i : Ideal R) ^ n) :=
  (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ n))).comp
    (MatrixCongruenceKernel (ι := ι) (WithIdeal.i : Ideal R)).subtype

/-- The genuine original residual matrix kernel is compact in its actual subgroup topology. -/
theorem adicCongruenceKernel_compactSpace :
    CompactSpace (MatrixCongruenceKernel (ι := ι) (WithIdeal.i : Ideal R)) := by
  letI : CompactSpace (Matrix ι ι R) := inferInstanceAs (CompactSpace (ι → ι → R))
  letI : DiscreteTopology (R ⧸ (WithIdeal.i : Ideal R)) := by
    have h := adicPowerQuotient_discrete (R := R) 1
    rw [pow_one] at h
    exact h
  have hc : Continuous (GeneralLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (WithIdeal.i : Ideal R))) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact (QuotientRing.isOpenQuotientMap_mk _).continuous.comp
      (continuous_apply_apply i j)
  have hk : IsClosed (MatrixCongruenceKernel (ι := ι) (WithIdeal.i : Ideal R) :
      Set (GeneralLinearGroup ι R)) := isClosed_singleton.preimage hc
  exact isCompact_iff_compactSpace.mp hk.isCompact

/-- Every actual continuous discrete quotient of the original residual matrix kernel is a p-group when the original adic ideal contains p. -/
theorem adicCongruenceKernel_continuous_quotient_isPGroup
    (p : ℕ) (hp : p.Prime) (hpI : (p : R) ∈ (WithIdeal.i : Ideal R))
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : MatrixCongruenceKernel (ι := ι) (WithIdeal.i : Ideal R) →* Q)
    (hf : Continuous f) (hsurj : Function.Surjective f) : IsPGroup p Q := by
  letI : ∀ n : ℕ, DiscreteTopology (R ⧸ (WithIdeal.i : Ideal R) ^ n) :=
    fun n => adicPowerQuotient_discrete n
  have he : Topology.IsEmbedding (fun g n => adicCongruencePowerReduction (R := R) (ι := ι) n g) :=
    (adicMatrixReductionProduct_isClosedEmbedding (R := R) (ι := ι)).isEmbedding.comp
      Topology.IsEmbedding.subtypeVal
  have hm : Antitone (fun n => (adicCongruencePowerReduction (R := R) (ι := ι) n).ker) := by
    intro m n hmn u hu
    exact adicMatrixPowerReduction_kernel_antitone (R := R) (ι := ι) hmn hu
  apply discreteReduction_continuous_quotient_isPGroup
    (adicCongruencePowerReduction (R := R) (ι := ι)) he hm p ?_ f hf hsurj
  intro n
  have hrange : (adicCongruencePowerReduction (R := R) (ι := ι) n).range =
      (MatrixCongruenceKernel (ι := ι) (WithIdeal.i : Ideal R)).map
        (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ n))) := by
    rw [adicCongruencePowerReduction, ← MonoidHom.map_range, Subgroup.range_subtype]
  rw [hrange]
  exact matrixCongruenceKernel_powerImage_isPGroup (WithIdeal.i : Ideal R) hp hpI n

/-- The actual original adic matrix kernel with its proved profinite topology. -/
def adicResidualProfiniteKernel : ProfiniteGrp := by
  letI := adicCongruenceKernel_compactSpace (R := R) (ι := ι)
  letI := adicMatrixGroup_totallyDisconnected (R := R) (ι := ι)
  exact ProfiniteGrp.of (MatrixCongruenceKernel (ι := ι) (WithIdeal.i : Ideal R))

/-- Genuine finite p-quotients separate the actual entire original residual matrix kernel. -/
theorem adicResidualProfiniteKernel_commonKernel_eq_bot
    (p : ℕ) (hp : p.Prime) (hpI : (p : R) ∈ (WithIdeal.i : Ideal R)) :
    profiniteProPKernel p (adicResidualProfiniteKernel (R := R) (ι := ι)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  by_contra hne
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := adicResidualProfiniteKernel (R := R) (ι := ι))
    (U := ({g} : Set (adicResidualProfiniteKernel (R := R) (ι := ι)))ᶜ)
    isOpen_compl_singleton (by simpa only [mem_compl_iff, mem_singleton_iff] using Ne.symm hne)
  letI : DiscreteTopology (adicResidualProfiniteKernel (R := R) (ι := ι) ⧸ U.toSubgroup) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  let quotientPrimeGroup := adicCongruenceKernel_continuous_quotient_isPGroup
    (R := R) (ι := ι)
    (Q := adicResidualProfiniteKernel (R := R) (ι := ι) ⧸ U.toSubgroup) p hp hpI
  have hP : IsPGroup p (adicResidualProfiniteKernel (R := R) (ι := ι) ⧸ U.toSubgroup) :=
    quotientPrimeGroup (QuotientGroup.mk' U.toSubgroup) QuotientGroup.continuous_mk
      (QuotientGroup.mk'_surjective U.toSubgroup)
  have hgU := (profiniteProPKernel_mem_iff p _ g).mp hg U hP
  exact (hU hgU) rfl

end
end Dubon2026
