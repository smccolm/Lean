import Dubon2026.CompletedResidualCongruenceImages
import Dubon2026.CompletedResidualMatrixTopology
import Dubon2026.AdicMatrixProductEmbedding
import Dubon2026.ProfiniteCongruenceNeighborhoods

/-! # The genuine congruence basis and all discrete quotients of the original completed residual kernel -/

namespace Dubon2026

noncomputable section
open Matrix Filter Set
open scoped Topology

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The original completed residual matrix kernel is compact as the genuine closed kernel of its continuous residue reduction. -/
theorem completedResidualKernel_compactSpace
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    CompactSpace (MatrixCongruenceKernel (ι := ι)
      (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))) := by
  letI : DiscreteTopology (ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)) := by
    have h := adicPowerQuotient_discrete (R := ResidualRepresentationCompletion ρ) 1
    change DiscreteTopology (ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ 1) at h
    rw [pow_one] at h
    exact h
  have hc : Continuous (GeneralLinearGroup.map (n := ι)
      (R := ResidualRepresentationCompletion ρ)
      (S := ResidualRepresentationCompletion ρ ⧸
        IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)))) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact (QuotientRing.isOpenQuotientMap_mk _).continuous.comp
      (continuous_apply_apply i j)
  have hk : IsClosed ((MatrixCongruenceKernel (ι := ι)
      (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))) :
        Set (GeneralLinearGroup ι (ResidualRepresentationCompletion ρ))) :=
    isClosed_singleton.preimage hc
  exact isCompact_iff_compactSpace.mp hk.isCompact

/-- The original completed residual matrix kernel is reduced to its actual maximal-power matrix quotient. -/
def completedResidualPowerReduction
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (n : ℕ) :
    MatrixCongruenceKernel (ι := ι)
      (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)) →*
        GeneralLinearGroup ι (ResidualRepresentationCompletion ρ ⧸
          IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n) :=
  (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
    (S := ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n)
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n))).comp
      (MatrixCongruenceKernel (ι := ι)
        (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))).subtype

private theorem completedResidualReduction_embedding
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Topology.IsEmbedding (fun g n => completedResidualPowerReduction ρ n g) := by
  letI := residualRepresentationCompletion_compactSpace ρ
  exact (adicMatrixReductionProduct_isClosedEmbedding
    (R := ResidualRepresentationCompletion ρ) (ι := ι)).isEmbedding.comp
      Topology.IsEmbedding.subtypeVal

omit [Finite (IsLocalRing.ResidueField O)] in
private theorem completedResidualReduction_antitone
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Antitone (fun n => (completedResidualPowerReduction ρ n).ker) := by
  intro m n hmn u hu
  exact adicMatrixPowerReduction_kernel_antitone
    (R := ResidualRepresentationCompletion ρ) (ι := ι) hmn hu

/-- Every genuine identity neighborhood of the original completed residual kernel contains one actual congruence kernel. -/
theorem completedResidualPowerReduction_neighborhood
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (U : Set (MatrixCongruenceKernel (ι := ι)
      (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))))
    (hU : U ∈ 𝓝 1) :
    ∃ N : ℕ, ((completedResidualPowerReduction ρ N).ker : Set _) ⊆ U := by
  letI : ∀ n : ℕ, DiscreteTopology (ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n) :=
    fun n => adicPowerQuotient_discrete (R := ResidualRepresentationCompletion ρ) n
  exact discreteReduction_kernel_neighborhood (completedResidualPowerReduction ρ)
    (completedResidualReduction_embedding ρ) (completedResidualReduction_antitone ρ) U hU

/-- Every original continuous discrete quotient of the actual completed residual matrix kernel is a p-group for its genuine residue prime. -/
theorem completedResidualKernel_continuous_quotient_isPGroup
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : MatrixCongruenceKernel (ι := ι)
      (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)) →* Q)
    (hf : Continuous f) (hsurj : Function.Surjective f) : IsPGroup p Q := by
  letI : ∀ n : ℕ, DiscreteTopology (ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n) :=
    fun n => adicPowerQuotient_discrete (R := ResidualRepresentationCompletion ρ) n
  apply discreteReduction_continuous_quotient_isPGroup (completedResidualPowerReduction ρ)
    (completedResidualReduction_embedding ρ) (completedResidualReduction_antitone ρ) p
      ?_ f hf hsurj
  intro n
  have hrange : (completedResidualPowerReduction ρ n).range =
      CompletedResidualCongruenceImage ρ n := by
    rw [completedResidualPowerReduction, ← MonoidHom.map_range, Subgroup.range_subtype]
  rw [hrange]
  exact completedResidualCongruenceImage_isPGroup ρ p hp n

end
end Dubon2026
