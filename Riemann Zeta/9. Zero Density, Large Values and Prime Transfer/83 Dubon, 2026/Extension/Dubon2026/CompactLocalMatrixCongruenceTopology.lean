import Dubon2026.MatrixCongruenceKernelPGroup
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Openness of the original principal matrix congruence kernel

For DUB-17's compact open unitary level, the native compact local-ring
theorem makes the original maximal ideal open. Its genuine quotient
topology is discrete, so the original matrix residue kernel is open.
-/

namespace Dubon2026

noncomputable section

open Matrix IsLocalRing

/-- The original principal matrix congruence kernel is open over a compact Noetherian local ring. -/
theorem compactLocalMatrixCongruenceKernel_isOpen
    (R ι : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [Fintype ι] [DecidableEq ι] :
    IsOpen (MatrixCongruenceKernel (ι := ι) (maximalIdeal R) : Set (GeneralLinearGroup ι R)) := by
  letI : DiscreteTopology (R ⧸ maximalIdeal R) :=
    QuotientAddGroup.discreteTopology (IsLocalRing.isOpen_maximalIdeal R)
  have hr : Continuous (Ideal.Quotient.mk (maximalIdeal R)) :=
    (QuotientRing.isOpenQuotientMap_mk _).continuous
  have hm : Continuous (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk (maximalIdeal R))) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact hr.comp (continuous_apply_apply i j)
  exact (isOpen_discrete ({1} : Set (GeneralLinearGroup ι (R ⧸ maximalIdeal R)))).preimage hm

end
end Dubon2026
