import Dubon2026.MatrixRepresentationRelationIdeals
import Dubon2026.CompactAdicQuotients
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Quotient

/-! # The genuine topology of original matrix relation quotients -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type*} [Group G] [TopologicalSpace G]
  [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The actual descended matrix representation is continuous in the genuine group and coefficient quotient topologies. -/
theorem matrixRelationQuotientRepresentation_continuous
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (N : Subgroup G) [N.Normal] :
    Continuous (matrixRelationQuotientRepresentation ρ N) := by
  apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
  have hm : Continuous (GeneralLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (matrixRepresentationRelationIdeal ρ N))) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact (QuotientRing.isOpenQuotientMap_mk _).continuous.comp
      (continuous_apply_apply i j)
  exact hm.comp hρ

omit [TopologicalSpace G] in
/-- Imposing every original matrix relation preserves complete separated adic coefficients in the actual compact Noetherian case. -/
theorem matrixRelationQuotient_isAdicComplete
    [CompactSpace R] [T2Space R] [IsNoetherianRing R]
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G)
    (I : Ideal R) (hI : IsAdic I) :
    IsAdicComplete
      (I.map (Ideal.Quotient.mk (matrixRepresentationRelationIdeal ρ N)))
      (R ⧸ matrixRepresentationRelationIdeal ρ N) :=
  compactNoetherianAdicQuotient_complete I (matrixRepresentationRelationIdeal ρ N) hI

end
end Dubon2026
