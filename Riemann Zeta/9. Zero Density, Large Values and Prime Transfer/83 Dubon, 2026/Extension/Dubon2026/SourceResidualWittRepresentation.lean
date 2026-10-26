import Dubon2026.SourceResidualWittCoefficients
import Mathlib.Topology.Algebra.Group.Matrix

/-! DUB-17/18 -> arithmetic automorphy -> the genuine finite residual
deformation input over its Witt coefficient ring. Transport the same
original matrices through the proved residue-field equivalence. -/
namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
variable {G : Type} [Group G]
  (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K] [CharP K p]

/-- The original residual representation in the actual Witt residue field. -/
def sourceResidualWittRepresentation (σ : G →* GeneralLinearGroup (Fin 2) K) :
    G →* GeneralLinearGroup (Fin 2) (ResidueField (WittVector p K)) :=
  (GeneralLinearGroup.map (sourceResidualWittResidueEquiv p K).symm.toRingHom).comp σ

theorem sourceResidualWittRepresentation_original
    (σ : G →* GeneralLinearGroup (Fin 2) K) :
    (GeneralLinearGroup.map (sourceResidualWittResidueEquiv p K).toRingHom).comp
      (sourceResidualWittRepresentation p K σ) = σ := by
  apply MonoidHom.ext
  intro g
  apply GeneralLinearGroup.ext
  intro i j
  exact (sourceResidualWittResidueEquiv p K).apply_symm_apply ((σ g).val i j)

theorem sourceResidualWittRepresentation_continuous
    [TopologicalSpace G] [TopologicalSpace K] [DiscreteTopology K]
    (σ : G →* GeneralLinearGroup (Fin 2) K) (hσ : Continuous σ) :
    letI : TopologicalSpace (ResidueField (WittVector p K)) := ⊥
    Continuous (sourceResidualWittRepresentation p K σ) := by
  letI : TopologicalSpace (ResidueField (WittVector p K)) := ⊥
  exact (show Continuous
    (GeneralLinearGroup.map (n := Fin 2) (sourceResidualWittResidueEquiv p K).symm.toRingHom)
    from continuous_of_discreteTopology).comp hσ

end
end Dubon2026
