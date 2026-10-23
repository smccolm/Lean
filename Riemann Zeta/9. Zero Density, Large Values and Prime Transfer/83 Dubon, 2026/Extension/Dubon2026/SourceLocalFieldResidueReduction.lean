import Dubon2026.CanonicalAdelicGL2Coordinates
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Ring.Compact

/-! DUB-17/18 -> continuous residual association -> actual coefficient
reduction. Reuse the native finite residue field, open maximal ideal and
quotient topology, and the existing continuous GL2 coefficient map. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
open Matrix
variable (E : Type*) [Field E] [ValuativeRel E] [UniformSpace E]
variable [IsNonarchimedeanLocalField E]

private local instance : TopologicalSpace 𝓀[E] :=
  inferInstanceAs (TopologicalSpace (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]))

theorem localCoefficientResidue_finite_discrete [IsUniformAddGroup E] :
    Finite 𝓀[E] ∧ DiscreteTopology 𝓀[E] :=
  ⟨inferInstance, QuotientAddGroup.discreteTopology (IsLocalRing.isOpen_maximalIdeal 𝒪[E])⟩

theorem localCoefficientResidue_continuous : Continuous (IsLocalRing.residue 𝒪[E]) :=
  (QuotientRing.isOpenQuotientMap_mk (IsLocalRing.maximalIdeal 𝒪[E])).continuous

variable {G : Type*} [Group G]

/-- The actual reduction of integral matrices modulo the coefficient maximal ideal. -/
def localFieldResidualRep (ρ : G →* GeneralLinearGroup (Fin 2) 𝒪[E]) :
    G →* GeneralLinearGroup (Fin 2) 𝓀[E] :=
  (GeneralLinearGroup.map (IsLocalRing.residue 𝒪[E])).comp ρ

theorem localFieldResidualRep_entry (ρ : G →* GeneralLinearGroup (Fin 2) 𝒪[E])
    (g : G) (i j : Fin 2) :
    (localFieldResidualRep E ρ g).val i j = IsLocalRing.residue 𝒪[E] ((ρ g).val i j) := rfl

theorem localFieldResidualRep_continuous [TopologicalSpace G]
    (ρ : G →* GeneralLinearGroup (Fin 2) 𝒪[E]) (hρ : Continuous ρ) :
    Continuous (localFieldResidualRep E ρ) :=
  (gl2Map_continuous (IsLocalRing.residue 𝒪[E]) (localCoefficientResidue_continuous E)).comp hρ

end
end Dubon2026
