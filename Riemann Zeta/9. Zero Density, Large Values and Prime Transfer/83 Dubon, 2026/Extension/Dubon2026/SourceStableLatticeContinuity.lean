import Dubon2026.SourceStableLatticeFieldComparison
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-! DUB-17/18 -> continuous residual association -> continuity of the
constructed integral matrices. Their included entries are coordinates
of the original continuous field action in the extended lattice basis.
The integer ring carries the induced topology, so this proves continuity
without an additional topology hypothesis on the lattice. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
open Matrix
variable {E G : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
variable [IsTopologicalRing E] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* GeneralLinearGroup (Fin 2) E)
variable (L : Submodule 𝒪[E] (Fin 2 → E)) [Submodule.IsLattice E L]
variable (hL : ∀ g x, x ∈ L → (ρ g).val *ᵥ x ∈ L) (b : Module.Basis (Fin 2) 𝒪[E] L)

omit [IsTopologicalGroup G] in
theorem stableLatticeGeneralLinearRep_entry_continuous (hρ : Continuous ρ) (i j : Fin 2) :
    Continuous (fun g => (stableLatticeGeneralLinearRep ρ L hL b g).val i j) := by
  apply continuous_induced_rng.mpr
  have h := (IsModuleTopology.continuous_of_linearMap ((b.extendOfIsLattice E).coord i)).comp
    ((Units.continuous_val.comp hρ).matrix_mulVec
      (continuous_const : Continuous (fun _ : G => b.extendOfIsLattice E j)))
  apply h.congr
  intro g
  exact (stableLatticeGeneralLinearRep_field_entry ρ L hL b g i j).symm

theorem stableLatticeGeneralLinearRep_continuous (hρ : Continuous ρ) :
    Continuous (stableLatticeGeneralLinearRep ρ L hL b) := by
  have hm : Continuous (fun g => (stableLatticeGeneralLinearRep ρ L hL b g).val) :=
    continuous_matrix (stableLatticeGeneralLinearRep_entry_continuous ρ L hL b hρ)
  apply Units.continuous_iff.mpr
  exact ⟨hm, hm.comp continuous_inv⟩

end
end Dubon2026
