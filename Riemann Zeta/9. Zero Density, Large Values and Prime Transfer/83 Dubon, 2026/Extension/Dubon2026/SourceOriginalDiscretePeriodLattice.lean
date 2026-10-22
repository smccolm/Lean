import Dubon2026.SourceOriginalConstructedGeneratingLoops
import Dubon2026.SourceOriginalDiscretePeriodsOfLoops

/-! DUB-17/18 -> original torsion cardinality -> original Abel-Jacobi.
The exact original period lattice is discrete, with no loop-generation premise.
Reuse the already proved full real span and the basis/discreteness theorem;
the actual generators and their integer coefficients are now constructed.
The Abel converse, Qbar comparison and arithmetic realization remain required.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_integral_period_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) :
    ∃ B : Module.Basis (Fin n ⊕ Fin n) ℝ (Fin n → ℂ),
      pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])) = Submodule.span ℤ (Set.range B) := by
  obtain ⟨Pz, Z, hgen⟩ := exists_original_generating_loops N b
  obtain ⟨B, _, hB⟩ := original_period_basis_of_generating_loops N b Pz Z hgen
  exact ⟨B, hB⟩

theorem original_discrete_period_lattice {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) :
    DiscreteTopology (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) := by
  obtain ⟨Pz, Z, hgen⟩ := exists_original_generating_loops N b
  exact original_discrete_periods_of_generating_loops N b Pz Z hgen

end
end Dubon2026.SourceFunctionField.OriginalChart
