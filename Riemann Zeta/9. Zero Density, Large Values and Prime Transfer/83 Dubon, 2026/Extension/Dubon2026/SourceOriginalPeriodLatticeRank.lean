import Dubon2026.SourceOriginalDiscretePeriodLattice
import Mathlib.Algebra.Module.ZLattice.Basic

/-! DUB-17/18 -> original torsion cardinality -> complex Picard comparison.
The already proved original discreteness and full real span identify the
actual period subgroup as an integral lattice of rank 2g. Native ZLattice
theorems supply freeness and finite generation; no new lattice is substituted.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_period_lattice_free_finite_rank {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) :
    Module.Free ℤ (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) ∧
      Module.Finite ℤ (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) ∧
      Module.finrank ℤ (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) = 2 * n := by
  let L := pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))
  letI : DiscreteTopology L := original_discrete_period_lattice N b
  letI : IsZLattice ℝ L := ⟨span_real_pathPeriodLattice_eq_top N b⟩
  refine ⟨ZLattice.module_free ℝ L, ZLattice.module_finite ℝ L, ?_⟩
  change Module.finrank ℤ L = 2 * n
  rw [ZLattice.rank ℝ L, finrank_real_of_complex, Module.finrank_fin_fun]

end
end Dubon2026.SourceFunctionField.OriginalChart
