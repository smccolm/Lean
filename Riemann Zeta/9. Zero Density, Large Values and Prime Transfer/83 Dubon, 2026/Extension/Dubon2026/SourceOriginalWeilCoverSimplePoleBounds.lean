import Dubon2026.SourceOriginalWeilCoverDifferentialResidues
import Dubon2026.SourceOriginalWeilCoverCanonicalSupport
import Dubon2026.SourceCurveFiniteCoordinateGlobalResidues

/-! DUB-17/18 -> cover prescribed residues. Simple-pole bounds survive the
required finite linear combinations. The native finite-coordinate theorem
proves global residue vanishing for these actual cover differentials. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)

theorem cover_simple_pole_zero_bound (v : Place ℂ EE) :
    -1 ≤ v.ordDifferential (0 : Ω[EE⁄ℂ]) := by
  change -1 ≤ v.ord (coverDifferentialCoeff N n r v 0)
  rw [map_zero, v.ord_zero]
  norm_num

theorem cover_simple_pole_add_bound (v : Place ℂ EE) {ω η : Ω[EE⁄ℂ]}
    (hω : -1 ≤ v.ordDifferential ω) (hη : -1 ≤ v.ordDifferential η) :
    -1 ≤ v.ordDifferential (ω + η) := by
  rw [cover_simple_pole_bound_iff] at hω hη ⊢
  change v.uniformizer * coverDifferentialCoeff N n r v (ω + η) ∈ v.toValuationSubring
  rw [map_add, mul_add]
  exact add_mem hω hη

theorem cover_simple_pole_smul_bound (v : Place ℂ EE) (c : ℂ) {ω : Ω[EE⁄ℂ]}
    (hω : -1 ≤ v.ordDifferential ω) : -1 ≤ v.ordDifferential (c • ω) := by
  rw [cover_simple_pole_bound_iff] at hω ⊢
  change v.uniformizer * coverDifferentialCoeff N n r v (c • ω) ∈ v.toValuationSubring
  rw [map_smul, Algebra.smul_def, mul_left_comm]
  exact mul_mem (v.algebraMap_mem' c) hω

theorem cover_simple_pole_sum_bound {ι : Type*} (s : Finset ι) (ω : ι → Ω[EE⁄ℂ])
    (v : Place ℂ EE) (hω : ∀ i ∈ s, -1 ≤ v.ordDifferential (ω i)) :
    -1 ≤ v.ordDifferential (∑ i ∈ s, ω i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using cover_simple_pole_zero_bound N n r v
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact cover_simple_pole_add_bound N n r v (hω a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hω i (Finset.mem_insert_of_mem hi)))

theorem coverDifferentialResidue_finsum (ω : Ω[EE⁄ℂ]) :
    (∑ᶠ v : Place ℂ EE, coverDifferentialResidue N n r v ω) = 0 := by
  letI := (originalWeilKummerCover_finite_coordinate N ℂ n r).2
  simpa only [kaehlerResidueTermKFam_apply, diagonalHom_apply, one_mul,
    coverDifferentialResidue_apply] using finite_coordinate_global_residue_sum_zero
    (algebraMap FF EE (jOver N ℂ)) (originalWeilKummerCover_finite_coordinate N ℂ n r).1
    (cover_coordinate_differential_ne_zero N n r) (coverCanonicalLocalResidueData N n r) ω 1


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
