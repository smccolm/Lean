import Dubon2026.SourceGammaOneDifferentialResidues
import Dubon2026.SourceCurveFiniteCoordinateGlobalResidues

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> principal-divisor converse ->
prescribed-residue differential. Reuse actual local linear coefficients
for finite sums, and instantiate native finite-coordinate global residue
vanishing at j. A simple pole with zero residue is regular; this controls
all places outside the prescribed divisor, including the cusps. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve KaehlerDifferential
open scoped MatrixGroups
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
local notation "EE" => functionFieldOver Γ ℂ
include hT

theorem simple_pole_zero_bound (v : Place ℂ EE) :
    -1 ≤ v.ordDifferential (0 : Ω[EE⁄ℂ]) := by
  change -1 ≤ v.ord (differentialCoeff hT v 0)
  rw [map_zero, v.ord_zero]
  norm_num

theorem simple_pole_add_bound (v : Place ℂ EE) {ω η : Ω[EE⁄ℂ]}
    (hω : -1 ≤ v.ordDifferential ω) (hη : -1 ≤ v.ordDifferential η) :
    -1 ≤ v.ordDifferential (ω + η) := by
  rw [simple_pole_bound_iff] at hω hη ⊢
  change v.uniformizer * differentialCoeff hT v (ω + η) ∈ v.toValuationSubring
  rw [map_add, mul_add]
  exact add_mem hω hη

theorem simple_pole_smul_bound (v : Place ℂ EE) (c : ℂ) {ω : Ω[EE⁄ℂ]}
    (hω : -1 ≤ v.ordDifferential ω) : -1 ≤ v.ordDifferential (c • ω) := by
  rw [simple_pole_bound_iff] at hω ⊢
  change v.uniformizer * differentialCoeff hT v (c • ω) ∈ v.toValuationSubring
  rw [map_smul, Algebra.smul_def, mul_left_comm]
  exact mul_mem (v.algebraMap_mem' c) hω

theorem simple_pole_sum_bound {ι : Type*} (s : Finset ι) (ω : ι → Ω[EE⁄ℂ])
    (v : Place ℂ EE) (hω : ∀ i ∈ s, -1 ≤ v.ordDifferential (ω i)) :
    -1 ≤ v.ordDifferential (∑ i ∈ s, ω i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using simple_pole_zero_bound hT v
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact simple_pole_add_bound hT v (hω a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hω i (Finset.mem_insert_of_mem hi)))

theorem differentialResidue_finsum (ω : Ω[EE⁄ℂ]) :
    (∑ᶠ v : Place ℂ EE, differentialResidue hT v ω) = 0 := by
  letI := finiteDimensional_jCoordinateOver hT ℂ
  simpa only [kaehlerResidueTermKFam_apply, diagonalHom_apply, one_mul,
    differentialResidue_apply] using finite_coordinate_global_residue_sum_zero
    (jCoordinateOver Γ ℂ) (transcendental_jCoordinateOver Γ ℂ)
    (D_jCoordinateOver_ne_zero Γ ℂ) (differentialCanonicalLocalResidueData hT) ω 1

theorem simple_pole_regular_of_residue_zero (v : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : -1 ≤ v.ordDifferential ω) (hr : differentialResidue hT v ω = 0) :
    0 ≤ v.ordDifferential ω := by
  by_contra hn
  exact differentialResidue_ne_zero_of_simplePole hT v ω (by omega) hr



end
end Dubon2026.SourceFunctionField.GammaOne
