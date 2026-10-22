import Dubon2026.SourceOriginalDifferentialResidues

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
prescribed residues. Simple-pole bounds are closed under finite complex
linear combinations. The proof uses regularity of the uniformizer times
the existing linear coefficient, so cancellation and zero differentials
are included without additional nonvanishing assumptions.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_simple_pole_zero_bound (v : Place ℂ F) :
    -1 ≤ v.ordDifferential (0 : Ω[F⁄ℂ]) := by
  change -1 ≤ v.ord (originalDifferentialCoeff N v 0)
  rw [map_zero, v.ord_zero]
  norm_num

theorem original_simple_pole_add_bound (v : Place ℂ F) {ω η : Ω[F⁄ℂ]}
    (hω : -1 ≤ v.ordDifferential ω) (hη : -1 ≤ v.ordDifferential η) :
    -1 ≤ v.ordDifferential (ω + η) := by
  rw [original_simple_pole_bound_iff] at hω hη ⊢
  change v.uniformizer * originalDifferentialCoeff N v (ω + η) ∈ v.toValuationSubring
  rw [map_add, mul_add]
  exact add_mem hω hη

theorem original_simple_pole_smul_bound (v : Place ℂ F) (c : ℂ) {ω : Ω[F⁄ℂ]}
    (hω : -1 ≤ v.ordDifferential ω) : -1 ≤ v.ordDifferential (c • ω) := by
  rw [original_simple_pole_bound_iff] at hω ⊢
  change v.uniformizer * originalDifferentialCoeff N v (c • ω) ∈ v.toValuationSubring
  rw [map_smul, Algebra.smul_def, mul_left_comm]
  exact mul_mem (v.algebraMap_mem' c) hω

theorem original_simple_pole_sum_bound {ι : Type*} (s : Finset ι) (ω : ι → Ω[F⁄ℂ])
    (v : Place ℂ F) (hω : ∀ i ∈ s, -1 ≤ v.ordDifferential (ω i)) :
    -1 ≤ v.ordDifferential (∑ i ∈ s, ω i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using original_simple_pole_zero_bound N v
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact original_simple_pole_add_bound N v (hω a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hω i (Finset.mem_insert_of_mem hi)))

theorem originalDifferentialResidue_finsum (ω : Ω[F⁄ℂ]) :
    (∑ᶠ v : Place ℂ F, originalDifferentialResidue N v ω) = 0 := by
  simpa only [kaehlerResidueTermKFam_apply, diagonalHom_apply, one_mul,
    originalDifferentialResidue_apply] using original_global_residue_sum_zero N ℂ ω 1

end
end Dubon2026.SourceFunctionField
