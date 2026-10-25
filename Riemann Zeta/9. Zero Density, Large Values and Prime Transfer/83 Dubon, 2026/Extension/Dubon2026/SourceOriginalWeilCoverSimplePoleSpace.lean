import Dubon2026.SourceOriginalWeilCoverSimplePoleBounds

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse ->
meromorphic loop generation for every permitted simple-pole differential.
Reuse the existing simple-pole subspace and finite residue-kernel argument
with the actual cover linear coefficients, residues and finite regular space.
A finite basis will allow one simultaneous integer loop formula to extend
by linearity to all allowed differentials; generation itself remains open. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)

/-- Original differentials with at most simple poles, all contained in the given finite set. -/
def coverSimplePoleSpace (S : Finset (Place ℂ EE)) : Submodule ℂ Ω[EE⁄ℂ] where
  carrier := {θ | ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential θ ∧ (v ∉ S → 0 ≤ v.ordDifferential θ)}
  zero_mem' v := by
    refine ⟨cover_simple_pole_zero_bound N n radicand v, fun _ => ?_⟩
    change 0 ≤ v.ord (coverDifferentialCoeff N n radicand v 0)
    rw [map_zero, v.ord_zero]
  add_mem' {θ₁ θ₂} h₁ h₂ v := by
    refine ⟨cover_simple_pole_add_bound N n radicand v (h₁ v).1 (h₂ v).1, fun hv => ?_⟩
    apply v.ord_nonneg_of_mem
    change coverDifferentialCoeff N n radicand v (θ₁ + θ₂) ∈ v.toValuationSubring
    rw [map_add]
    exact add_mem (v.mem_of_ord_nonneg ((h₁ v).2 hv)) (v.mem_of_ord_nonneg ((h₂ v).2 hv))
  smul_mem' c {θ} h v := by
    refine ⟨cover_simple_pole_smul_bound N n radicand v c (h v).1, fun hv => ?_⟩
    apply v.ord_nonneg_of_mem
    change coverDifferentialCoeff N n radicand v (c • θ) ∈ v.toValuationSubring
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (v.algebraMap_mem' c) (v.mem_of_ord_nonneg ((h v).2 hv))

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
