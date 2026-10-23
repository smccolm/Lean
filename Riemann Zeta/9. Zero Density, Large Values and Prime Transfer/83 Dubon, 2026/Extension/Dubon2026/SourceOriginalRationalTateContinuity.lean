import Dubon2026.SourceOriginalRationalTateGalois
import Dubon2026.SourceOriginalTatePadicContinuity
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Instances.Matrix

/-! DUB-17/18 -> continuous original rank-two Galois realization ->
continuity of the literal rational Tate action. The already proved
integral Tate matrix continuity survives native scalar extension. A
finite rational basis then gives continuous action on each actual vector
in the canonical module topology. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "Qbar" => AlgebraicClosure ℚ
local notation "V" => originalRationalTateModule N p

theorem originalRationalTateGalois_matrix_continuous {m : ℕ}
    (b : Module.Basis (Fin m) ℤ_[p] (TateModule p (originalJZero N))) :
    Continuous (fun σ : Qbar ≃ₐ[ℚ] Qbar =>
      LinearMap.toMatrix (Algebra.TensorProduct.basis ℚ_[p] b)
        (Algebra.TensorProduct.basis ℚ_[p] b) (originalRationalTateGaloisRep N p σ)) := by
  have hz := originalTateGaloisRep_matrix_continuous N p b
  have hc : Continuous (fun σ : Qbar ≃ₐ[ℚ] Qbar =>
      (LinearMap.toMatrix b b (originalTateGaloisRep N p σ)).map
        (algebraMap ℤ_[p] ℚ_[p])) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_subtype_val.comp ((continuous_apply j).comp ((continuous_apply i).comp hz))
  apply hc.congr
  intro σ
  exact (LinearMap.toMatrix_baseChange ℚ_[p] (originalTateGaloisRep N p σ) b b).symm

theorem originalRationalTateGalois_continuous_apply {m : ℕ}
    (b : Module.Basis (Fin m) ℤ_[p] (TateModule p (originalJZero N)))
    [TopologicalSpace V] [IsModuleTopology ℚ_[p] V] (x : V) :
    Continuous (fun σ : Qbar ≃ₐ[ℚ] Qbar => originalRationalTateGaloisRep N p σ x) := by
  letI := IsModuleTopology.toContinuousAdd ℚ_[p] V
  let B := Algebra.TensorProduct.basis ℚ_[p] b
  have h := (IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap).comp
    ((originalRationalTateGalois_matrix_continuous N p b).matrix_mulVec
      (continuous_const : Continuous (fun _ : Qbar ≃ₐ[ℚ] Qbar => B.equivFun x)))
  apply h.congr
  intro σ
  have hm := LinearMap.toMatrix_mulVec_repr B B (originalRationalTateGaloisRep N p σ) x
  exact (congrArg B.equivFun.symm hm).trans
    (B.equivFun.symm_apply_apply (originalRationalTateGaloisRep N p σ x))

end
end Dubon2026.SourceFunctionField.OriginalChart
