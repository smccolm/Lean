import Dubon2026.SourceStabilizerMeromorphicOrder
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> actual
meromorphic multiplier correction. Reuse native elliptic fixed points and
the repository Mobius-germ and signed parabolic classification results.
Adapt the remaining actual multiplier calculation from the Apache-2.0
scope-755b primary at revision 6e837e75355538c7f80bab5b956861e86c4eacc2.
No congruence level or central-sign normalization is discarded. -/
namespace Dubon2026.SourceMeromorphicMultiplier
noncomputable section
open UpperHalfPlane Filter SourceFunctionField.SubgroupStabilizer
open scoped MatrixGroups Topology
theorem exists_smul_eq_self_of_trace_sq_lt_four (γ : SL(2, ℤ))
    (h : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 < 4) : ∃ τ : ℍ, γ • τ = τ := by
  let g : GL (Fin 2) ℝ := γ
  have hdet : g.val.det = 1 := SourceFunctionField.SubgroupStabilizer.det_coe_SL γ
  have hell : g.IsElliptic := by
    change g.val.discr < 0
    rw [Matrix.discr_fin_two, hdet, mul_one, sub_neg]
    rw [Matrix.trace_fin_two] at h ⊢
    change ((γ 0 0 : ℝ) + (γ 1 1 : ℝ)) ^ 2 < 4
    exact_mod_cast h
  refine ⟨fixedPt g hell, ?_⟩
  change g • fixedPt g hell = fixedPt g hell
  exact (gl_smul_eq_self_iff_eq_fixedPt (by rw [hdet]; norm_num) hell).mpr rfl

end
end Dubon2026.SourceMeromorphicMultiplier
