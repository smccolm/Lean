import Dubon2026.SourceOriginalGeneratorRatios

/-! DUB-17/18 -> matching cusp-form lower dimension -> analytic
realization of the original function field. Every actual field element
is a ratio of genuine same-weight Gamma0(N) modular forms. The proved
two-generator identity reduces this to actual j and j_N cusp ratios;
field-operation closure handles all elements. No realization or ratio
premise remains. Turning these ratios into meromorphic germs, normalized
places and regular-differential cusp forms remains required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

theorem isRatio_original_field (N : ℕ) [NeZero N] {x : LaurentSeries ℂ}
    (hx : x ∈ modularFunctionFieldOver N ℂ) : ModularRatios.IsRatio N x := by
  rw [original_field_eq_pair_over] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      rcases hy with rfl | hy
      · simpa only [qExpand_one_apply] using isRatio_coeffEmb_qExpand_jq N 1 (one_dvd N)
      · rcases hy with rfl
        exact isRatio_coeffEmb_qExpand_jq N N dvd_rfl
  | algebraMap c => exact ModularRatios.isRatio_algebraMap c
  | add _ _ _ _ hx hy => exact hx.add hy
  | inv _ _ hx => exact hx.inv
  | mul _ _ _ _ hx hy => exact hx.mul hy

theorem original_field_modular_ratio (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) :
    ∃ (k : ℤ) (g h : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k),
      h ≠ 0 ∧ (x : LaurentSeries ℂ) *
        (qExpansion 1 (h : UpperHalfPlane → ℂ) : LaurentSeries ℂ) =
          (qExpansion 1 (g : UpperHalfPlane → ℂ) : LaurentSeries ℂ) :=
  isRatio_original_field N x.2

end
end Dubon2026.SourceFunctionField
