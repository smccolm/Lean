import TaoTrudgianYang2025.SargosPhaseCorrection

/-! Affine correction normalization on the full canonical interval for shifted physical windows. -/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosAffinePhysicalCorrection (U : ℝ → ℝ) (N A T₁ u : ℝ) : ℝ :=
  T₁⁻¹*U (N*u-A)

theorem sargosAffinePhysicalCorrection_contDiff {U : ℝ → ℝ} (hU : ContDiff ℝ ∞ U)
    (N A T₁ : ℝ) :
    ContDiff ℝ ∞ (sargosAffinePhysicalCorrection U N A T₁) :=
  contDiff_const.mul (hU.comp (by fun_prop))

theorem sargosAffinePhysicalCorrection_iteratedDeriv {U : ℝ → ℝ} (hU : ContDiff ℝ ∞ U)
    (N A T₁ u : ℝ) (j : ℕ) :
    iteratedDeriv j (sargosAffinePhysicalCorrection U N A T₁) u =
      (N^j/T₁)*iteratedDeriv j U (N*u-A) := by
  have ha := sargos_iteratedDeriv_comp_affine_local
    (l := u-1) (r := u+1) (c := N) (d := -A)
    (fun y hy => hU.contDiffAt)
    (show u ∈ Ioo (u-1) (u+1) by constructor <;> linarith) j
  have he : iteratedDeriv j (fun y => U (N*y-A)) u = N^j*iteratedDeriv j U (N*u-A) := by
    simpa only [sub_eq_add_neg] using ha
  unfold sargosAffinePhysicalCorrection
  rw [iteratedDeriv_const_mul_field,he]
  ring

theorem sargosAffinePhysicalCorrection_uniform_jets {U : ℝ → ℝ} {N A T₁ B : ℝ} {Q : ℕ}
    (hU : ContDiff ℝ ∞ U) (hN : 0 < N) (hT : 0 < T₁)
    (ha : N ≤ A) (hb : A ≤ 2*N)
    (hjets : ∀ x ∈ Icc (-N) N, ∀ j ≤ Q, |iteratedDeriv j U x| ≤ B/N^j)
    {u : ℝ} (hu : u ∈ phaseInterval) {j : ℕ} (hj : j ≤ Q) :
    |iteratedDeriv j (sargosAffinePhysicalCorrection U N A T₁) u| ≤ B/T₁ := by
  have hx : N*u-A ∈ Icc (-N) N := by
    constructor <;> nlinarith [hu.1,hu.2]
  rw [sargosAffinePhysicalCorrection_iteratedDeriv hU,abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ N^j/T₁)]
  calc
    _ ≤ (N^j/T₁)*(B/N^j) :=
      mul_le_mul_of_nonneg_left (hjets _ hx j hj) (by positivity)
    _ = _ := by field_simp

end TaoTrudgianYang2025
