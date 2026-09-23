import TaoTrudgianYang2025.SargosFourthDerivativeModel

/-! Closed model errors under a genuinely smooth correction and its physical normalization. -/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargos_approximateModel_add_correction {F U : ℝ → ℝ} {σ δ η : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hU : ContDiff ℝ ∞ U)
    (hjets : ∀ u ∈ phaseInterval, ∀ p ≤ P, |iteratedDeriv (p+1) U u| ≤ η) :
    IsApproximateModelPhaseFunction (fun u => F u+U u) σ P (δ+η) := by
  refine ⟨hF.1.add hU.contDiffOn,?_⟩
  intro p hp u
  have hn : ((p+1:ℕ) : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1)
  have he : modelPhaseErrorAt (fun u => F u+U u) σ p u =
      modelPhaseErrorAt F σ p u+iteratedDeriv (p+1) U u := by
    rw [modelPhaseErrorAt,iteratedDerivWithin_fun_add u.property uniqueDiffOn_phaseInterval
      ((hF.1 u u.property).of_le hn) (hU.contDiffAt.of_le hn).contDiffWithinAt,
      iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval
        (hU.contDiffAt.of_le hn) u.property]
    dsimp [modelPhaseErrorAt]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (hF.2 p hp u) (hjets u u.property p hp))

def sargosPhysicalCorrection (U : ℝ → ℝ) (M T₁ u : ℝ) : ℝ :=
  T₁⁻¹*U (M*(u-1))

theorem sargosPhysicalCorrection_contDiff {U : ℝ → ℝ} (hU : ContDiff ℝ ∞ U)
    (M T₁ : ℝ) :
    ContDiff ℝ ∞ (sargosPhysicalCorrection U M T₁) :=
  contDiff_const.mul (hU.comp (by fun_prop))

theorem sargosPhysicalCorrection_iteratedDeriv {U : ℝ → ℝ} (hU : ContDiff ℝ ∞ U)
    (M T₁ u : ℝ) (j : ℕ) :
    iteratedDeriv j (sargosPhysicalCorrection U M T₁) u =
      (M^j/T₁)*iteratedDeriv j U (M*(u-1)) := by
  have hn : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  unfold sargosPhysicalCorrection
  rw [iteratedDeriv_const_mul_field]
  change T₁⁻¹*iteratedDeriv j (fun x => (fun y => U (M*y)) (x-1)) u = _
  rw [iteratedDeriv_comp_sub_const (f := fun y => U (M*y)) (s := 1),
    iteratedDeriv_comp_const_mul (hU.of_le hn)]
  dsimp only
  ring

theorem sargosPhysicalCorrection_uniform_jets {U : ℝ → ℝ} {M T₁ B : ℝ} {Q : ℕ}
    (hU : ContDiff ℝ ∞ U) (hM : 0 < M) (hT : 0 < T₁)
    (hjets : ∀ x ∈ Icc 0 M, ∀ j ≤ Q, |iteratedDeriv j U x| ≤ B/M^j)
    {u : ℝ} (hu : u ∈ phaseInterval) {j : ℕ} (hj : j ≤ Q) :
    |iteratedDeriv j (sargosPhysicalCorrection U M T₁) u| ≤ B/T₁ := by
  have hx : M*(u-1) ∈ Icc 0 M := by
    constructor
    · exact mul_nonneg hM.le (by linarith [hu.1])
    · nlinarith [hu.2]
  rw [sargosPhysicalCorrection_iteratedDeriv hU,abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ M^j/T₁)]
  calc
    _ ≤ (M^j/T₁)*(B/M^j) :=
      mul_le_mul_of_nonneg_left (hjets _ hx j hj) (by positivity)
    _ = _ := by field_simp

end TaoTrudgianYang2025
