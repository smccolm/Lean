import Dubon2026.RectangularCongruence

/-! # Exact conjugation of the rectangular congruence subgroup -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups Pointwise ModularForm

noncomputable section

/-- The literal inverse diagonal conjugation, with integrality witnessed by the upper-right entry. -/
def levelLowerConjOfDvd (a : ℕ) (g : SL(2, ℤ))
    (hdvd : (a : ℤ) ∣ g 0 1) : SL(2, ℤ) :=
  ⟨!![g 0 0, g 0 1 / a; a * g 1 0, g 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (Matrix.det_fin_two g.val).symm.trans g.property -
      g 1 0 * Int.ediv_mul_cancel hdvd⟩

/-- Inverse conjugation restores the exact product-level lower-left divisibility. -/
theorem levelLowerConjOfDvd_mem_Gamma0 (a b : ℕ) (g : SL(2, ℤ))
    (hg : g ∈ rectangularCongruenceSubgroup a b) :
    levelLowerConjOfDvd a g hg.1 ∈ Gamma0 (a * b) := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  change ((a * b : ℕ) : ℤ) ∣ (a : ℤ) * g 1 0
  rw [Nat.cast_mul]
  exact mul_dvd_mul_left _ hg.2

/-- The inverse integral conjugation is the actual real matrix conjugation. -/
theorem levelLowerConjOfDvd_mul_matrix (a : ℕ) [NeZero a] (g : SL(2, ℤ))
    (hdvd : (a : ℤ) ∣ g 0 1) :
    levelRaiseMatrix a * mapGL ℝ (levelLowerConjOfDvd a g hdvd) =
      mapGL ℝ g * levelRaiseMatrix a := by
  have hdvd_real : (a : ℝ) * ((g 0 1 / (a : ℤ) : ℤ) : ℝ) = (g 0 1 : ℝ) := by
    rw [mul_comm, ← Int.cast_natCast (R := ℝ), ← Int.cast_mul, Int.ediv_mul_cancel hdvd]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [levelRaiseMatrix, levelLowerConjOfDvd, mul_comm, hdvd_real]

/-- The mixed group is exactly the real conjugate of Gamma0 at the product level. -/
theorem rectangularCongruence_map_eq_conj (a b : ℕ) [NeZero a] :
    (rectangularCongruenceSubgroup a b).map (mapGL ℝ) =
      ConjAct.toConjAct (levelRaiseMatrix a) • (Gamma0 (a * b)).map (mapGL ℝ) := by
  apply le_antisymm
  · rintro g ⟨γ, hγ, rfl⟩
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨mapGL ℝ (levelLowerConjOfDvd a γ hγ.1),
      ⟨_, levelLowerConjOfDvd_mem_Gamma0 a b γ hγ, rfl⟩, ?_⟩
    change levelRaiseMatrix a * mapGL ℝ (levelLowerConjOfDvd a γ hγ.1) *
      (levelRaiseMatrix a)⁻¹ = mapGL ℝ γ
    rw [levelLowerConjOfDvd_mul_matrix, mul_inv_cancel_right]
  · intro g hg
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hg
    obtain ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩ := hg
    refine ⟨levelRaiseConjOfDvd a γ (Gamma0_dmul_lower_left_dvd a b γ hγ),
      levelRaiseConjOfDvd_mem_rectangularCongruence a b γ hγ, ?_⟩
    change mapGL ℝ (levelRaiseConjOfDvd a γ _) =
      levelRaiseMatrix a * mapGL ℝ γ * (levelRaiseMatrix a)⁻¹
    rw [← levelRaiseMatrix_mul_mapGL a γ (Gamma0_dmul_lower_left_dvd a b γ hγ),
      mul_inv_cancel_right]

/-- The actual rescaled cusp form belongs to the exact mixed congruence subgroup. -/
def rectangularCuspForm {a b : ℕ} [NeZero a] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) :
    CuspForm ((rectangularCongruenceSubgroup a b).map (mapGL ℝ)) k :=
  cuspRestrictSubgroup (by rw [rectangularCongruence_map_eq_conj]; simp)
    (CuspForm.translate f (levelRaiseMatrix a)⁻¹)

/-- Rescaling retains the literal inverse slash operator and its determinant normalization. -/
theorem rectangularCuspForm_apply {a b : ℕ} [NeZero a] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) :
    ⇑(rectangularCuspForm f) = ⇑f ∣[k] (levelRaiseMatrix a)⁻¹ := rfl

end
end Dubon2026
