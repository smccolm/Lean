import Dubon2026.SourceHeckeProductConjugation

/-! DUB-17/18 -> original Picard-period Hecke comparison -> weighted
analytic divisor formula. The existing integral conjugation identifies
the actual upper Hecke subgroup with Gamma0 at the raised level. This
is needed to identify analytic fibers and their stabilizer multiplicities.
-/
namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups
variable (N ℓ : ℕ) [NeZero ℓ]

/-- The existing integral conjugate, with its actual stronger level condition. -/
def originalHeckeUpperToRaised (g : heckeUpperSubgroup N ℓ) : Gamma0 (N * ℓ) :=
  ⟨(sourceIntegralHeckeConjugate g).val, by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((N * ℓ : ℕ) : ℤ) ∣ g.val.val 1 0 * (ℓ : ℤ)
    rw [Nat.cast_mul]
    exact mul_dvd_mul
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (Gamma0_mem.mp g.val.property))
      (dvd_refl (ℓ : ℤ))⟩

/-- The existing level-raising conjugate, as an element of the upper subgroup. -/
def originalHeckeRaisedToUpper (g : Gamma0 (N * ℓ)) : heckeUpperSubgroup N ℓ := by
  have hg : g.val ∈ Gamma0 (ℓ * N) := by simpa only [mul_comm ℓ N] using g.property
  refine ⟨⟨levelRaiseConjOfDvd ℓ g.val (Gamma0_dmul_lower_left_dvd ℓ N g.val hg),
    levelRaiseConjOfDvd_mem_Gamma0 ℓ N g.val hg⟩, ?_⟩
  rw [sourceHeckeUpper_mem_iff]
  exact dvd_mul_right _ _

theorem originalHeckeRaisedToUpper_toRaised (g : heckeUpperSubgroup N ℓ) :
    originalHeckeRaisedToUpper N ℓ (originalHeckeUpperToRaised N ℓ g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have hb := (sourceHeckeUpper_mem_iff N ℓ g.val).mp g.property
  have hℓ : (ℓ : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalHeckeRaisedToUpper, originalHeckeUpperToRaised,
      sourceIntegralHeckeConjugate, levelRaiseConjOfDvd,
      Int.mul_ediv_cancel _ hℓ, Int.mul_ediv_cancel' hb]

theorem originalHeckeUpperToRaised_toUpper (g : Gamma0 (N * ℓ)) :
    originalHeckeUpperToRaised N ℓ (originalHeckeRaisedToUpper N ℓ g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  have hg : g.val ∈ Gamma0 (ℓ * N) := by simpa only [mul_comm ℓ N] using g.property
  have hc := Gamma0_dmul_lower_left_dvd ℓ N g.val hg
  have hℓ : (ℓ : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalHeckeRaisedToUpper, originalHeckeUpperToRaised,
      sourceIntegralHeckeConjugate, levelRaiseConjOfDvd,
      Int.mul_ediv_cancel_left _ hℓ, Int.ediv_mul_cancel hc]

/-- The actual diagonal conjugation equivalence, without a coprimality premise. -/
def originalHeckeUpperEquiv : heckeUpperSubgroup N ℓ ≃ Gamma0 (N * ℓ) where
  toFun := originalHeckeUpperToRaised N ℓ
  invFun := originalHeckeRaisedToUpper N ℓ
  left_inv := originalHeckeRaisedToUpper_toRaised N ℓ
  right_inv := originalHeckeUpperToRaised_toUpper N ℓ

theorem originalHeckeUpperToRaised_matrix (g : heckeUpperSubgroup N ℓ) :
    levelRaiseMatrix ℓ * mapGL ℝ (originalHeckeUpperToRaised N ℓ g).val =
      mapGL ℝ g.val.val * levelRaiseMatrix ℓ := by
  have hb := (sourceHeckeUpper_mem_iff N ℓ g.val).mp g.property
  have hbr : (ℓ : ℝ) * ((g.val.val 0 1 / (ℓ : ℤ) : ℤ) : ℝ) =
      (g.val.val 0 1 : ℝ) := by exact_mod_cast Int.mul_ediv_cancel' hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalHeckeUpperToRaised, sourceIntegralHeckeConjugate,
      levelRaiseMatrix, mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two, hbr, mul_comm]

theorem originalHeckeUpperToRaised_smul (g : heckeUpperSubgroup N ℓ) (w : ℍ) :
    levelRaiseMatrix ℓ • ((originalHeckeUpperToRaised N ℓ g).val • w) =
      g.val.val • (levelRaiseMatrix ℓ • w) := by
  change levelRaiseMatrix ℓ • (mapGL ℝ (originalHeckeUpperToRaised N ℓ g).val • w) =
    mapGL ℝ g.val.val • (levelRaiseMatrix ℓ • w)
  rw [← mul_smul, originalHeckeUpperToRaised_matrix, mul_smul]

end
end Dubon2026
