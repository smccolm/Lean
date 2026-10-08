import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

/-! # Actual elementary matrices over a commutative ring -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable {R : Type*} [CommRing R]

/-- The upper elementary matrix over the original scalar ring. -/
def ringUpperUnipotent (t : R) : SL(2, R) := ⟨!![1, t; 0, 1], by simp⟩

/-- The lower elementary matrix over the original scalar ring. -/
def ringLowerUnipotent (t : R) : SL(2, R) := ⟨!![1, 0; t, 1], by simp⟩

/-- The determinant-one diagonal attached to an actual unit. -/
def ringSL2UnitDiagonal (u : Rˣ) : SL(2, R) := ⟨!![↑u, 0; 0, ↑u⁻¹], by simp⟩

/-- The elementary upper matrix varies continuously in its actual entry. -/
theorem ringUpperUnipotent_continuous [TopologicalSpace R] :
    Continuous (ringUpperUnipotent (R := R)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- The elementary lower matrix varies continuously in its actual entry. -/
theorem ringLowerUnipotent_continuous [TopologicalSpace R] :
    Continuous (ringLowerUnipotent (R := R)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- Every actual unit diagonal is a finite word in upper and lower elementary matrices. -/
theorem ringSL2UnitDiagonal_eq_unipotents (u : Rˣ) :
    ringSL2UnitDiagonal u =
      ringUpperUnipotent (↑u : R) * ringLowerUnipotent (-(↑u⁻¹ : R)) *
      ringUpperUnipotent (↑u : R) *
      (ringUpperUnipotent (-1) * ringLowerUnipotent 1 * ringUpperUnipotent (-1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ringSL2UnitDiagonal, ringUpperUnipotent, ringLowerUnipotent,
      coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- Gaussian elimination at an actual unit pivot preserves the original matrix exactly. -/
theorem ringSL2_gauss_unit (g : SL(2, R)) (u : Rˣ) (hu : g 0 0 = ↑u) :
    g = ringLowerUnipotent (g 1 0 * (↑u⁻¹ : R)) * ringSL2UnitDiagonal u *
      ringUpperUnipotent (g 0 1 * (↑u⁻¹ : R)) := by
  have hd : g 0 0 * g 1 1 = 1 + g 0 1 * g 1 0 := by
    exact sub_eq_iff_eq_add.mp (by simpa only [Matrix.det_fin_two] using g.property)
  have hd' : g 1 1 = (↑u⁻¹ : R) * (1 + g 0 1 * g 1 0) := by
    rw [← hd, hu, ← mul_assoc, Units.inv_mul, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ringLowerUnipotent, ringSL2UnitDiagonal, ringUpperUnipotent,
      coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hu]
  · calc
      g 0 1 = g 0 1 * ((↑u : R) * (↑u⁻¹ : R)) := by simp
      _ = (↑u : R) * (g 0 1 * (↑u⁻¹ : R)) := by ring
  · rw [hd']; ring

/-- A subgroup containing all elementary matrices contains every matrix with a unit first entry. -/
theorem ringSL2_mem_of_unit_pivot (H : Subgroup SL(2, R))
    (hU : ∀ t : R, ringUpperUnipotent t ∈ H)
    (hL : ∀ t : R, ringLowerUnipotent t ∈ H)
    (g : SL(2, R)) (hg : IsUnit (g 0 0)) : g ∈ H := by
  obtain ⟨u, hu⟩ := hg
  rw [ringSL2_gauss_unit g u hu.symm, ringSL2UnitDiagonal_eq_unipotents]
  exact H.mul_mem (H.mul_mem (hL _) (H.mul_mem
    (H.mul_mem (H.mul_mem (hU _) (hL _)) (hU _))
    (H.mul_mem (H.mul_mem (hU _) (hL _)) (hU _)))) (hU _)

/-- One elementary row operation producing a unit pivot suffices for membership. -/
theorem ringSL2_mem_of_elementary_unit_pivot (H : Subgroup SL(2, R))
    (hU : ∀ t : R, ringUpperUnipotent t ∈ H)
    (hL : ∀ t : R, ringLowerUnipotent t ∈ H)
    (g : SL(2, R)) (t : R) (hg : IsUnit ((ringUpperUnipotent t * g) 0 0)) : g ∈ H := by
  have h := ringSL2_mem_of_unit_pivot H hU hL (ringUpperUnipotent t * g) hg
  simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem (hU t)) h

end
end Dubon2026
