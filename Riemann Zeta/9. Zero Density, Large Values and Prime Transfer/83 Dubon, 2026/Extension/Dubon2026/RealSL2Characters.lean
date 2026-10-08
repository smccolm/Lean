import Dubon2026.RealSL2Generators

/-! # Triviality of actual real special-linear characters into commutative monoids -/

namespace Dubon2026

noncomputable section
open scoped MatrixGroups

/-- Actual elementary commutators and Gaussian elimination exclude every nontrivial commutative real-group character. -/
theorem realSL2_commutative_group_character {A : Type*} [CommGroup A]
    (χ : SL(2, ℝ) →* A) (g : SL(2, ℝ)) : χ g = 1 := by
  have hu (t : ℝ) : χ (realUpperUnipotent t) = 1 := by
    rw [← realUpperUnipotent_commutator t]
    simp [map_mul, mul_assoc, mul_comm]
  have hl (t : ℝ) : χ (realLowerUnipotent t) = 1 := by
    rw [← realLowerUnipotent_commutator t]
    simp [map_mul, mul_assoc, mul_comm]
  have hw : χ realWeyl = 1 := by
    rw [realWeyl_eq_unipotents]
    simp only [map_mul, hu, hl, mul_one]
  have hd (a : ℝ) (ha : a ≠ 0) : χ (realDiagonal a ha) = 1 := by
    rw [realDiagonal_eq_unipotents]
    simp only [map_mul, hu, hl, hw, mul_one]
  have hg (v : SL(2, ℝ)) (ha : v 0 0 ≠ 0) : χ v = 1 := by
    rw [realSL2_gauss v ha]
    simp only [map_mul, hu, hl, hd, mul_one]
  by_cases ha : g 0 0 = 0
  · simpa only [map_mul, hw, one_mul] using hg (realWeyl * g) (realWeyl_mul_first_ne_zero g ha)
  · exact hg g ha

/-- Passing through genuine units proves character triviality even for commutative monoid targets. -/
theorem realSL2_commutative_character {A : Type*} [CommMonoid A]
    (χ : SL(2, ℝ) →* A) (g : SL(2, ℝ)) : χ g = 1 := by
  have he := realSL2_commutative_group_character χ.toHomUnits g
  exact congrArg Units.val he

end
end Dubon2026
