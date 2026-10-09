import Dubon2026.GeneralLinearUnitDiagonal
import Dubon2026.RingSL2Elementary

/-! # Literal two-unit diagonals and Gaussian elimination in the original general-linear group -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup

/-- The genuine diagonal with its two original invertible entries. -/
def gl2UnitDiagonalPair {R : Type*} [CommRing R] (u v : Rˣ) : GeneralLinearGroup (Fin 2) R where
  val := !![↑u, 0; 0, ↑v]
  inv := !![↑u⁻¹, 0; 0, ↑v⁻¹]
  val_inv := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Multiplication of the actual two-unit diagonals is exactly coordinatewise unit multiplication. -/
theorem gl2UnitDiagonalPair_mul {R : Type*} [CommRing R] (a b c d : Rˣ) :
    gl2UnitDiagonalPair a b * gl2UnitDiagonalPair c d = gl2UnitDiagonalPair (a * c) (b * d) := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2UnitDiagonalPair, Matrix.mul_apply, Fin.sum_univ_two]

/-- The original unit diagonal pair is exactly the identity matrix. -/
theorem gl2UnitDiagonalPair_one {R : Type*} [CommRing R] :
    gl2UnitDiagonalPair (1 : Rˣ) 1 = 1 := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [gl2UnitDiagonalPair]

/-- Powers of the original diagonal are exactly the powers of its original unit entries. -/
theorem gl2UnitDiagonalPair_pow {R : Type*} [CommRing R] (u v : Rˣ) (n : ℕ) :
    (gl2UnitDiagonalPair u v) ^ n = gl2UnitDiagonalPair (u ^ n) (v ^ n) := by
  induction n with
  | zero => simp only [pow_zero, gl2UnitDiagonalPair_one]
  | succ n ih => rw [pow_succ, ih, gl2UnitDiagonalPair_mul, ← pow_succ, ← pow_succ]

/-- Mapping the genuine diagonal into an original scalar ring maps exactly its two original units. -/
theorem gl2UnitDiagonalPair_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (u v : Rˣ) :
    GeneralLinearGroup.map φ (gl2UnitDiagonalPair u v) =
      gl2UnitDiagonalPair (Units.map φ.toMonoidHom u) (Units.map φ.toMonoidHom v) := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [gl2UnitDiagonalPair, GeneralLinearGroup.map]

/-- Gaussian elimination expresses the actual original matrix through its two literal unipotent entries and invertible diagonal. -/
theorem gl2_gauss_unit_pivot {R : Type*} [CommRing R]
    (g : GeneralLinearGroup (Fin 2) R) (u : Rˣ) (hu : g.val 0 0 = ↑u) :
    g = toGL (ringLowerUnipotent (g.val 1 0 * (↑u⁻¹ : R))) *
      gl2UnitDiagonalPair u (GeneralLinearGroup.det g * u⁻¹) *
      toGL (ringUpperUnipotent (g.val 0 1 * (↑u⁻¹ : R))) := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2UnitDiagonalPair, ringLowerUnipotent, ringUpperUnipotent,
      toGL, Matrix.mul_apply, Fin.sum_univ_two, hu, GeneralLinearGroup.det, Matrix.det_fin_two]
  · calc
      g.val 0 1 = g.val 0 1 * ((↑u : R) * (↑u⁻¹ : R)) := by simp
      _ = (↑u : R) * (g.val 0 1 * (↑u⁻¹ : R)) := by ring
  · calc
      g.val 1 1 = g.val 1 1 * ((↑u : R) * (↑u⁻¹ : R)) := by simp
      _ = g.val 1 0 * (g.val 0 1 * (↑u⁻¹ : R)) +
        ((↑u : R) * g.val 1 1 - g.val 0 1 * g.val 1 0) * (↑u⁻¹ : R) := by ring

end
end Dubon2026
