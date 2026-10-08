import Dubon2026.RealPositiveUnitaryLift

/-! # The genuine trivial real central character of the original normalized cusp representation -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The genuine scalar matrix for every nonzero real scalar, with its actual positive determinant. -/
def realPositiveScalar (r : ℝ) (hr : r ≠ 0) : GL(2, ℝ)⁺ :=
  ⟨GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr), by
    change 0 < Matrix.det (Matrix.scalar (Fin 2) r)
    simpa [Matrix.scalar, Matrix.det_diagonal, Fin.prod_univ_two, ← pow_two] using sq_pos_of_ne_zero hr⟩

/-- The original scalar matrix retains precisely its literal diagonal entries. -/
theorem realPositiveScalar_val (r : ℝ) (hr : r ≠ 0) :
    ((realPositiveScalar r hr).val : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) r := rfl

/-- The actual determinant root of a nonzero scalar matrix is its real absolute value. -/
theorem realPositiveDetRoot_scalar (r : ℝ) (hr : r ≠ 0) :
    realPositiveDetRoot (realPositiveScalar r hr) = |r| := by
  simp [realPositiveDetRoot, realPositiveScalar_val, Matrix.scalar,
    Matrix.det_diagonal, Real.sqrt_sq_eq_abs]

/-- Normalizing a positive scalar gives the genuine identity real matrix. -/
theorem realPositiveNormalize_scalar_pos (r : ℝ) (hr : 0 < r) :
    realPositiveNormalize (realPositiveScalar r hr.ne') = 1 := by
  apply Subtype.ext
  rw [realPositiveNormalize_val, realPositiveDetRoot_scalar, abs_of_pos hr, realPositiveScalar_val]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar, hij, hr.ne']

/-- Normalizing a negative scalar gives the genuine central negative identity. -/
theorem realPositiveNormalize_scalar_neg (r : ℝ) (hr : r < 0) :
    realPositiveNormalize (realPositiveScalar r hr.ne) = -1 := by
  apply Subtype.ext
  rw [realPositiveNormalize_val, realPositiveDetRoot_scalar, abs_of_neg hr, realPositiveScalar_val]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar, hij, hr.ne]

/-- Every actual nonzero real scalar becomes the identity in the genuine projective normalization. -/
theorem realPositiveNormalize_scalar_projective (r : ℝ) (hr : r ≠ 0) :
    (QuotientGroup.mk (realPositiveNormalize (realPositiveScalar r hr)) : PSL(2, ℝ)) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [realSL2_center_eq_signs]
  rcases lt_or_gt_of_ne hr with hn | hp
  · exact Or.inr (realPositiveNormalize_scalar_neg r hn)
  · exact Or.inl (realPositiveNormalize_scalar_pos r hp)

/-- The actual completed cusp representation has trivial real scalar central character. -/
theorem realPositiveHilbertRepresentation_scalar {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (r : ℝ) (hr : r ≠ 0)
    (v : RealProjectiveHilbert f) :
    realPositiveHilbertRepresentation f (realPositiveScalar r hr) v = v := by
  change realProjectiveHilbertRepresentation f
    (QuotientGroup.mk (realPositiveNormalize (realPositiveScalar r hr))) v = v
  rw [realPositiveNormalize_scalar_projective]
  simp

/-- The literal original unitary cusp function is unchanged under every actual real scalar matrix. -/
theorem realPositiveUnitaryLift_scalar_mul {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (r : ℝ) (hr : r ≠ 0)
    (g : GL(2, ℝ)⁺) :
    realPositiveUnitaryLift k f (realPositiveScalar r hr * g) = realPositiveUnitaryLift k f g := by
  change realProjectiveCuspLift f
    (QuotientGroup.mk (realPositiveNormalize (realPositiveScalar r hr * g))) =
      realProjectiveCuspLift f (QuotientGroup.mk (realPositiveNormalize g))
  rw [map_mul, QuotientGroup.mk_mul, realPositiveNormalize_scalar_projective, one_mul]

end
end Dubon2026
