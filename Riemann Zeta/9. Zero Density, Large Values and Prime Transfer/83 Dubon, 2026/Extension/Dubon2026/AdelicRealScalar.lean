import Dubon2026.CanonicalAdelicGL2CuspLift
import Dubon2026.RealPositiveCentral

/-! # The actual trivial real scalar character of the original full adelic cusp function -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix UpperHalfPlane CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- The original scalar invertible matrix commutes with every genuine invertible matrix. -/
theorem gl2Scalar_mul_comm {R : Type*} [CommRing R] (u : Rˣ)
    (g : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.scalar (Fin 2) u * g = g * GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  exact Matrix.scalar_commute u.val (fun _ => mul_comm _ _) g.val

/-- Actual scalar-ring maps preserve the original scalar matrices. -/
theorem gl2Scalar_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : Rˣ) :
    GeneralLinearGroup.map f (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom u) := by
  apply Units.ext
  ext i j
  by_cases hij : i = j <;> simp [GeneralLinearGroup.map, GeneralLinearGroup.scalar, Matrix.scalar, hij]

/-- The positive real scalar retains its exact central commutation relation. -/
theorem realPositiveScalar_mul_comm (r : ℝ) (hr : r ≠ 0) (g : GL(2, ℝ)⁺) :
    realPositiveScalar r hr * g = g * realPositiveScalar r hr := by
  apply Subtype.ext
  exact gl2Scalar_mul_comm (Units.mk0 r hr) g.val

/-- Every original real scalar acts trivially on the genuine positive-real adelic cusp function at every finite point. -/
theorem positiveAdelicGL2CuspLift_real_scalar (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (r : ℝ) (hr : r ≠ 0)
    (g : GL(2, ℝ)⁺) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    positiveAdelicGL2CuspLift N k f (realPositiveScalar r hr * g) a =
      positiveAdelicGL2CuspLift N k f g a := by
  unfold positiveAdelicGL2CuspLift
  rw [← mul_assoc, ← realPositiveScalar_mul_comm, mul_assoc]
  exact realPositiveUnitaryLift_scalar_mul f r hr _

/-- Multiplication by an original positive-determinant matrix leaves the actual rational sign correction unchanged. -/
theorem realGL2RationalSign_positive_mul (s : GL(2, ℝ)⁺) (g : GeneralLinearGroup (Fin 2) ℝ) :
    realGL2RationalSign (s.val * g) = realGL2RationalSign g := by
  have he : 0 < (GeneralLinearGroup.det (s.val * g)).val ↔
      0 < (GeneralLinearGroup.det g).val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos_iff_of_pos_left s.property
  simp only [realGL2RationalSign, he]

/-- The actual positive-component correction commutes with every original real scalar. -/
theorem realGL2PositivePart_scalar (r : ℝ) (hr : r ≠ 0)
    (g : GeneralLinearGroup (Fin 2) ℝ) :
    realGL2PositivePart ((realPositiveScalar r hr).val * g) =
      realPositiveScalar r hr * realGL2PositivePart g := by
  apply Subtype.ext
  change (rationalGL2ToReal (realGL2RationalSign ((realPositiveScalar r hr).val * g)))⁻¹ *
      ((realPositiveScalar r hr).val * g) =
    (realPositiveScalar r hr).val * ((rationalGL2ToReal (realGL2RationalSign g))⁻¹ * g)
  rw [realGL2RationalSign_positive_mul, ← mul_assoc]
  change (rationalGL2ToReal (realGL2RationalSign g))⁻¹ *
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr) * g =
    GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr) *
      ((rationalGL2ToReal (realGL2RationalSign g))⁻¹ * g)
  rw [← gl2Scalar_mul_comm (Units.mk0 r hr), mul_assoc]

/-- The whole original adelic cusp function, including both real components, has trivial real scalar character. -/
theorem fullAdelicGL2CuspLift_real_scalar (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (r : ℝ) (hr : r ≠ 0)
    (g : GeneralLinearGroup (Fin 2) ℝ) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    fullAdelicGL2CuspLift N k f ((realPositiveScalar r hr).val * g) a =
      fullAdelicGL2CuspLift N k f g a := by
  unfold fullAdelicGL2CuspLift
  rw [realGL2PositivePart_scalar, realGL2RationalSign_positive_mul]
  exact positiveAdelicGL2CuspLift_real_scalar N f r hr _ _

end
end Dubon2026
