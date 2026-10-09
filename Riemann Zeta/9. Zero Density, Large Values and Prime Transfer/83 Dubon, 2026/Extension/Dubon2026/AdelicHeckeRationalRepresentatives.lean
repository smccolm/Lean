import Dubon2026.AdelicRationalTranslateRestriction
import Dubon2026.FiniteAdelicHeckeTrace
import Dubon2026.HeckeTransversalTrace

/-! # The same original rational Hecke representatives in real and finite adelic coordinates -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The literal original upper diagonal followed by each genuine classical Gamma0 representative, with its proved positive rational determinant. -/
def positiveHeckeRationalRepresentative (N p : ℕ) [NeZero p] (hpN : p.Coprime N)
    (x : Option (ZMod p)) : GL(2, ℚ)⁺ :=
  ⟨heckeTriangularRat 1 p 0 *
    GeneralLinearGroup.map (Int.castRingHom ℚ) (toGL (heckeUpperRepresentative p N hpN x).val), by
      change (0 : ℚ) < (GeneralLinearGroup.det (_ * _)).val
      rw [map_mul, GeneralLinearGroup.map_det, Matrix.SpecialLinearGroup.coeToGL_det, map_one, mul_one]
      change 0 < Matrix.det !![(1 : ℚ), 0; 0, (p : ℚ)]
      simpa only [Matrix.det_fin_two_of, one_mul, zero_mul, sub_zero] using
        (Nat.cast_pos.mpr (Nat.pos_of_neZero p) : (0 : ℚ) < p)⟩

/-- The genuine real coordinate of the original rational representative is precisely the classical slash matrix. -/
theorem positiveHeckeRationalRepresentative_real (N p : ℕ) [NeZero p] (hpN : p.Coprime N)
    (x : Option (ZMod p)) :
    (rationalPositiveGL2ToReal (positiveHeckeRationalRepresentative N p hpN x)).val =
      heckeTriangularMatrix 1 p 0 * mapGL ℝ (heckeUpperRepresentative p N hpN x).val := by
  change GeneralLinearGroup.map (algebraMap ℚ ℝ) (_ * _) = _
  rw [map_mul]
  congr 1
  apply Units.ext
  funext i j
  exact map_intCast (algebraMap ℚ ℝ) ((heckeUpperRepresentative p N hpN x).val i j)

/-- The genuine finite coordinate is exactly the original finite Hecke diagonal times the actual integral level representative. -/
theorem positiveHeckeRationalRepresentative_finite (N p : ℕ) [NeZero N] [NeZero p]
    (hpN : p.Coprime N) (x : Option (ZMod p)) :
    rationalPositiveGL2ToFinite (positiveHeckeRationalRepresentative N p hpN x) =
      finiteAdelicHeckeDiagonal p * (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN x)).val := by
  change GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (_ * _) = _
  rw [map_mul]
  congr 1
  apply Units.ext
  funext i j
  exact map_intCast (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) ((heckeUpperRepresentative p N hpN x).val i j)

/-- Every actual rational Hecke representative has exactly the same positive real determinant root. -/
theorem positiveHeckeRationalRepresentative_root (N p : ℕ) [NeZero p] (hpN : p.Coprime N)
    (x : Option (ZMod p)) :
    realPositiveDetRoot (rationalPositiveGL2ToReal (positiveHeckeRationalRepresentative N p hpN x)) =
      Real.sqrt (p : ℝ) := by
  unfold realPositiveDetRoot
  rw [positiveHeckeRationalRepresentative_real, Units.val_mul, Matrix.det_mul]
  simp only [← GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one, mul_one]
  change Real.sqrt (Matrix.det (heckeTriangularMatrix 1 p 0).val) = _
  rw [heckeTriangularMatrix_val]
  simp [Matrix.det_fin_two]

end
end Dubon2026
