import Dubon2026.RealAffineLift
import Dubon2026.HeckePrimeInvariance

/-! # Exact determinant-one representatives and normalization for the real Hecke action -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- The original upper Hecke point is the action of its actual determinant-one real representative. -/
theorem realAffineMatrix_hecke_upper (p b : ℕ) [NeZero p] (z : ℍ) :
    realAffineMatrix ((b : ℝ) / p)
      (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero p))) • z = heckeUpperPoint p b z := by
  apply UpperHalfPlane.ext
  rw [realAffineMatrix_smul]
  dsimp only [heckeUpperPoint]
  push_cast
  ring

/-- The original lower Hecke point is the action of its actual determinant-one real representative. -/
theorem realAffineMatrix_hecke_lower (p : ℕ) [NeZero p] (z : ℍ) :
    realAffineMatrix 0 (Nat.cast_pos.mpr (Nat.pos_of_neZero p)) • z = levelRaiseMatrix p • z := by
  apply UpperHalfPlane.ext
  rw [realAffineMatrix_smul, coe_levelRaiseMatrix_smul]
  simp

/-- The upper representative has the exact unitary-to-classical scalar factor. -/
theorem realHecke_upper_scalar (k : ℤ) {p : ℝ} (hp : 0 < p) :
    p ^ (-(1 : ℝ) / 2) * (1 / p) ^ ((k : ℝ) / 2) =
      p ^ (-((k : ℝ) - 1) / 2) * p⁻¹ := by
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_neg_one,
    ← Real.rpow_add hp, ← Real.rpow_add hp]
  congr 1
  ring

/-- The lower representative has the exact unitary-to-classical scalar factor. -/
theorem realHecke_lower_scalar (k : ℤ) {p : ℝ} (hp : 0 < p) :
    p ^ (-(1 : ℝ) / 2) * p ^ ((k : ℝ) / 2) =
      p ^ (-((k : ℝ) - 1) / 2) * p ^ (k - 1) := by
  rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_one,
    ← Real.rpow_add hp, ← Real.rpow_add hp]
  congr 1
  ring

/-- A genuine upper real-group Hecke translate has exactly the original upper summand and common denominator. -/
theorem realWeightLift_hecke_upper (p b : ℕ) [NeZero p] (k : ℤ)
    (f : ℍ → ℂ) (g : SL(2, ℝ)) :
    (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      realWeightLift k f (realAffineMatrix ((b : ℝ) / p)
        (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero p))) * g) =
      (((p : ℝ) ^ (-((k : ℝ) - 1) / 2) : ℝ) : ℂ) * (p : ℂ)⁻¹ *
        f (heckeUpperPoint p b (g • I)) * denom (mapGL ℝ g) I ^ (-k) := by
  have he := congrArg (fun x : ℝ => (x : ℂ))
    (realHecke_upper_scalar k (Nat.cast_pos.mpr (Nat.pos_of_neZero p)))
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast] at he
  rw [realWeightLift_affine, realAffineMatrix_hecke_upper]
  calc
    _ = ((((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        (((1 / (p : ℝ)) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) *
        f (heckeUpperPoint p b (g • I)) * denom (mapGL ℝ g) I ^ (-k) := by ring
    _ = _ := by rw [he]

/-- A genuine lower real-group Hecke translate has exactly the original lower summand and common denominator. -/
theorem realWeightLift_hecke_lower (p : ℕ) [NeZero p] (k : ℤ)
    (f : ℍ → ℂ) (g : SL(2, ℝ)) :
    (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      realWeightLift k f (realAffineMatrix 0 (Nat.cast_pos.mpr (Nat.pos_of_neZero p)) * g) =
      (((p : ℝ) ^ (-((k : ℝ) - 1) / 2) : ℝ) : ℂ) * (p : ℂ) ^ (k - 1) *
        f (levelRaiseMatrix p • (g • I)) * denom (mapGL ℝ g) I ^ (-k) := by
  have he := congrArg (fun x : ℝ => (x : ℂ))
    (realHecke_lower_scalar k (Nat.cast_pos.mpr (Nat.pos_of_neZero p)))
  simp only [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_natCast] at he
  rw [realWeightLift_affine, realAffineMatrix_hecke_lower]
  calc
    _ = ((((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        (((p : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) *
        f (levelRaiseMatrix p • (g • I)) * denom (mapGL ℝ g) I ^ (-k) := by ring
    _ = _ := by rw [he]

end
end Dubon2026
