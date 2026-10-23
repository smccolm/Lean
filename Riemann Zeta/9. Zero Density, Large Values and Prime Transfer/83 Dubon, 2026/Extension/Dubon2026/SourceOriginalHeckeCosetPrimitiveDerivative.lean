import Dubon2026.SourceOriginalHeckeCosetMultiplicity
import Dubon2026.SourceWeightTwoHeckeCosetTrace
import Dubon2026.SourceWeightTwoAnalyticPrimitive
import Dubon2026.SourcePeriodSlash

/-! DUB-17/18 -> original Picard-period Hecke comparison -> differentiating
the actual Hecke point sum. The literal inverse-dilation point is the
existing positive triangular matrix action. The proved weight-two
Möbius primitive chain rule therefore gives its exact slash derivative.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
variable (N p : ℕ) [NeZero p]

theorem originalHeckeCosetPoint_eq_triangular (τ : ℍ)
    (q : Gamma0 N ⧸ heckeUpperSubgroup N p) :
    originalHeckeCosetPoint N p τ q =
      (heckeTriangularMatrix 1 p 0 * mapGL ℝ q.out.val⁻¹) • τ := by
  apply (MulAction.injective (levelRaiseMatrix p))
  dsimp only
  rw [originalHeckeCosetPoint_dilation, mul_smul, heckeTriangularMatrix_smul]
  apply UpperHalfPlane.ext
  simp only [coe_levelRaiseMatrix_smul, heckeUpperPoint,
    Nat.cast_one, one_mul, Nat.cast_zero, add_zero]
  change ((q.out.val⁻¹ • τ : ℍ) : ℂ) =
    (p : ℂ) * (((q.out.val⁻¹ • τ : ℍ) : ℂ) / p)
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne p)]

variable [NeZero N]

theorem originalHeckeCosetPrimitive_hasDerivAt (hp : Nat.Prime p)
    (f : CuspForm (Gamma0 N) 2) (q : Gamma0 N ⧸ heckeUpperSubgroup N p) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => sourceWeightTwoPrimitive 1 f
      (originalHeckeCosetPoint N p (ofComplex z) q))
      (sourceWeightTwoHeckeCoset hp f q τ) (τ : ℂ) := by
  let g := heckeTriangularMatrix 1 p 0 * mapGL ℝ q.out.val⁻¹
  have hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp only [g, Units.val_mul, Matrix.det_mul,
      ← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one, mul_one]
    exact heckeTriangularMatrix_det_pos 1 p 0
  have hd := sourceHasDerivAt_comp_smul
    (fun z => sourceWeightTwoPrimitive_hasDerivAt f (by norm_num)
      (ModularRatios.one_mem_strictPeriods N) z) hg τ
  have he : (fun z : ℂ => sourceWeightTwoPrimitive 1 f
      (originalHeckeCosetPoint N p (ofComplex z) q)) =
      fun z : ℂ => (sourceWeightTwoPrimitive 1 f ∘ ofComplex) (g • ofComplex z : ℍ) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply, originalHeckeCosetPoint_eq_triangular, g]
  rw [he, sourceWeightTwoHeckeCoset_out, ← SlashAction.slash_mul]
  exact hd

end
end Dubon2026.SourceFunctionField
