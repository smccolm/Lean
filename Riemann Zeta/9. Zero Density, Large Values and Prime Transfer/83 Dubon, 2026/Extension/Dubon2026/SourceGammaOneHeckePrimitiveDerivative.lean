import Dubon2026.SourceGammaOneWeightTwoHeckeCosets
import Dubon2026.SourceGammaOneModularRatios
import Dubon2026.SourceWeightTwoAnalyticPrimitive
import Dubon2026.SourcePeriodSlash

/-! DUB17/18 -> actual Gamma1 Picard/H1 Hecke comparison -> endpoint
primitive trace. The point is the literal inverse-dilation image of the
inverse coset representative. The native weight-two chain rule gives the
exact derivative, with no primitive or normalization hypothesis. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
variable (M d : ℕ) [NeZero d]

/-- The actual inverse-dilation point of a Gamma1 upper-subgroup coset representative. -/
def heckeCosetPoint (τ : ℍ) (q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) : ℍ :=
  (levelRaiseMatrix d)⁻¹ • (q.out.val⁻¹ • τ)

theorem heckeCosetPoint_dilation (τ : ℍ) (q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) :
    levelRaiseMatrix d • heckeCosetPoint M d τ q = q.out.val⁻¹ • τ := by
  exact smul_inv_smul (levelRaiseMatrix d) (q.out.val⁻¹ • τ)

theorem heckeCosetPoint_eq_triangular (τ : ℍ) (q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) :
    heckeCosetPoint M d τ q = (heckeTriangularMatrix 1 d 0 * mapGL ℝ q.out.val⁻¹) • τ := by
  apply (MulAction.injective (levelRaiseMatrix d))
  dsimp only
  rw [heckeCosetPoint_dilation, mul_smul, heckeTriangularMatrix_smul]
  apply UpperHalfPlane.ext
  simp only [coe_levelRaiseMatrix_smul, heckeUpperPoint,
    Nat.cast_one, one_mul, Nat.cast_zero, add_zero]
  change ((q.out.val⁻¹ • τ : ℍ) : ℂ) =
    (d : ℂ) * (((q.out.val⁻¹ • τ : ℍ) : ℂ) / d)
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne d)]

variable [NeZero M]

theorem heckeCosetPrimitive_hasDerivAt
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2)
    (q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => sourceWeightTwoPrimitive 1 f (heckeCosetPoint M d (ofComplex z) q))
      (sourceGammaOneWeightTwoHeckeCoset M d f q τ) (τ : ℂ) := by
  let g := heckeTriangularMatrix 1 d 0 * mapGL ℝ q.out.val⁻¹
  have hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp only [g, Units.val_mul, Matrix.det_mul,
      ← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one, mul_one]
    exact heckeTriangularMatrix_det_pos 1 d 0
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  have hd := sourceHasDerivAt_comp_smul
    (fun z => sourceWeightTwoPrimitive_hasDerivAt f one_pos (hper hT) z) hg τ
  have he : (fun z : ℂ => sourceWeightTwoPrimitive 1 f (heckeCosetPoint M d (ofComplex z) q)) =
      fun z : ℂ => (sourceWeightTwoPrimitive 1 f ∘ ofComplex) (g • ofComplex z : ℍ) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply, heckeCosetPoint_eq_triangular, g]
  rw [he, sourceGammaOneWeightTwoHeckeCoset_out, ← SlashAction.slash_mul]
  exact hd

private local instance : Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M d
  exact Fintype.ofFinite _

theorem heckePrimitiveTrace_hasDerivAt
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
      sourceWeightTwoPrimitive 1 f (heckeCosetPoint M d (ofComplex z) q))
      (∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
        sourceGammaOneWeightTwoHeckeCoset M d f q τ) (τ : ℂ) :=
  HasDerivAt.fun_sum (u := Finset.univ) (fun q _ => heckeCosetPrimitive_hasDerivAt M d f q τ)

end
end Dubon2026.SourceFunctionField.GammaOne
