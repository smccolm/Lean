import Dubon2026.RealPositiveSlashLift
import Dubon2026.RationalCuspSlashSpan
import Dubon2026.AdelicRealFiniteCommute

/-! # The genuine classical function of an original finite-adelic translate -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The actual rational slash function, with its exact determinant-root correction, of an original finite-adelic translate. -/
def finiteAdelicClassicalTranslate (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : ℍ → ℂ :=
  let r := (rationalPositiveGL2ToReal (positiveAdelicGL2Representative N a))⁻¹
  (realPositiveDetRoot r : ℂ) ^ (2 - k) • (f ∣[k] r.val)

/-- The genuine finite-adelic translate restricts to precisely the real lift of the original corrected rational slash function. -/
theorem finiteAdelicClassicalTranslate_real_lift (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (g : SL(2, ℝ)) :
    canonicalAdelicGL2CuspLift N k f (adelicRealSL2Embedding g * rationalAdelicFiniteGL2Embedding a) =
      realWeightLift k (finiteAdelicClassicalTranslate N k f a) g := by
  have hc : rationalAdelicGL2RealFiniteEquiv
      (adelicRealSL2Embedding g * rationalAdelicFiniteGL2Embedding a) = (toGL g, a) := by
    rw [map_mul, ← adelicRealGL2Embedding_toGL, adelicRealGL2Embedding_coordinates,
      rationalAdelicFiniteGL2Embedding_coordinates]
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
  unfold canonicalAdelicGL2CuspLift
  rw [hc]
  change fullAdelicGL2CuspLift N k f (toGLPos g).val a = _
  rw [fullAdelicGL2CuspLift_positive]
  unfold positiveAdelicGL2CuspLift
  rw [realPositiveUnitaryLift_left_slash]
  exact (congrFun (map_smul (realWeightLiftLinear k)
    ((realPositiveDetRoot ((rationalPositiveGL2ToReal (positiveAdelicGL2Representative N a))⁻¹) : ℂ) ^ (2 - k))
    (f ∣[k] ((rationalPositiveGL2ToReal (positiveAdelicGL2Representative N a))⁻¹).val)) g).symm

/-- The original corrected finite-adelic translate belongs to the genuine rational slash span of the original cusp form. -/
theorem finiteAdelicClassicalTranslate_mem_span {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    finiteAdelicClassicalTranslate N k f a ∈ rationalCuspSlashSpan f := by
  apply (rationalCuspSlashSpan f).smul_mem
  apply Submodule.subset_span
  refine ⟨(positiveAdelicGL2Representative N a).val⁻¹, ?_⟩
  change (f : ℍ → ℂ) ∣[k] rationalGL2ToReal ((positiveAdelicGL2Representative N a).val⁻¹) = _
  rw [map_inv]
  rfl

end
end Dubon2026
