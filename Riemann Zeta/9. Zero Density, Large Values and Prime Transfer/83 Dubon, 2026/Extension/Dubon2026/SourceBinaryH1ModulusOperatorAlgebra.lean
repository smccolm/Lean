import Dubon2026.SourceBinaryH1TensorChange
import Dubon2026.SourceBinaryH1HeckeAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! DUB-17/18 -> original all-weight adic association -> actual finite-level
Hecke specialization. Use the native tensor base-change homomorphism to
construct the actual finite image of the original integral H1 operator
algebra. This does not require all residual H1 classes to lift integrally. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct

/-- The original integral H1 operator algebra acts on its literal
coefficient-reduced tensor module. -/
def sourceBinaryH1ModulusOperatorMap (Q w N : ℕ) :
    sourceBinaryH1HeckeAlgebra Q w →ₐ[ℤ]
      Module.End (ZMod N) ((ZMod N) ⊗[ℤ]
        groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)) :=
  RingHom.toIntAlgHom {
    toFun T := T.val.baseChange (ZMod N)
    map_one' := LinearMap.baseChange_one ℤ _
    map_mul' T U := LinearMap.baseChange_mul T.val U.val
    map_zero' := LinearMap.baseChange_zero
    map_add' T U := LinearMap.baseChange_add T.val U.val }

/-- The literal finite-precision image of the original integral H1 Hecke algebra. -/
def sourceBinaryH1ModulusOperatorAlgebra (Q w N : ℕ) :=
  (sourceBinaryH1ModulusOperatorMap Q w N).range

/-- At every nonzero modulus, the actual original H1 operator image is finite. -/
theorem sourceBinaryH1ModulusOperatorAlgebra_finite (Q w N : ℕ)
    [NeZero Q] [NeZero N] : Finite (sourceBinaryH1ModulusOperatorAlgebra Q w N) := by
  let M := groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)
  letI : Module.Finite ℤ M := sourceIntegralBinaryH1Finite Q w
  letI : Module.Finite (ZMod N) ((ZMod N) ⊗[ℤ] M) :=
    Module.Finite.base_change ℤ (ZMod N) M
  letI : Finite ((ZMod N) ⊗[ℤ] M) := Module.finite_of_finite (ZMod N)
  letI : Finite (Module.End (ZMod N) ((ZMod N) ⊗[ℤ] M)) :=
    Finite.of_injective (fun T : Module.End (ZMod N) ((ZMod N) ⊗[ℤ] M) =>
      (T : ((ZMod N) ⊗[ℤ] M) → ((ZMod N) ⊗[ℤ] M))) DFunLike.coe_injective
  exact Finite.of_injective
    (fun T : sourceBinaryH1ModulusOperatorAlgebra Q w N => T.val) Subtype.val_injective

/-- A zero tensor-reduced original operator vanishes on every literal
coefficient reduction of an original integral H1 class. -/
theorem sourceBinaryH1ModulusOperatorMap_zero_coefficients (Q w N : ℕ)
    (T : sourceBinaryH1HeckeAlgebra Q w)
    (hT : sourceBinaryH1ModulusOperatorMap Q w N T = 0)
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)) :
    sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w (T.val x) = 0 := by
  have he := LinearMap.congr_fun hT ((1 : ZMod N) ⊗ₜ[ℤ] x)
  change (1 : ZMod N) ⊗ₜ[ℤ] (T.val x) = 0 at he
  have hx := congrArg (sourceBinaryH1TensorChange (ZMod N) Q w) he
  simpa only [sourceBinaryH1TensorChange_tmul, one_smul, map_zero] using hx

end
end Dubon2026
