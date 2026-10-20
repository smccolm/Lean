import Dubon2026.CMFiniteAdelicIntegralLevel
import Dubon2026.IntegralFiniteAdelicLocalMatrixMap

/-! # Original integral evaluation on the actual CM unitary level

This is the original continuous integral local matrix map used to pull
back the source parabolic levels to the actual global unitary level in
DUB-17's auxiliary module construction.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original integral unitary level includes in the original integral matrix level. -/
def cmFiniteAdelicIntegralMatrixInclusion (H : Matrix ι ι K) :
    cmFiniteAdelicIntegralLevel K H →* numberFieldIntegralMatrixLevel K ι :=
  (((cmFiniteAdelicUnitaryGroup K H).subtype).comp
    (cmFiniteAdelicIntegralLevel K H).subtype).codRestrict _ (fun M => M.property)

/-- The original integral unitary matrix evaluated in the original local integral matrix group. -/
def cmFiniteAdelicIntegralLocalMap (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) :
    cmFiniteAdelicIntegralLevel K H →* (Matrix ι ι (Valued.integer (v.adicCompletion K)))ˣ :=
  (numberFieldIntegralMatrixLocalMap K ι v).comp (cmFiniteAdelicIntegralMatrixInclusion K H)

/-- Forgetting the integral structures recovers the original finite-place projection on the actual unitary group. -/
theorem cmFiniteAdelicIntegralLocalMap_compatibility (H : Matrix ι ι K)
    (v : HeightOneSpectrum (𝓞 K)) (M : cmFiniteAdelicIntegralLevel K H) :
    Units.map (Valued.integer (v.adicCompletion K)).subtype.mapMatrix.toMonoidHom
      (cmFiniteAdelicIntegralLocalMap K H v M) =
        numberFieldFiniteAdelicMatrixProjection K ι v M.val.val :=
  numberFieldIntegralMatrixLocalMap_compatibility K ι v (cmFiniteAdelicIntegralMatrixInclusion K H M)

/-- The actual integral unitary evaluation is continuous in the original adelic and local topologies. -/
theorem cmFiniteAdelicIntegralLocalMap_continuous (H : Matrix ι ι K)
    (v : HeightOneSpectrum (𝓞 K)) : Continuous (cmFiniteAdelicIntegralLocalMap K H v) := by
  apply (numberFieldIntegralMatrixLocalMap_continuous K ι v).comp
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

end
end Dubon2026
