import Dubon2026.IntegralMatrixSubringEquiv
import Dubon2026.NumberFieldIntegralMatrixLevel
import Dubon2026.NumberFieldFiniteAdelicMatrixProjection

/-! # Original local integral evaluation of the finite-adelic level

This constructs the actual map to matrices over the original completed
valuation ring. It supplies residue reduction and principal-congruence
refinements of DUB-17's compact open unitary level, with its original
finite-place projection and topology retained.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Evaluation of the original integral finite adeles lands in the original completed integer ring. -/
def numberFieldIntegralAdeleLocalMap (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldIntegralFiniteAdeles K →+* Valued.integer (v.adicCompletion K) :=
  (((RestrictedProduct.evalRingHom _ v : FiniteAdeleRing (𝓞 K) K →+* v.adicCompletion K).comp
    (numberFieldIntegralFiniteAdeles K).subtype)).codRestrict _ (fun x => x.property v)

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The original integral matrix level has its actual local integral matrix image. -/
def numberFieldIntegralMatrixLocalMap (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldIntegralMatrixLevel K ι →* (Matrix ι ι (Valued.integer (v.adicCompletion K)))ˣ :=
  (Units.map (((numberFieldIntegralAdeleLocalMap K v).mapMatrix).comp
    (integralMatrixSubringEquiv (numberFieldIntegralFiniteAdeles K)).toRingHom).toMonoidHom).comp
      (((numberFieldIntegralFiniteAdeles K).matrix (n := ι)).toSubmonoid.unitsEquivUnitsType).toMonoidHom

/-- Forgetting local integrality recovers exactly the original finite-place projection. -/
theorem numberFieldIntegralMatrixLocalMap_compatibility (v : HeightOneSpectrum (𝓞 K))
    (M : numberFieldIntegralMatrixLevel K ι) :
    Units.map (Valued.integer (v.adicCompletion K)).subtype.mapMatrix.toMonoidHom
      (numberFieldIntegralMatrixLocalMap K ι v M) =
        numberFieldFiniteAdelicMatrixProjection K ι v M.val := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  rfl

/-- The original local integral matrix map is continuous. -/
theorem numberFieldIntegralMatrixLocalMap_continuous (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (numberFieldIntegralMatrixLocalMap K ι v) := by
  have hv : Continuous (fun M : numberFieldIntegralMatrixLevel K ι => M.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous (fun M : numberFieldIntegralMatrixLevel K ι => (M.val⁻¹).val) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    apply Continuous.subtype_mk
    exact (RestrictedProduct.continuous_eval v).comp
      ((continuous_apply_apply i j).comp hv)
  · apply continuous_matrix
    intro i j
    apply Continuous.subtype_mk
    exact (RestrictedProduct.continuous_eval v).comp
      ((continuous_apply_apply i j).comp hi)

end
end Dubon2026
