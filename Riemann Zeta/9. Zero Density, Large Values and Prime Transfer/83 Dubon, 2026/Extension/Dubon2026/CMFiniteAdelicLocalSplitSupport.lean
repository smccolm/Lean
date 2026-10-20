import Dubon2026.CMFiniteAdelicIntegralSplitHom

/-! # Support of the original paired-place unitary section

The constructed unitary element is the identity away from the original
pair of CM-conjugate places. This is the exact independence needed to
realize simultaneous source auxiliary levels for DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField
attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original unitary insertion has no component outside the specified CM-conjugate pair. -/
theorem cmFiniteAdelicLocalSplitElement_ne
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (w : HeightOneSpectrum (𝓞 K)) (hw : w ≠ v) (hwc : w ≠ cmFinitePlaceConjugation K v)
    (g : GeneralLinearGroup ι (v.adicCompletion K)) :
    numberFieldFiniteAdelicMatrixProjection K ι w
      (cmFiniteAdelicLocalSplitElement K H hH v hv g).val = 1 := by
  change numberFieldFiniteAdelicMatrixProjection K ι w
    (numberFieldFiniteAdelicLocalGL K v g *
      ((Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H)⁻¹ *
        star (numberFieldFiniteAdelicLocalGL K v g) *
          Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H)⁻¹) = 1
  simp only [map_mul, map_inv, cmFiniteAdelicLocalGL_star_ne K v w hwc,
    mul_one, inv_mul_cancel, inv_one]
  exact numberFieldFiniteAdelicLocalGL_ne K v w hw g

/-- The integral unitary section leaves every other original local integral matrix component unchanged at one. -/
theorem cmFiniteAdelicIntegralSplitHom_ne
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (hlocal : cmFiniteAdelicFormIntegralAtConjugate K H v)
    (w : HeightOneSpectrum (𝓞 K)) (hw : w ≠ v) (hwc : w ≠ cmFinitePlaceConjugation K v)
    (g : (Matrix ι ι (Valued.integer (v.adicCompletion K)))ˣ) :
    cmFiniteAdelicIntegralLocalMap K H.val w (cmFiniteAdelicIntegralSplitHom K H hH v hv hlocal g) = 1 := by
  apply cmFiniteAdelicIntegralLocalMap_eq_of_projection
  rw [map_one]
  simp only [cmFiniteAdelicIntegralSplitHom, MonoidHom.codRestrict_apply, MonoidHom.comp_apply]
  exact cmFiniteAdelicLocalSplitElement_ne K H hH v hv w hw hwc _

end
end Dubon2026
