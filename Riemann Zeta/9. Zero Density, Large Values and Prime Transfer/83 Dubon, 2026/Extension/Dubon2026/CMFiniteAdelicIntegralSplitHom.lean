import Dubon2026.CMFiniteAdelicLocalSplitIntegral
import Dubon2026.CMFiniteAdelicIntegralLocalFaithful

/-! # The actual integral split-place unitary section

The original local integral matrix group is realized inside the original
global integral unitary level. The proved section of integral evaluation
will transfer the source parabolic quotient without supplying an
independent global level-quotient realization in DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField
attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original form and its inverse are integral at the actual CM-conjugate place. -/
def cmFiniteAdelicFormIntegralAtConjugate
    (H : (Matrix ι ι K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  numberFieldFiniteAdelicMatrixProjection K ι (cmFinitePlaceConjugation K v)
    (Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H) ∈
      (((cmFinitePlaceConjugation K v).adicCompletionIntegers K).matrix (n := ι)).toSubmonoid.units

/-- The original integral local matrix group maps into the actual integral unitary level at the pair of distinct conjugate places. -/
def cmFiniteAdelicIntegralSplitHom
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (hlocal : cmFiniteAdelicFormIntegralAtConjugate K H v) :
    (Matrix ι ι (Valued.integer (v.adicCompletion K)))ˣ →* cmFiniteAdelicIntegralLevel K H.val :=
  ((cmFiniteAdelicLocalSplitHom K H hH v hv).comp
    (Units.map (Valued.integer (v.adicCompletion K)).subtype.mapMatrix.toMonoidHom)).codRestrict _
      (cmFiniteAdelicLocalSplitElement_integral K H hH v hv hlocal)


/-- The original ambient matrix projection recovers the inserted integral matrix after its original inclusion. -/
theorem cmFiniteAdelicIntegralSplitHom_projection
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (hlocal : cmFiniteAdelicFormIntegralAtConjugate K H v)
    (g : (Matrix ι ι (Valued.integer (v.adicCompletion K)))ˣ) :
    numberFieldFiniteAdelicMatrixProjection K ι v
      (cmFiniteAdelicIntegralSplitHom K H hH v hv hlocal g).val.val =
        Units.map (Valued.integer (v.adicCompletion K)).subtype.mapMatrix.toMonoidHom g := by
  simp only [cmFiniteAdelicIntegralSplitHom, MonoidHom.codRestrict_apply, MonoidHom.comp_apply]
  exact cmFiniteAdelicLocalSplitHom_section K H hH v hv _

/-- Original integral evaluation recovers every original integral matrix from its unitary insertion. -/
theorem cmFiniteAdelicIntegralSplitHom_section
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (hlocal : cmFiniteAdelicFormIntegralAtConjugate K H v)
    (g : (Matrix ι ι (Valued.integer (v.adicCompletion K)))ˣ) :
    cmFiniteAdelicIntegralLocalMap K H.val v (cmFiniteAdelicIntegralSplitHom K H hH v hv hlocal g) = g :=
  cmFiniteAdelicIntegralLocalMap_eq_of_projection K H.val v _ g
    (cmFiniteAdelicIntegralSplitHom_projection K H hH v hv hlocal g)

/-- The actual global integral unitary level surjects onto the original integral matrix group at every permitted split place. -/
theorem cmFiniteAdelicIntegralLocalMap_surjective
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (hlocal : cmFiniteAdelicFormIntegralAtConjugate K H v) :
    Function.Surjective (cmFiniteAdelicIntegralLocalMap K H.val v) :=
  fun g => ⟨cmFiniteAdelicIntegralSplitHom K H hH v hv hlocal g,
    cmFiniteAdelicIntegralSplitHom_section K H hH v hv hlocal g⟩

end
end Dubon2026
