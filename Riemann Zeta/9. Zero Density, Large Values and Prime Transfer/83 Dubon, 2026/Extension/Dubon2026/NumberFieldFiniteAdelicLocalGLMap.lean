import Dubon2026.NumberFieldFiniteAdelicLocalGL

/-! # The original local insertion is a group section

This is the required group map for inserting paired conjugate-place
factors into DUB-17's original unitary auxiliary levels.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Original finite-place projections separate original invertible adelic matrices. -/
theorem numberFieldFiniteAdelicGL_ext
    {a b : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ}
    (h : ∀ v, numberFieldFiniteAdelicMatrixProjection K ι v a =
      numberFieldFiniteAdelicMatrixProjection K ι v b) : a = b := by
  apply Units.ext
  apply numberFieldFiniteAdeleMatrix_ext K
  intro v
  exact congrArg Units.val (h v)

/-- Local insertion preserves the multiplication in the original general linear group. -/
theorem numberFieldFiniteAdelicLocalGL_mul (v : HeightOneSpectrum (𝓞 K))
    (a b : GeneralLinearGroup ι (v.adicCompletion K)) :
    numberFieldFiniteAdelicLocalGL K v (a * b) =
      numberFieldFiniteAdelicLocalGL K v a * numberFieldFiniteAdelicLocalGL K v b := by
  apply numberFieldFiniteAdelicGL_ext K
  intro w
  rw [map_mul]
  change GeneralLinearGroup.map (numberFieldFiniteAdelePlace K w) _ =
    GeneralLinearGroup.map (numberFieldFiniteAdelePlace K w) _ *
      GeneralLinearGroup.map (numberFieldFiniteAdelePlace K w) _
  by_cases hw : w = v
  · subst w
    rw [numberFieldFiniteAdelicLocalGL_same, numberFieldFiniteAdelicLocalGL_same,
      numberFieldFiniteAdelicLocalGL_same]
  · rw [numberFieldFiniteAdelicLocalGL_ne K v w hw,
      numberFieldFiniteAdelicLocalGL_ne K v w hw,
      numberFieldFiniteAdelicLocalGL_ne K v w hw, one_mul]

/-- The original local-to-adelic insertion as a genuine group homomorphism. -/
def numberFieldFiniteAdelicLocalGLHom (v : HeightOneSpectrum (𝓞 K)) :
    GeneralLinearGroup ι (v.adicCompletion K) →*
      GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K) :=
  MonoidHom.mk' (numberFieldFiniteAdelicLocalGL K v)
    (numberFieldFiniteAdelicLocalGL_mul K v)

/-- The insertion is a section of the original finite-place matrix projection. -/
theorem numberFieldFiniteAdelicLocalGLHom_section (v : HeightOneSpectrum (𝓞 K))
    (a : GeneralLinearGroup ι (v.adicCompletion K)) :
    numberFieldFiniteAdelicMatrixProjection K ι v (numberFieldFiniteAdelicLocalGLHom K v a) = a :=
  numberFieldFiniteAdelicLocalGL_same K v a

end
end Dubon2026
