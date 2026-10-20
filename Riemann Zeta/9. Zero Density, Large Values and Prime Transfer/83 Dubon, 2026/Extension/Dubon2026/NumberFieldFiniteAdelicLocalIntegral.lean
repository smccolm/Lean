import Dubon2026.NumberFieldFiniteAdelicLocalGLMap
import Dubon2026.NumberFieldIntegralMatrixLevel

/-! # Integral compatibility of the original local matrix insertion

The actual local integral matrix and its inverse stay integral at every
original finite place after insertion. This is the integral input to
the source split unitary/parabolic level bridge for DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- An original integral local matrix becomes an integral matrix at every original finite place. -/
theorem numberFieldFiniteAdelePlaceMatrix_integral
    (v : HeightOneSpectrum (𝓞 K)) (a : Matrix ι ι (v.adicCompletion K))
    (ha : ∀ i j, a i j ∈ v.adicCompletionIntegers K) :
    ∀ i j w, numberFieldFiniteAdelePlaceMatrix K v a i j w ∈ w.adicCompletionIntegers K := by
  intro i j w
  by_cases hw : w = v
  · subst w
    have he := congrArg (fun M => M i j) (numberFieldFiniteAdelePlaceMatrix_same K v a)
    change numberFieldFiniteAdelePlaceMatrix K v a i j v = a i j at he
    rw [he]
    exact ha i j
  · have he := congrArg (fun M => M i j) (numberFieldFiniteAdelePlaceMatrix_ne K v w hw a)
    change numberFieldFiniteAdelePlaceMatrix K v a i j w =
      (1 : Matrix ι ι (w.adicCompletion K)) i j at he
    rw [he]
    rw [Matrix.one_apply]
    split
    · exact (w.adicCompletionIntegers K).one_mem
    · exact (w.adicCompletionIntegers K).zero_mem

/-- The original integral local general linear group inserts into the original integral adelic matrix level. -/
theorem numberFieldFiniteAdelicLocalGL_integral
    (v : HeightOneSpectrum (𝓞 K))
    (g : (Matrix ι ι (Valued.integer (v.adicCompletion K)))ˣ) :
    numberFieldFiniteAdelicLocalGL K v
      (Units.map (Valued.integer (v.adicCompletion K)).subtype.mapMatrix.toMonoidHom g) ∈
        numberFieldIntegralMatrixLevel K ι := by
  rw [numberFieldIntegralMatrixLevel_mem_iff]
  constructor
  · apply numberFieldFiniteAdelePlaceMatrix_integral K v
    intro i j
    exact (g.val i j).property
  · apply numberFieldFiniteAdelePlaceMatrix_integral K v
    intro i j
    exact ((g⁻¹).val i j).property

/-- The original integral adelic matrix level is exactly integrality of all original local matrix projections and inverses. -/
theorem numberFieldIntegralMatrixLevel_iff_local
    (M : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) :
    M ∈ numberFieldIntegralMatrixLevel K ι ↔
      ∀ v, numberFieldFiniteAdelicMatrixProjection K ι v M ∈
        ((v.adicCompletionIntegers K).matrix (n := ι)).toSubmonoid.units := by
  rw [numberFieldIntegralMatrixLevel_mem_iff]
  constructor
  · rintro ⟨h, hi⟩ v
    exact ⟨fun i j => h i j v, fun i j => hi i j v⟩
  · intro h
    exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩

end
end Dubon2026
