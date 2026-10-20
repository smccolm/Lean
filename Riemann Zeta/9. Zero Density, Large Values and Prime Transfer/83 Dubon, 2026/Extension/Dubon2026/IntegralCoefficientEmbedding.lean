import Dubon2026.OriginalLocalCompletionValuation
import Mathlib.FieldTheory.Finiteness

/-! The actual integral coefficient embedding attached to a number-field
embedding in the common local coefficient field. The existing completion
extension and valuation comparison construct the map on local integers;
integer preservation is derived, not assumed. This supplies precisely
the coefficient maps used in Geraghty Definition 2.2.3's tensor action.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField ValuativeRel

variable (K E : Type) [Field K] [NumberField K] [Field E] [CharZero E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]

/-- The genuine finite place induced by the specified original number-field embedding. -/
def integralCoefficientEmbeddingPrime (τ : K →ₐ[ℚ] E) : HeightOneSpectrum (𝓞 K) :=
  letI : Algebra K E := τ.toRingHom.toAlgebra
  originalLocalEmbeddingPrime K E p hp

/-- The actual completion embedding restricted to its original integer ring, with integral preservation proved by the existing valuation comparison. -/
def integralCoefficientEmbedding (τ : K →ₐ[ℚ] E) :
    Valued.integer ((integralCoefficientEmbeddingPrime K E p hp τ).adicCompletion K) →+* 𝒪[E] := by
  letI : Algebra K E := τ.toRingHom.toAlgebra
  exact ((originalLocalCompletionMap K E p hp).comp
    (Valued.integer ((originalLocalEmbeddingPrime K E p hp).adicCompletion K)).subtype).codRestrict
      (ValuativeRel.valuation E).integer
      (fun x => (originalLocalCompletionMap_le_one_iff K E p hp x.val).mp x.property)

/-- The constructed integral coefficient map is literally the original completed field embedding on every integer. -/
theorem integralCoefficientEmbedding_coe (τ : K →ₐ[ℚ] E)
    (x : Valued.integer ((integralCoefficientEmbeddingPrime K E p hp τ).adicCompletion K)) :
    letI : Algebra K E := τ.toRingHom.toAlgebra
    (integralCoefficientEmbedding K E p hp τ x : E) = originalLocalCompletionMap K E p hp x.val :=
  rfl

/-- The original integer embedding is continuous in its native subspace topologies. -/
theorem integralCoefficientEmbedding_continuous (τ : K →ₐ[ℚ] E) :
    Continuous (integralCoefficientEmbedding K E p hp τ) := by
  letI : Algebra K E := τ.toRingHom.toAlgebra
  exact ((originalLocalCompletionMap_continuous K E p hp).comp continuous_subtype_val).subtype_mk _

/-- The source index consists of the actual embeddings inducing the prescribed set of coefficient places. -/
def IntegralCoefficientEmbeddingIndex (places : Set (HeightOneSpectrum (𝓞 K))) :=
  {τ : K →ₐ[ℚ] E // integralCoefficientEmbeddingPrime K E p hp τ ∈ places}

/-- The original coefficient-embedding index is finite because the number field has finite degree. -/
instance integralCoefficientEmbeddingIndexFinite (places : Set (HeightOneSpectrum (𝓞 K))) :
    Finite (IntegralCoefficientEmbeddingIndex K E p hp places) := by
  unfold IntegralCoefficientEmbeddingIndex
  infer_instance

end
end Dubon2026
