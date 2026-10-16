import Dubon2026.OriginalLocalCompletionMap
import Dubon2026.OriginalLocalScalarContinuity

/-! # The actual completion fills the generated local field

The image of the original completion is closed. Density of the rational
field puts the entire original rational-prime completion in that image.
The proved field-generation input then gives surjectivity, the precise
completion-comparison step on DUB-17's number-field reciprocity route.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain UniformSpace Topology
open scoped NumberField ValuativeRel

variable (L E : Type) [Field L] [NumberField L] [Field E] [Algebra L E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]

/-- The original rational-prime completion lies in the completed original field image. -/
theorem originalLocalCompletionMap_base_mem (x : rationalPrimeLocalField p hp) :
    algebraMap (rationalPrimeLocalField p hp) E x ∈
      (originalLocalCompletionMap L E p hp).fieldRange := by
  refine Completion.induction_on (p := fun x : rationalPrimeLocalField p hp =>
    algebraMap (rationalPrimeLocalField p hp) E x ∈
      (originalLocalCompletionMap L E p hp).fieldRange) x ?_ ?_
  · exact (originalLocalCompletionMap_isClosedEmbedding L E p hp).isClosed_range.preimage
      (originalLocalScalar_continuous (rationalPrimeLocalField p hp) E)
  · intro q
    refine ⟨algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L)
      (algebraMap ℚ L q.ofVal), ?_⟩
    change originalLocalCompletionMap L E p hp
      (algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L)
        (algebraMap ℚ L q.ofVal)) = _
    rw [originalLocalCompletionMap_algebraMap]
    change algebraMap L E (algebraMap ℚ L q.ofVal) =
      algebraMap (rationalPrimeLocalField p hp) E
        (algebraMap ℚ (rationalPrimeLocalField p hp) q.ofVal)
    simp only [eq_ratCast, map_ratCast]

/-- Generation by the actual local base and global field makes the original completion map onto. -/
theorem originalLocalCompletionMap_surjective
    (hgen : (algebraMap (rationalPrimeLocalField p hp) E).fieldRange ⊔
      (algebraMap L E).fieldRange = ⊤) :
    Function.Surjective (originalLocalCompletionMap L E p hp) := by
  apply RingHom.fieldRange_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  apply sup_le
  · rintro _ ⟨x, rfl⟩
    exact originalLocalCompletionMap_base_mem L E p hp x
  · rintro _ ⟨x, rfl⟩
    exact ⟨algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L) x,
      originalLocalCompletionMap_algebraMap L E p hp x⟩

/-- The original finite-prime completion is identified with the actual generated local field. -/
def originalLocalCompletionEquiv
    (hgen : (algebraMap (rationalPrimeLocalField p hp) E).fieldRange ⊔
      (algebraMap L E).fieldRange = ⊤) :
    (originalLocalEmbeddingPrime L E p hp).adicCompletion L ≃+* E :=
  RingEquiv.ofBijective (originalLocalCompletionMap L E p hp)
    ⟨(originalLocalCompletionMap L E p hp).injective,
      originalLocalCompletionMap_surjective L E p hp hgen⟩

/-- The comparison preserves the actual original embedded field elements. -/
theorem originalLocalCompletionEquiv_algebraMap
    (hgen : (algebraMap (rationalPrimeLocalField p hp) E).fieldRange ⊔
      (algebraMap L E).fieldRange = ⊤) (x : L) :
    originalLocalCompletionEquiv L E p hp hgen
      (algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L) x) =
        algebraMap L E x :=
  originalLocalCompletionMap_algebraMap L E p hp x

end
end Dubon2026
