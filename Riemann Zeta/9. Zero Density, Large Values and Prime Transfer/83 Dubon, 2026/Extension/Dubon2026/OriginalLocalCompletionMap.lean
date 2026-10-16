import Dubon2026.OriginalLocalEmbeddingUniformity

/-! # The original prime completion embeds as a closed field

Extend the literal number-field embedding using the proved adic
uniformity. This constructs the actual completion map, retaining its
original field values, on DUB-17's orbit/completion comparison route.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain UniformSpace Topology
open scoped NumberField ValuativeRel

variable (L E : Type) [Field L] [NumberField L] [Field E] [Algebra L E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]

/-- The original local-field uniformity is complete by the native compatible-norm theorem. -/
local instance originalLocalEmbeddingTargetComplete : CompleteSpace E := localFieldOriginalNorm_complete E

/-- Extend the actual original embedding to its genuine induced prime completion. -/
def originalLocalCompletionMap : (originalLocalEmbeddingPrime L E p hp).adicCompletion L →+* E :=
  Completion.extensionHom (originalLocalEmbeddingAdicMap L E p hp)
    (originalLocalEmbeddingAdicMap_uniformContinuous L E p hp).continuous

/-- The actual completion map preserves precisely the original embedded field element. -/
theorem originalLocalCompletionMap_algebraMap (x : L) :
    originalLocalCompletionMap L E p hp
        (algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L) x) =
      algebraMap L E x := by
  change Completion.extensionHom _ _
    (↑(WithVal.toVal ((originalLocalEmbeddingPrime L E p hp).valuation L) x) :
      (originalLocalEmbeddingPrime L E p hp).adicCompletion L) = _
  rw [Completion.extensionHom_coe]
  rfl

/-- The completed original embedding is continuous in the original topologies. -/
theorem originalLocalCompletionMap_continuous : Continuous (originalLocalCompletionMap L E p hp) :=
  Completion.continuous_extension

/-- Completion preserves the proved original adic uniformity comparison. -/
theorem originalLocalCompletionMap_isUniformInducing :
    IsUniformInducing (originalLocalCompletionMap L E p hp) :=
  Completion.isUniformInducing_extension (originalLocalEmbeddingAdicMap_isUniformInducing L E p hp)

/-- The genuine induced prime completion is embedded as a closed subfield of the original local field. -/
theorem originalLocalCompletionMap_isClosedEmbedding :
    IsClosedEmbedding (originalLocalCompletionMap L E p hp) :=
  (show IsUniformEmbedding (originalLocalCompletionMap L E p hp) from
    ⟨originalLocalCompletionMap_isUniformInducing L E p hp,
      (originalLocalCompletionMap L E p hp).injective⟩).isClosedEmbedding

end
end Dubon2026
