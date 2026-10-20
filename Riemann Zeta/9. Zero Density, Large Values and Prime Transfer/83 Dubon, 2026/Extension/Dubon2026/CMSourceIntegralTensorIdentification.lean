import Dubon2026.SourceIntegralTensorGenericFibreAction
import Dubon2026.CMSourceIntegralFactorIdentification

/-! The original arithmetic coefficient tensor as the required highest-weight lattice.
The generic-fibre tensor and its arithmetic action are constructed from the
same original embedding maps. The comparison preserves the actual highest
tensor, and every field factor has the proved original irreducibility.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField ValuativeRel TensorProduct

variable (K E : Type) [Field K] [NumberField K] [IsCMField K] [Field E] [CharZero E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
  (places : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ)
  (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
  (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ)

/-- The original field tensor action uses the same completed source embeddings, followed by their actual inclusion into the coefficient field. -/
def cmSourceFieldWeightRepresentation :
    Representation E (cmFiniteAdelicIntegralLevel K H)
      (IntegralInducedTensor E (n + 1) lam) :=
  cmIntegralInducedTensorRepresentation K E
    (I := IntegralCoefficientEmbeddingIndex K E p hp places)
    (fun i => integralCoefficientEmbeddingPrime K E p hp i.val)
    (fun i => (algebraMap 𝒪[E] E).comp (integralCoefficientEmbedding K E p hp i.val))
    (n + 1) H lam

/-- The exact original arithmetic integral coefficient tensor has the tensor of its original irreducible highest-weight field factors as generic fibre, preserving its normalized highest tensor and every actual unitary group operator. -/
theorem cmSourceIntegralWeight_genericFibre_identification
    (hlam : ∀ i, Antitone (lam i)) :
    ∃ e : E ⊗[𝒪[E]] CMSourceIntegralWeight K E p hp places n lam ≃ₗ[E]
        IntegralInducedTensor E (n + 1) lam,
      (∀ i, Representation.IsIrreducible
        (generalLinearIntegralInducedRepresentation E (n + 1) (lam i))) ∧
      e ((1 : E) ⊗ₜ[𝒪[E]] integralHighestTensor 𝒪[E] lam hlam) =
        integralHighestTensor E lam hlam ∧
      ∀ (g : cmFiniteAdelicIntegralLevel K H)
        (z : E ⊗[𝒪[E]] CMSourceIntegralWeight K E p hp places n lam),
        e ((cmSourceIntegralWeightRepresentation K E p hp places n H lam g).baseChange E z) =
          cmSourceFieldWeightRepresentation K E p hp places n H lam g (e z) := by
  refine ⟨sourceIntegralTensorGenericFibreEquiv 𝒪[E] E lam hlam,
    (fun i => sourceInduced_isIrreducible E (lam i) (hlam i)),
    sourceIntegralTensorGenericFibreEquiv_highest 𝒪[E] E lam hlam, ?_⟩
  intro g z
  exact sourceIntegralTensorGenericFibreEquiv_action 𝒪[E] E lam hlam
    (cmIntegralCoefficientMatrixMap K 𝒪[E]
      (I := IntegralCoefficientEmbeddingIndex K E p hp places)
      (fun i => integralCoefficientEmbeddingPrime K E p hp i.val)
      (fun i => integralCoefficientEmbedding K E p hp i.val) (n + 1) H g) z

end
end Dubon2026
