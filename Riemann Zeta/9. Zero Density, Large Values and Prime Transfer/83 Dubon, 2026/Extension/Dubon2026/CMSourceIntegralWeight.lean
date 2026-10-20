import Dubon2026.CMIntegralInducedTensorAction
import Dubon2026.IntegralCoefficientEmbedding

/-! Geraghty's original coefficient tensor from actual field embeddings.
The index is the set of original embeddings inducing the prescribed
coefficient places. The local integer maps are constructed from their
completion extensions, and finite freeness is proved for the literal
integral induced tensor over the original local coefficient integer ring.
CommonCoefficientLocalField constructs an adequate finite common local field,
consumed by CMCommonCoefficientAuxiliary. Prescribed unitary fields/forms
and remaining local choices remain separate source obligations.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField ValuativeRel TensorProduct

variable (K E : Type) [Field K] [NumberField K] [IsCMField K] [Field E] [CharZero E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
  (places : Set (HeightOneSpectrum (𝓞 K)))

/-- The original integral weight module is indexed by the actual field embeddings at the prescribed coefficient places. -/
abbrev CMSourceIntegralWeight (n : ℕ)
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ) :=
  IntegralInducedTensor 𝒪[E] (n + 1) lam

omit [IsCMField K] [IsUniformAddGroup E] in
/-- The original integral tensor coefficient module is finite free over the actual common local field's integer ring. -/
theorem cmSourceIntegralWeight_finite_free (n : ℕ)
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ) :
    Module.Finite 𝒪[E] (CMSourceIntegralWeight K E p hp places n lam) ∧
      Module.Free 𝒪[E] (CMSourceIntegralWeight K E p hp places n lam) :=
  integralLocalInducedTensor_finite_free 𝒪[E] lam

/-- The original integral unitary group acts through the actual completed field embeddings on the literal source tensor module. -/
def cmSourceIntegralWeightRepresentation (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ) :=
  cmIntegralInducedTensorRepresentation K 𝒪[E]
    (I := IntegralCoefficientEmbeddingIndex K E p hp places)
    (fun i => integralCoefficientEmbeddingPrime K E p hp i.val)
    (fun i => integralCoefficientEmbedding K E p hp i.val) (n + 1) H lam

/-- The source tensor action on the original small auxiliary level uses constructed completion embeddings, with no separate local coefficient maps supplied. -/
def cmSourceSmallParabolicWeightRepresentation {S : Type*}
    (a : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : HeightOneSpectrum (𝓞 K))
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ) :=
  cmSmallParabolicInducedTensorRepresentation K 𝒪[E]
    (I := IntegralCoefficientEmbeddingIndex K E p hp places)
    (fun i => integralCoefficientEmbeddingPrime K E p hp i.val)
    (fun i => integralCoefficientEmbedding K E p hp i.val) a n H w lam

/-- On actual pure tensors, the arithmetic action is the tensor of the original right translations evaluated at the constructed local coefficient embeddings. -/
theorem cmSourceIntegralWeightRepresentation_tprod (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ)
    (g : cmFiniteAdelicIntegralLevel K H)
    (f : ∀ i, generalLinearIntegralInducedSubmodule 𝒪[E] (n + 1) (lam i)) :
    cmSourceIntegralWeightRepresentation K E p hp places n H lam g (PiTensorProduct.tprod 𝒪[E] f) =
      PiTensorProduct.tprod 𝒪[E] (fun i =>
        generalLinearIntegralInducedRepresentation 𝒪[E] (n + 1) (lam i)
          (GeneralLinearGroup.map (integralCoefficientEmbedding K E p hp i.val)
            (cmFiniteAdelicIntegralLocalMap K H (integralCoefficientEmbeddingPrime K E p hp i.val) g))
          (f i)) :=
  cmIntegralInducedTensorRepresentation_tprod K 𝒪[E]
    (I := IntegralCoefficientEmbeddingIndex K E p hp places) _ _ (n + 1) H lam g f

end
end Dubon2026
