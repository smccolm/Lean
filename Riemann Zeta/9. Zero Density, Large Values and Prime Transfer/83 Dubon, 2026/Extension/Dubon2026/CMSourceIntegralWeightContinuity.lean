import Dubon2026.CMIntegralInducedTensorContinuity
import Dubon2026.CMSourceIntegralWeight

/-! Continuity of the original source arithmetic coefficient action.
The actual number-field embeddings construct the local integer maps;
their proved continuity and original unitary local evaluations feed the
literal induced tensor action. This removes an assumed continuous
coefficient representation on the automorphy dependency chain for
Dubon's Theorem 2.6 (DUB-17--19). It asserts neither nonzero prescribed
Hecke localization nor the remaining Galois and automorphy theorems.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField ValuativeRel TensorProduct

variable (K E : Type) [Field K] [NumberField K] [IsCMField K] [Field E] [CharZero E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
  (places : Set (HeightOneSpectrum (𝓞 K)))

/-- The actual original unitary coefficient matrices vary continuously in every constructed source embedding. -/
theorem cmSourceIntegralCoefficientMatrixMap_continuous (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Continuous (cmIntegralCoefficientMatrixMap K 𝒪[E]
      (I := IntegralCoefficientEmbeddingIndex K E p hp places)
      (fun i => integralCoefficientEmbeddingPrime K E p hp i.val)
      (fun i => integralCoefficientEmbedding K E p hp i.val) (n + 1) H) := by
  exact cmIntegralCoefficientMatrixMap_continuous K 𝒪[E]
    (I := IntegralCoefficientEmbeddingIndex K E p hp places) _ _ (n + 1) H
    (fun i => integralCoefficientEmbedding_continuous K E p hp i.val)

/-- The source's actual integral unitary tensor coefficient action is jointly continuous in the canonical module topology. -/
theorem cmSourceIntegralWeightRepresentation_continuous (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ)
    [TopologicalSpace (CMSourceIntegralWeight K E p hp places n lam)]
    [IsModuleTopology 𝒪[E] (CMSourceIntegralWeight K E p hp places n lam)] :
    Continuous (fun x : cmFiniteAdelicIntegralLevel K H ×
        CMSourceIntegralWeight K E p hp places n lam =>
      cmSourceIntegralWeightRepresentation K E p hp places n H lam x.1 x.2) := by
  exact cmIntegralInducedTensorRepresentation_continuous K 𝒪[E] E
    (I := IntegralCoefficientEmbeddingIndex K E p hp places) _ _ n H lam
    Subtype.val_injective continuous_subtype_val
    (fun i => integralCoefficientEmbedding_continuous K E p hp i.val)

/-- The source tensor action restricted to the original small auxiliary level is jointly continuous, with its coefficient maps and action continuity derived. -/
theorem cmSourceSmallParabolicWeightRepresentation_continuous {S : Type*}
    (a : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : HeightOneSpectrum (𝓞 K))
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ)
    [TopologicalSpace (CMSourceIntegralWeight K E p hp places n lam)]
    [IsModuleTopology 𝒪[E] (CMSourceIntegralWeight K E p hp places n lam)] :
    Continuous (fun x : cmFiniteAdelicSmallParabolicZero K a n H w ×
        CMSourceIntegralWeight K E p hp places n lam =>
      cmSourceSmallParabolicWeightRepresentation K E p hp places a n H w lam x.1 x.2) := by
  exact cmSmallParabolicInducedTensorRepresentation_continuous K 𝒪[E] E
    (I := IntegralCoefficientEmbeddingIndex K E p hp places) _ _ a n H w lam
    Subtype.val_injective continuous_subtype_val
    (fun i => integralCoefficientEmbedding_continuous K E p hp i.val)

end
end Dubon2026
