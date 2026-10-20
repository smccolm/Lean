import Dubon2026.IntegralHighestTensor
import Dubon2026.CMSourceIntegralWeight

/-! The exact highest tensor in the original arithmetic coefficient action.
The vector and its normalization functional are constructed on the same
literal embedding tensor used by the auxiliary modules. For every original
unitary element whose constructed coefficient matrices are upper Borel,
the actual arithmetic action has the exact product highest-weight character.
This is highest-vector existence and its source action, not uniqueness,
generation, irreducibility or prescribed nonzero Hecke localization.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField ValuativeRel

/-- The actual source coefficient tensor has a normalized nonzero highest vector with the exact original arithmetic Borel action; no highest-vector or coefficient-map witness is supplied. -/
theorem cmSourceIntegralWeight_exists_highestTensor
    (K E : Type) [Field K] [NumberField K] [IsCMField K] [Field E] [CharZero E]
    (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
    [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
    (places : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ)
    (hlam : ∀ i, Antitone (lam i)) :
    let I := IntegralCoefficientEmbeddingIndex K E p hp places
    letI := Fintype.ofFinite I
    let psi := cmIntegralCoefficientMatrixMap K 𝒪[E] (I := I)
      (fun i => integralCoefficientEmbeddingPrime K E p hp i.val)
      (fun i => integralCoefficientEmbedding K E p hp i.val) (n + 1) H
    ∃ z : CMSourceIntegralWeight K E p hp places n lam,
      integralHighestTensorEvaluation 𝒪[E] lam z = 1 ∧ z ≠ 0 ∧
      ∀ (g : cmFiniteAdelicIntegralLevel K H)
        (hg : ∀ i, psi g i ∈ generalLinearBorel 𝒪[E] (n + 1)),
        cmSourceIntegralWeightRepresentation K E p hp places n H lam g z =
          (∏ i : I, ((∏ j : Fin (n + 1),
            generalLinearBorelDiagonalUnit ⟨psi g i, hg i⟩ j ^ lam i j : 𝒪[E]ˣ) : 𝒪[E])) • z := by
  letI := Fintype.ofFinite (IntegralCoefficientEmbeddingIndex K E p hp places)
  refine ⟨integralHighestTensor 𝒪[E] lam hlam,
    integralHighestTensorEvaluation_vector 𝒪[E] lam hlam,
    integralHighestTensor_ne_zero 𝒪[E] lam hlam, ?_⟩
  intro g hg
  let psi := cmIntegralCoefficientMatrixMap K 𝒪[E]
    (I := IntegralCoefficientEmbeddingIndex K E p hp places)
    (fun i => integralCoefficientEmbeddingPrime K E p hp i.val)
    (fun i => integralCoefficientEmbedding K E p hp i.val) (n + 1) H
  have h := integralHighestTensor_action 𝒪[E] lam hlam (fun i => ⟨psi g i, hg i⟩)
  exact h

end
end Dubon2026
