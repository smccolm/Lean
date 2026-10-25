import Dubon2026.SourcePrimitiveHeckeAlgebraEvaluation
import Dubon2026.SourcePrimitiveTensorProjectionNonzero

/-! DUB-17/18 -> nonzero primitive rank-two image. The literal arithmetic
projector keeps character value one and every original Hecke scalar identity
in the coefficient extension of the p-adic Hecke algebra. -/
namespace Dubon2026
noncomputable section
open TensorProduct Polynomial
variable (N : ℕ) [NeZero N]
variable {K E T : Type*} [Field K] [Field E] [CommRing T]
variable [Algebra K E] [Algebra K T]

theorem primitiveHeckeAlgebraProjector_character (f : PrimitiveCuspForm N 2)
    (τ : sourcePrimitiveCoefficientField f →+* E)
    (δ : sourceOriginalIntegralHeckeAlgebra N 2 →+* T) (κ : T →ₐ[K] E)
    (hκ : ∀ t, κ (δ t) = τ (sourcePrimitiveFieldHeckeCharacter f t))
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : (sourcePrimitiveCoefficientField f)[X]) (hP : P.eval 0 = 1) :
    coefficientTensorCharacter κ
      (primitiveHeckeAlgebraEvaluation N f τ δ (primitiveGoodTensorProjector N f s P)) = 1 :=
  (primitiveHeckeAlgebraEvaluation_character N f τ δ κ hκ _).trans
    ((congrArg τ (primitiveTensorEigencharacter_projector N f s P hP)).trans (map_one τ))

theorem primitiveHeckeAlgebraProjector_eigen (f : PrimitiveCuspForm N 2)
    (τ : sourcePrimitiveCoefficientField f →+* E)
    (δ : sourceOriginalIntegralHeckeAlgebra N 2 →+* T)
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : (sourcePrimitiveCoefficientField f)[X]) (n : ℕ+)
    (h : ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ] primitiveIntegralHeckeIndex N n) *
      primitiveGoodTensorProjector N f s P =
        sourcePrimitiveFieldCoefficient f n • primitiveGoodTensorProjector N f s P) :
    ((1 : E) ⊗ₜ[K] δ (primitiveIntegralHeckeIndex N n)) *
        primitiveHeckeAlgebraEvaluation N f τ δ (K := K) (primitiveGoodTensorProjector N f s P) =
      τ (sourcePrimitiveFieldCoefficient f n) •
        primitiveHeckeAlgebraEvaluation N f τ δ (K := K) (primitiveGoodTensorProjector N f s P) := by
  have hi := primitiveHeckeAlgebraEvaluation_integral N f τ δ (K := K)
    (primitiveIntegralHeckeIndex N n)
  have he := integerCoefficientExtension_eigen_identity τ
    ((Algebra.TensorProduct.includeRight (R := K) (A := E) (B := T)).toRingHom.comp δ)
    _ _ _ h
  exact (congrArg (fun z => z * primitiveHeckeAlgebraEvaluation N f τ δ (K := K)
    (primitiveGoodTensorProjector N f s P)) hi.symm).trans he

theorem primitiveHeckeAlgebraProjector_scalar (f : PrimitiveCuspForm N 2)
    (τ : sourcePrimitiveCoefficientField f →+* E)
    (δ : sourceOriginalIntegralHeckeAlgebra N 2 →+* T) (κ : T →ₐ[K] E)
    (hκ : ∀ t, κ (δ t) = τ (sourcePrimitiveFieldHeckeCharacter f t))
    (hδ : Algebra.adjoin K (Set.range fun ell : Nat.Primes =>
      δ (primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩)) = ⊤)
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : (sourcePrimitiveCoefficientField f)[X])
    (hH : ∀ n : ℕ+, ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ]
      primitiveIntegralHeckeIndex N n) * primitiveGoodTensorProjector N f s P =
        sourcePrimitiveFieldCoefficient f n • primitiveGoodTensorProjector N f s P) :
    ∀ z : E ⊗[K] T, z *
        primitiveHeckeAlgebraEvaluation N f τ δ (primitiveGoodTensorProjector N f s P) =
      coefficientTensorCharacter κ z •
        primitiveHeckeAlgebraEvaluation N f τ δ (primitiveGoodTensorProjector N f s P) := by
  apply tensor_character_idempotent_scalar
    (fun ell : Nat.Primes => δ (primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩)) hδ
  intro ell
  let n : ℕ+ := ⟨ell.val, ell.property.pos⟩
  have hc := (hκ (primitiveIntegralHeckeIndex N n)).trans
    (congrArg τ (sourcePrimitiveFieldHeckeCharacter_hecke f n))
  exact (primitiveHeckeAlgebraProjector_eigen N f τ δ s P n (hH n)).trans
    (congrArg (fun c => c • primitiveHeckeAlgebraEvaluation N f τ δ (K := K)
      (primitiveGoodTensorProjector N f s P)) hc.symm)

end
end Dubon2026
