import Dubon2026.SourcePrimitiveHeckeAlgebraProjector
import Dubon2026.SourceCharacterIdempotentRankTwo
import Dubon2026.SourceIntegerCoefficientRankTwo
import Dubon2026.SourceRankTwoCharacterRange

/-! DUB-17/18 -> primitive determinant -> the nonzero prescribed rank-two
image. The actual arithmetic projector supplies the character normalization
and all eigenrelations; only the explicitly displayed algebra map and its
generator/character compatibility are upstream inputs here. -/
namespace Dubon2026
noncomputable section
open TensorProduct Polynomial
variable (N : ℕ) [NeZero N]
variable {K E T : Type*} [Field K] [Field E] [CommRing T]
variable [Algebra K E] [Algebra K T]

theorem exists_primitive_heckeAction_rankTwo {V : Type*} [AddCommGroup V] [Module K V]
    (f : PrimitiveCuspForm N 2)
    (τ : sourcePrimitiveCoefficientField f →+* E)
    (θ : sourceOriginalIntegralHeckeAlgebra N 2 →+* Module.End K V)
    (δ : sourceOriginalIntegralHeckeAlgebra N 2 →+* T) (κ : T →ₐ[K] E)
    (hκ : ∀ t, κ (δ t) = τ (sourcePrimitiveFieldHeckeCharacter f t))
    (hδ : Algebra.adjoin K (Set.range fun ell : Nat.Primes =>
      δ (primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩)) = ⊤)
    (he : ∃ e : V ≃ₗ[K] (Fin 2 → T),
      ∀ (t : sourceOriginalIntegralHeckeAlgebra N 2) (v : V),
        e (θ t v) = fun i => δ t * e v i) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N})
      (P : (sourcePrimitiveCoefficientField f)[X]), P.eval 0 = 1 ∧
      IsIdempotentElem (primitiveGoodTensorProjector N f s P) ∧
      Nonempty ((integerCoefficientEndExtension τ
        ((Module.End.baseChangeHom K E V).toRingHom.comp θ)
          (primitiveGoodTensorProjector N f s P)).range ≃ₗ[E] (Fin 2 → E)) := by
  obtain ⟨s, P, hP, _, hIdem, hH⟩ := exists_primitive_tensor_projection N f
  obtain ⟨e, he⟩ := exists_integerCoefficient_rankTwo_coordinates τ θ δ he
  have hc := primitiveHeckeAlgebraProjector_character N f τ δ κ hκ s P hP
  have hs := primitiveHeckeAlgebraProjector_scalar N f τ δ κ hκ hδ s P hH
  exact ⟨s, P, hP, hIdem,
    ⟨rankTwoCharacterRangeEquiv e _ _ (coefficientTensorCharacter κ) hc hs
      (he (primitiveGoodTensorProjector N f s P))⟩⟩

end
end Dubon2026
