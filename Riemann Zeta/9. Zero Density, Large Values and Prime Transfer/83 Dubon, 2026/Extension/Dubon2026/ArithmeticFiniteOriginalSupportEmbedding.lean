import Dubon2026.ArithmeticAuxiliarySupportRamification
import Dubon2026.OriginalSupportRamificationTransport
import Dubon2026.FiniteGaloisEmbeddingStage

/-! An actual finite field in the auxiliary-support extension, unramified
at the auxiliary primes, embeds in the original-support extension with
exactly the same ambient values. This is the field containment required
to descend the faithful finite representation in Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField BigOperators

/-- The auxiliary unramifiedness conditions place the actual finite
factor field in the original arithmetic extension. The embedding fixes
its literal realization in the chosen algebraic closure. -/
theorem rationalArithmetic_finite_original_support_embedding
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ))
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension b))
    (hQ : ∀ p : Q, Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p.val.val : 𝓞 ℚ)})) :
    ∃ i : F →ₐ[ℚ] rationalUnramifiedExtension a,
      ∀ x : F, (i x : AlgebraicClosure ℚ) = (x.val : AlgebraicClosure ℚ) := by
  letI (α : Algebra ℚ F) : @IsGalois ℚ _ F _ α := by
    have he : F.algebra' = α := Subsingleton.elim _ _
    exact Eq.mp (congrArg (fun β : Algebra ℚ F => @IsGalois ℚ _ F _ β) he) F.isGalois
  exact originalSupport_exists_embedding ((rationalUnramifiedExtension b).val.comp F.val) a
    (rationalArithmetic_finite_field_original_support_ramification a b hb Q hba F hQ)

end
end Dubon2026
