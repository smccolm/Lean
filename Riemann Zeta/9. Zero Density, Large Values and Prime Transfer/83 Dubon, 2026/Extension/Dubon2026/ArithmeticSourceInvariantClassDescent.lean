import Dubon2026.ArithmeticFiniteClassHomGaloisDescent
import Dubon2026.OriginalInvariantHomEvaluation
import Dubon2026.ArithmeticSourceHomContinuity

/-! # Actual invariant source-class Hom descends to a finite class quotient

The continuous source Hom exact sequence returns invariant source-class
coefficients. Literal evaluation and the already proved source-to-full
class comparison turn those actual coefficients into the degree-zero
finite-stage term of DUB-17's class/Ext comparison. No principalization,
stage representative or equivariance hypothesis is added.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(P/K)) [Finite B]

/-- An invariant returned by the actual source-class Hom sequence has a
finite-Galois equivariant full-class representative above the same source
field, whose values are exactly the original source-class comparison. -/
theorem arithmeticSourceInvariantClass_exists_finite_descent
    (w : (arithmeticSourceClassHomRep K Ω a ha
      (Rep.res (AlgEquiv.restrictNormalHom P :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) B)).ρ.invariants) :
    ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hPN : P ≤ N,
        letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
        ∃ η : Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) B ⟶
            arithmeticClassesModOutsideStageRep K Ω a ha N,
          ∀ b : B, (coefficientRepresentationColimitOf _
            (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) N).hom (η.hom b) =
              (arithmeticSourceClassColimitComparison K Ω a ha).hom
                ((show B →ₗ[ℤ] arithmeticSPlaceClassColimitRep K Ω a ha from w.val) b) := by
  let A := Rep.res (AlgEquiv.restrictNormalHom P :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) B
  let S := arithmeticSPlaceClassColimitRep K Ω a ha
  let φ : A ⟶ arithmeticClassesModOutsideColimitRep K Ω a ha :=
    originalInvariantHomMorphism A S w ≫ arithmeticSourceClassColimitComparison K Ω a ha
  obtain ⟨N, hPN, η, hη⟩ := arithmeticFiniteClassHom_exists_galois_descent K Ω a ha P B φ
  refine ⟨N, hPN, η, ?_⟩
  intro b
  exact hη b

end
end Dubon2026
