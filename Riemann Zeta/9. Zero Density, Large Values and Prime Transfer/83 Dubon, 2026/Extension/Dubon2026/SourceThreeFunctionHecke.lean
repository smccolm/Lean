import Dubon2026.SourceThreeFunctionAction

/-! Exact full-Hecke comparisons for the characteristic-three odd twist.
DUB-17/18 -> residual modular Galois association -> all-prime weight-two
reduction -> characteristic-three odd twist. Native coefficient naturality
and scalar compatibility give the required original H1 operators directly.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory groupCohomology

variable (F : Type) [Field F] (Q : ℕ) (h3Q : 3 ∣ Q)

/-- The original coefficient difference induces the native H1 endomorphism. -/
def sourceThreeFunctionDifferenceH1 :
    Module.End F (H1 (sourceAffineFunctionRep 3 Q F h3Q)) :=
  ((groupCohomology.functor F (Gamma0 Q) 1).map
    (sourceThreeFunctionDifferenceMap F Q h3Q)).hom

/-- The actual constant coefficient inclusion induces its native H1 map. -/
def sourceThreeConstantH1 :
    H1 (Rep.trivial F (Gamma0 Q) F) →ₗ[F] H1 (sourceAffineFunctionRep 3 Q F h3Q) :=
  ((groupCohomology.functor F (Gamma0 Q) 1).map
    (sourceThreeConstantMap F Q h3Q)).hom

private local instance threePrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- The actual constant coefficient inclusion preserves every full Hecke eigenvalue. -/
theorem sourceThreeConstantH1_hecke (ell : sourceBinaryHeckePrime Q)
    (x : H1 (Rep.trivial F (Gamma0 Q) F)) :
    sourceThreeConstantH1 F Q h3Q (sourceTrivialCoefficientHeckeOperators F Q ell x) =
      sourceAffineFunctionHeckeOperators F 3 Q h3Q ell (sourceThreeConstantH1 F Q h3Q x) :=
  sourcePrimeHeckeH1_naturality ell.property.1 _ _ (sourceThreeConstantMap F Q h3Q)
    LinearMap.id (sourceAffineFunctionDiagonal 3 F ell.val)
    (sourceTrivialCoefficient_intertwine F Q ell.property.1)
    (sourceAffineFunctionDiagonal_intertwine F 3 Q h3Q ell)
    (LinearMap.ext fun _ => rfl) x

/-- The exact prime-scaled original coefficient map still intertwines
the actual Hecke subgroup conjugation. -/
theorem sourceThreeFunctionTwisted_intertwine (ell : sourceBinaryHeckePrime Q)
    (u : heckeUpperSubgroup Q ell.val) :
      ((ell.val : F) • sourceAffineFunctionDiagonal 3 F ell.val).comp
          ((sourceAffineFunctionRep 3 Q F h3Q).ρ (sourceHeckeConjugation ell.property.1 u)) =
        ((sourceAffineFunctionRep 3 Q F h3Q).ρ u.val).comp
          ((ell.val : F) • sourceAffineFunctionDiagonal 3 F ell.val) := by
  apply LinearMap.ext
  intro f
  funext w
  exact congrArg (fun v : sourceAffineFunctionRep 3 Q F h3Q => (ell.val : F) * v w)
    (LinearMap.congr_fun (sourceAffineFunctionDiagonal_intertwine F 3 Q h3Q ell u) f)

variable [CharP F 3]

/-- The native difference coefficient morphism intertwines the original
Hecke coefficient maps with their exact prime twist. -/
theorem sourceThreeFunctionDifferenceMap_diagonal (ell : sourceBinaryHeckePrime Q) :
      (sourceThreeFunctionDifferenceMap F Q h3Q).hom.toLinearMap.comp
          (sourceAffineFunctionDiagonal 3 F ell.val) =
        ((ell.val : F) • sourceAffineFunctionDiagonal 3 F ell.val).comp
          (sourceThreeFunctionDifferenceMap F Q h3Q).hom.toLinearMap := by
  rw [LinearMap.smul_comp]
  exact sourceThreeFunctionDifference_diagonal F ell.val
    (sourceBinaryFlag_goodPrime_cast_ne_zero (ZMod 3) 3 Q h3Q Nat.prime_three ell)

/-- On actual full native H1, the original coefficient difference intertwines
Hecke with multiplication by the exact good prime. -/
theorem sourceThreeFunctionDifferenceH1_hecke (ell : sourceBinaryHeckePrime Q)
    (x : H1 (sourceAffineFunctionRep 3 Q F h3Q)) :
    sourceThreeFunctionDifferenceH1 F Q h3Q (sourceAffineFunctionHeckeOperators F 3 Q h3Q ell x) =
      (ell.val : F) • sourceAffineFunctionHeckeOperators F 3 Q h3Q ell
        (sourceThreeFunctionDifferenceH1 F Q h3Q x) :=
  (sourcePrimeHeckeH1_naturality ell.property.1
    (sourceAffineFunctionRep 3 Q F h3Q) (sourceAffineFunctionRep 3 Q F h3Q)
    (sourceThreeFunctionDifferenceMap F Q h3Q)
    (sourceAffineFunctionDiagonal 3 F ell.val)
    ((ell.val : F) • sourceAffineFunctionDiagonal 3 F ell.val)
    (sourceAffineFunctionDiagonal_intertwine F 3 Q h3Q ell)
    (sourceThreeFunctionTwisted_intertwine F Q h3Q ell)
    (sourceThreeFunctionDifferenceMap_diagonal F Q h3Q ell) x).trans
      (sourcePrimeHeckeH1_smul ell.property.1 (sourceAffineFunctionRep 3 Q F h3Q)
        (sourceAffineFunctionDiagonal 3 F ell.val)
        (sourceAffineFunctionDiagonal_intertwine F 3 Q h3Q ell) (ell.val : F)
        (sourceThreeFunctionTwisted_intertwine F Q h3Q ell)
        (sourceThreeFunctionDifferenceH1 F Q h3Q x))

end
end Dubon2026
