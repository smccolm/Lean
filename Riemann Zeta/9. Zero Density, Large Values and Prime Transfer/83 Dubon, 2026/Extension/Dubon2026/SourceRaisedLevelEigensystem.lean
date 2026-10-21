import Dubon2026.SourceRaisedLevelEvaluationHecke
import Dubon2026.SourceBinaryLevelEigensystem
import Dubon2026.SourceAffineFlagEigenSurvival

/-! Original nonzero eigensystems at the raised trivial-coefficient level.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> original trivial-coefficient native H1. The actual evaluation
is injective and Hecke-compatible; these are proved dependencies, not
extra hypotheses. The exact Eisenstein alternative remains visible.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] (hpQ : p ∣ Q)

/-- Every original nonzero full-function H1 eigensystem gives a nonzero
trivial-coefficient eigensystem at level Q*p with the same good-prime eigenvalues. -/
theorem sourceAffineFunction_raiseLevel (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceAffineFunctionRep p Q F hpQ)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceAffineFunctionHeckeOperators F p Q hpQ ell x = values ell • x) :
    ∃ y : H1 (Rep.trivial F (Gamma0 (Q * p)) F), y ≠ 0 ∧
      ∀ ell : sourceBinaryHeckePrime (Q * p),
        sourceTrivialCoefficientHeckeOperators F (Q * p) ell y =
          values (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell) • y := by
  refine ⟨sourceRaisedLevelEvaluationH1 F p Q hpQ x, ?_, ?_⟩
  · intro hzero
    exact hx (sourceRaisedLevelEvaluationH1_injective F p Q hpQ
      (hzero.trans (map_zero (sourceRaisedLevelEvaluationH1 F p Q hpQ)).symm))
  · intro ell
    letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
    rw [← sourceRaisedLevelEvaluationH1_hecke F p Q hpQ ell.property.1 ell.property.2,
      heig, map_smul]
    rfl

/-- An actual character H1 eigensystem, after inverting six, either reaches
nonzero trivial-coefficient H1 at the raised level with the exact twist,
or satisfies the precise source Eisenstein exception.
No evaluation injectivity, Hecke compatibility or eigenclass survival is assumed. -/
theorem sourceAffineCharacter_raiseLevel_or_exception [CharP F p] [NeZero Q]
    (j : Fin p) (h6 : (6 : F) ≠ 0) (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ (2 * j.val) 0)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ (2 * j.val) 0 ell x =
      values ell • x) :
    (∃ y : H1 (Rep.trivial F (Gamma0 (Q * p)) F), y ≠ 0 ∧
      ∀ ell : sourceBinaryHeckePrime (Q * p),
        sourceTrivialCoefficientHeckeOperators F (Q * p) ell y =
          (sourceAffineFlagHeckeScalar F p j ell.val *
            values (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell)) • y) ∨
    (j.val + 1 < p ∧ (p - 1) ∣ 2 * (j.val + 1) ∧
      ∀ ell : sourceBinaryHeckePrime Q,
        sourceAffineFlagHeckeScalar F p j ell.val * values ell =
          ((ell.val : F) + 1) *
            (ZMod.castHom (dvd_refl p) F ((ell.val : ZMod p)⁻¹)) ^ (j.val + 1)) := by
  rcases sourceAffineCharacter_eigen_survival F p Q hpQ j h6 values x hx heig with
    ⟨y, hy, he⟩ | hex
  · exact Or.inl (sourceAffineFunction_raiseLevel F p Q hpQ
      (fun ell => sourceAffineFlagHeckeScalar F p j ell.val * values ell) y hy he)
  · exact Or.inr hex

end
end Dubon2026
