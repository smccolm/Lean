import Dubon2026.SourceCharacterExponentReduction

/-! Exact native Hecke eigenclass transport through proved character equalities.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the required original normalized character and trivial boundary cases.
The only representation identifications used below are the actual prime-field
equalities proved in SourceCharacterExponentReduction.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] (hpQ : p ∣ Q)

private local instance characterReductionPrimeNeZero (ell : sourceBinaryHeckePrime Q) :
    NeZero ell.val := ⟨ell.property.1.ne_zero⟩

private theorem identity_eigen_of_rep_eq (A B : Rep F (Gamma0 Q)) (hAB : A = B)
    (hA : ∀ ell : sourceBinaryHeckePrime Q, ∀ u : heckeUpperSubgroup Q ell.val,
      (LinearMap.id : Module.End F A).comp (A.ρ (sourceHeckeConjugation ell.property.1 u)) =
        (A.ρ u.val).comp LinearMap.id)
    (hB : ∀ ell : sourceBinaryHeckePrime Q, ∀ u : heckeUpperSubgroup Q ell.val,
      (LinearMap.id : Module.End F B).comp (B.ρ (sourceHeckeConjugation ell.property.1 u)) =
        (B.ρ u.val).comp LinearMap.id)
    (values : sourceBinaryHeckePrime Q → F) (x : H1 A) (hx : x ≠ 0)
    (heig : ∀ ell : sourceBinaryHeckePrime Q,
      sourcePrimeHeckeH1 ell.property.1 A LinearMap.id (hA ell) x = values ell • x) :
    ∃ y : H1 B, y ≠ 0 ∧ ∀ ell : sourceBinaryHeckePrime Q,
      sourcePrimeHeckeH1 ell.property.1 B LinearMap.id (hB ell) y = values ell • y := by
  subst B
  exact ⟨x, hx, heig⟩

/-- The original binary-flag character eigenclass gives its actual lower-diagonal eigenclass
with exactly the same identity-coefficient Hecke eigenvalues. -/
theorem sourceCharacterEigen_to_lower (n j : ℕ) (hj : j ≤ n)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ n j ell x = values ell • x) :
    ∃ y : H1 (sourceBinaryFlagQuotientRep F p Q hpQ (sourceBinaryFlagExponentOf p n j) 0),
      y ≠ 0 ∧ ∀ ell,
        sourceBinaryFlagUntwistedOperators F p Q hpQ (sourceBinaryFlagExponentOf p n j) 0 ell y =
          values ell • y :=
  identity_eigen_of_rep_eq F Q _ _ (sourceCharacterRep_eq_lower F p Q hpQ n j hj)
    (fun ell => sourceBinaryFlagIdentity_intertwine F p Q hpQ n j ell.property.1)
    (fun ell => sourceBinaryFlagIdentity_intertwine F p Q hpQ
      (sourceBinaryFlagExponentOf p n j) 0 ell.property.1) values x hx heig

/-- Congruent original lower-diagonal exponents preserve the complete native Hecke eigensystem. -/
theorem sourceCharacterEigen_of_modEq {e e' : ℕ} (he : e ≡ e' [MOD (p - 1)])
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ e 0)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ e 0 ell x = values ell • x) :
    ∃ y : H1 (sourceBinaryFlagQuotientRep F p Q hpQ e' 0),
      y ≠ 0 ∧ ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ e' 0 ell y = values ell • y :=
  identity_eigen_of_rep_eq F Q _ _ (sourceCharacterRep_eq_of_modEq F p Q hpQ he)
    (fun ell => sourceBinaryFlagIdentity_intertwine F p Q hpQ e 0 ell.property.1)
    (fun ell => sourceBinaryFlagIdentity_intertwine F p Q hpQ e' 0 ell.property.1) values x hx heig

/-- An actual trivial lower-diagonal character gives the original trivial-coefficient Hecke eigensystem. -/
theorem sourceCharacterEigen_to_trivial (e : ℕ) (he : (p - 1) ∣ e)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ e 0)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ e 0 ell x = values ell • x) :
    ∃ y : H1 (Rep.trivial F (Gamma0 Q) F), y ≠ 0 ∧
      ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell y = values ell • y :=
  identity_eigen_of_rep_eq F Q _ _ (sourceCharacterRep_eq_trivial F p Q hpQ e he)
    (fun ell => sourceBinaryFlagIdentity_intertwine F p Q hpQ e 0 ell.property.1)
    (fun ell => sourceTrivialCoefficient_intertwine F Q ell.property.1) values x hx heig

/-- An actual trivial-coefficient eigenclass is also the exact lower-diagonal character
whenever its exponent is divisible by the actual prime-field unit order. -/
theorem sourceTrivialEigen_to_character (e : ℕ) (he : (p - 1) ∣ e)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (Rep.trivial F (Gamma0 Q) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell x = values ell • x) :
    ∃ y : H1 (sourceBinaryFlagQuotientRep F p Q hpQ e 0), y ≠ 0 ∧
      ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ e 0 ell y = values ell • y :=
  identity_eigen_of_rep_eq F Q _ _ (sourceCharacterRep_eq_trivial F p Q hpQ e he).symm
    (fun ell => sourceTrivialCoefficient_intertwine F Q ell.property.1)
    (fun ell => sourceBinaryFlagIdentity_intertwine F p Q hpQ e 0 ell.property.1) values x hx heig

end
end Dubon2026
