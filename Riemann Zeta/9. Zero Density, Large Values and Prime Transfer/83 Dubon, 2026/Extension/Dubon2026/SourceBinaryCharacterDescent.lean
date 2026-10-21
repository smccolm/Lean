import Dubon2026.SourceBinaryFlagOriginal
import Dubon2026.SourceBinaryFlagExponent
import Dubon2026.SourceBinaryFlagUntwisted

/-! Exact character and eigenvalue descent from the original residual binary H1.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> actual character eigensystem with the original ell^j Hecke twist.
This consumer derives the surviving character and nonzero native H1 class;
the residue characteristic dividing the source level remains explicit.
-/

namespace Dubon2026
noncomputable section

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n : ℕ)

/-- A nonzero original binary H1 eigensystem descends to a genuine
one-dimensional coefficient character and its identity-coefficient Hecke
eigensystem. The precise exponent congruence, all good-prime scalar twists
and the character formula are derived, including characteristics two and three. -/
theorem sourceBinaryH1_exists_untwistedCharacterPiece [NeZero Q] (hp : p.Prime)
    (eigenvalues : sourceBinaryHeckePrime Q → F)
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep F Q n)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryH1PrimeOperators F Q n ell x = eigenvalues ell • x) :
    ∃ j : ℕ, j ≤ n ∧
      (sourceBinaryFlagExponentOf p n j + 2 * j ≡ n [MOD (p - 1)]) ∧
      (∀ g : CongruenceSubgroup.Gamma0 Q, sourceBinaryFlagCharacter F p Q hpQ n j g =
        ((g.val 1 1 : ℤ) : F) ^ sourceBinaryFlagExponentOf p n j) ∧
      ∃ (values : sourceBinaryHeckePrime Q → F)
        (y : groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j)),
        y ≠ 0 ∧
        (∀ ell, eigenvalues ell = (ell.val : F) ^ j * values ell) ∧
        ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ n j ell y = values ell • y := by
  obtain ⟨j, hj, y, hy, hye⟩ :=
    sourceBinaryH1_exists_characterPiece F p Q hpQ n eigenvalues x hx heig
  refine ⟨j, hj, sourceBinaryFlagExponentOf_modEq hp n j,
    sourceBinaryFlagCharacter_eq_lower_pow F p Q hpQ n j hp hj,
    (fun ell => ((ell.val : F) ^ j)⁻¹ * eigenvalues ell), y, hy, ?_, ?_⟩
  · intro ell
    have ha : (ell.val : F) ^ j ≠ 0 :=
      pow_ne_zero _ (sourceBinaryFlag_goodPrime_cast_ne_zero F p Q hpQ hp ell)
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · intro ell
    letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
    have ha : (ell.val : F) ^ j ≠ 0 :=
      pow_ne_zero _ (sourceBinaryFlag_goodPrime_cast_ne_zero F p Q hpQ hp ell)
    have h := hye ell
    change sourceBinaryFlagQuotientHeckeH1 F p Q hpQ n j ell.property.1 y =
      eigenvalues ell • y at h
    rw [sourceBinaryFlagQuotientHeckeH1_eq_smul] at h
    have he := congrArg (fun z => ((ell.val : F) ^ j)⁻¹ • z) h
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using he

end
end Dubon2026
