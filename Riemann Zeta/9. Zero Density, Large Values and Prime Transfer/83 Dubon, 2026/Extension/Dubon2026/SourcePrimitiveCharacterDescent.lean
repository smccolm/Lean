import Dubon2026.SourceBinaryCharacterDescent
import Dubon2026.SourceOriginalResidualH1Eigensystem

/-! The original primitive form supplies the actual residual character eigensystem.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> original residual character descent. The already proved integral
character, tensor nonvanishing, coefficient injection and Hecke commutativity
produce the input eigenclass. The level-divisibility condition is explicit;
the separate level-raising step will remove it at primes outside the level.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- For the original primitive form at every source weight, when the residue
prime divides its level, a genuine nonzero native H1 character class realizes
all original good-prime Fourier reductions with the derived ell^j twist.
The local coefficient embedding is the existing one; no binary eigenclass,
surviving quotient, Hecke compatibility or exponent congruence is assumed. -/
theorem sourcePrimitive_exists_residualCharacterEigensystem
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type} [Field K] [IsAlgClosed K] [Algebra 𝓀[E] K]
    (p : ℕ) (hp : p.Prime) [CharP K p] (hpQ : p ∣ Q)
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    ∃ j : ℕ, j ≤ (k - 2).toNat ∧
      (sourceBinaryFlagExponentOf p (k - 2).toNat j + 2 * j ≡ (k - 2).toNat [MOD (p - 1)]) ∧
      ∃ (values : sourceBinaryHeckePrime Q → K)
        (y : groupCohomology.H1 (sourceBinaryFlagQuotientRep K p Q hpQ (k - 2).toNat j)),
        y ≠ 0 ∧
        (∀ ell : sourceBinaryHeckePrime Q,
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
            ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
              ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) =
            (ell.val : K) ^ j * values ell) ∧
        ∀ ell, sourceBinaryFlagUntwistedOperators K p Q hpQ (k - 2).toNat j ell y =
          values ell • y := by
  obtain ⟨x, hx, heig⟩ := sourcePrimitive_exists_residualH1Eigensystem (K := K) p hp f hk τ
  obtain ⟨j, hj, hmod, _, values, y, hy, hvalues, he⟩ :=
    sourceBinaryH1_exists_untwistedCharacterPiece K p Q hpQ (k - 2).toNat hp _ x hx heig
  exact ⟨j, hj, hmod, values, y, hy, hvalues, he⟩

end
end Dubon2026
