import Dubon2026.SourcePrimitiveLocalH1Character
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! DUB-17/18 -> original all-weight adic association -> compatible
prime-power Hecke realizations. Reduce the same original local H1 character
modulo every positive maximal-ideal power. Native quotient transition maps
prove compatibility and retain the original Fourier values. These are
characters of the original integral Hecke algebra, not Galois representations.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- The same original local H1 character at every positive adic precision. -/
def sourcePrimitiveH1AdicQuotientCharacter
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) (n : ℕ) :
    sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →+*
      𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1) :=
  (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))).comp
    (sourcePrimitiveLocalH1HeckeCharacter f hk τ)

/-- At every adic precision each original good-prime value is the reduction of its exact Fourier coefficient. -/
theorem sourcePrimitiveH1AdicQuotientCharacter_hecke
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) (n : ℕ)
    (ell : sourceBinaryHeckePrime Q) :
    sourcePrimitiveH1AdicQuotientCharacter f hk τ n
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell,
        Algebra.subset_adjoin ⟨ell, rfl⟩⟩ =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
        ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
          sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩ := by
  change Ideal.Quotient.mk _ (sourcePrimitiveLocalH1HeckeCharacter f hk τ _) = _
  rw [sourcePrimitiveLocalH1HeckeCharacter_hecke]

/-- Native adic transition maps preserve the entire original H1 character. -/
theorem sourcePrimitiveH1AdicQuotientCharacter_compatible
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal 𝒪[E])
      (Nat.add_le_add_right h 1)).comp (sourcePrimitiveH1AdicQuotientCharacter f hk τ n) =
        sourcePrimitiveH1AdicQuotientCharacter f hk τ m := by
  ext T
  simp only [sourcePrimitiveH1AdicQuotientCharacter, RingHom.comp_apply,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

omit [CharZero E] in
/-- A Noetherian valuation ring with finite residue field has finite coefficient rings at every adic precision. -/
theorem sourceLocalH1AdicQuotient_finite
    [IsNoetherianRing 𝒪[E]] [Finite 𝓀[E]] (n : ℕ) :
    Finite (𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1)) := by
  letI : Finite (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]) :=
    inferInstanceAs (Finite 𝓀[E])
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal 𝒪[E])) (n + 1)

end
end Dubon2026
